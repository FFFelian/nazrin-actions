#!/usr/bin/env python3
"""Run one shard of the schema-4 structured atomization-trace export.

Every theorem is atomized in its **own short-lived Lean process** and writes one
schema-4 JSONL file (one ``record: "step"`` per atomization step plus one final
``record: "theorem"`` summary).  A crash, a wall-clock timeout or heartbeat
exhaustion in one theorem therefore cannot corrupt or truncate another theorem's
trace, and the shard can be stopped and resumed at theorem granularity.

The exporter is `Standalone/StructuredTraceV4.lean` from the paper overlay:

    lean --run Standalone/StructuredTraceV4.lean MODULE THEOREM OUTPUT_PATH

``--exporter-mode lean-run`` runs exactly that command through ``lake env``.
``binary`` runs the executable that ``lake build StructuredTraceV4`` produced,
which skips the per-theorem re-elaboration of the 54 KB exporter source; both
write identical records.  ``auto`` (default) prefers the built executable when
it exists and falls back to ``lean-run``.

Outputs (under ``--output-dir``):

    work/<index>-<theorem>.jsonl   per-theorem raw output (resume checkpoint)
    steps.jsonl / steps.jsonl.gz   validated step records, shard order
    theorems.jsonl / *.gz          one summary record per theorem, shard order
    stats.json / stats.md          shard statistics
    provenance.json                run configuration + input/output digests
    state.json                     progress snapshot
    shard.tsv                      exact input rows of this shard
    meta.json                      compact contract for the merge job
    work.tgz                       ``--archive-work``: compressed checkpoints

Envelope handling (the exporter is the only producer of the payload, this
runner never edits a step record):

* ``schema_version`` must be 4 and ``schema`` must be 3 or 4 (the envelope
  schema is an exporter option; schema 3 + ``schema_version`` 4 is what the
  Gate 1.4a local runs produced);
* a ``record: "step"`` line whose ``theorem`` does not match the slice row, or
  whose envelope is not schema 4, is dropped and counted as a violation;
* a missing summary (timeout, crash, OOM) is replaced by a synthetic failure
  summary carrying ``partial: true``; the process is never allowed to invent a
  successful theorem.

Step records are streamed from the per-theorem work files into ``steps.jsonl``
in shard order, so a 500 MB shard does not have to be held in memory.

Usage:

    python3 scripts/run_schema4_shard.py \
      --slice plan/shard-00.tsv \
      --output-dir outputs/shard-0 \
      --repo "$NAZRIN_DIR" \
      --jobs 2 --timeout-seconds 180 --max-heartbeats 200000
"""

from __future__ import annotations

import argparse
import concurrent.futures
import gzip
import hashlib
import json
import os
import shlex
import signal
import statistics
import subprocess
import sys
import tarfile
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence

SCHEMA_VERSION = 4
ENVELOPE_SCHEMAS = (3, 4)
DEFAULT_EXPORTER_SOURCE = "Standalone/StructuredTraceV4.lean"
EXPORTER_BASENAME = "StructuredTraceV4"


class ConfigError(Exception):
    """A dispatch or environment problem that must stop the shard."""


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sanitize(name: str) -> str:
    return "".join(c if c.isalnum() or c in "._-" else "_" for c in name)[:120]


def write_json(path: Path, value: Any) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, path)


def gzip_file(source: Path, destination: Path, level: int = 1) -> dict[str, Any]:
    """Deterministic gzip copy (mtime=0) plus its digests and sizes."""

    digest = hashlib.sha256()
    size = 0
    tmp = destination.with_suffix(destination.suffix + ".tmp")
    with source.open("rb") as reader, tmp.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw,
                           compresslevel=level, mtime=0) as writer:
            for chunk in iter(lambda: reader.read(1 << 20), b""):
                writer.write(chunk)
                digest.update(chunk)
                size += len(chunk)
    os.replace(tmp, destination)
    return {
        "name": destination.name,
        "sha256": sha256_file(destination),
        "compressed_bytes": destination.stat().st_size,
        "uncompressed_sha256": digest.hexdigest(),
        "uncompressed_bytes": size,
    }


# ---------------------------------------------------------------------------
# Slice input
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class SliceRow:
    index: int
    theorem: str
    module: str
    fields: tuple[str, ...]
    header: tuple[str, ...]

    def field(self, name: str, default: str = "") -> str:
        try:
            position = self.header.index(name)
        except ValueError:
            return default
        return self.fields[position] if position < len(self.fields) else default


def read_slice(path: Path) -> tuple[list[SliceRow], bytes]:
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise ConfigError(f"{path}: input is not valid UTF-8") from exc
    lines = text.splitlines()
    if not lines:
        raise ConfigError(f"{path}: empty shard TSV")
    header = tuple(cell.strip() for cell in lines[0].split("\t"))
    if "theorem" not in header:
        raise ConfigError(f"{path}: header has no 'theorem' column")
    if "module" not in header:
        raise ConfigError(f"{path}: header has no 'module' column")
    theorem_col = header.index("theorem")
    module_col = header.index("module")
    index_col = header.index("index") if "index" in header else None

    rows: list[SliceRow] = []
    seen: set[str] = set()
    for line_number, line in enumerate(lines[1:], start=2):
        if not line.strip():
            continue
        cells = tuple(cell.strip() for cell in line.split("\t"))
        if len(cells) != len(header):
            raise ConfigError(
                f"{path}:{line_number}: expected {len(header)} columns, got {len(cells)}"
            )
        theorem = cells[theorem_col]
        module = cells[module_col]
        if not theorem:
            raise ConfigError(f"{path}:{line_number}: empty theorem name")
        if not module:
            raise ConfigError(f"{path}:{line_number}: empty module for {theorem}")
        if theorem in seen:
            raise ConfigError(f"{path}:{line_number}: duplicate theorem {theorem}")
        seen.add(theorem)
        try:
            index = int(cells[index_col]) if index_col is not None else len(rows)
        except ValueError:
            index = len(rows)
        rows.append(SliceRow(index=index, theorem=theorem, module=module,
                             fields=cells, header=header))
    if not rows:
        raise ConfigError(f"{path}: no theorem rows")
    return rows, raw


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------


@dataclass
class Config:
    repo: Path
    slice_path: Path
    output_dir: Path
    rows_total: int
    rows_selected: int
    jobs: int = 2
    timeout_seconds: float = 180.0
    max_heartbeats: int = 200_000
    max_steps: int = 3000
    envelope_schema: int = 3
    run_id: str = ""
    shard_id: int | None = None
    plan_sha256: str = ""
    limit: int = 0
    window_start: int = 0
    window_end: int = -1
    exporter_mode: str = "auto"
    exporter_cmd: str = ""
    resume: bool = True
    retry_failures: bool = False
    force: bool = False
    archive_work: bool = False
    gzip_only: bool = False
    quiet: bool = False


# ---------------------------------------------------------------------------
# Exporter invocation
# ---------------------------------------------------------------------------


def resolve_exporter(cfg: Config) -> tuple[list[str], str]:
    if cfg.exporter_cmd:
        argv = shlex.split(cfg.exporter_cmd)
        if not argv:
            raise ConfigError("--exporter-cmd is empty")
        return argv, "explicit"

    binary = cfg.repo / ".lake" / "build" / "bin" / EXPORTER_BASENAME
    mode = cfg.exporter_mode
    if mode == "binary":
        if not binary.is_file() or not os.access(binary, os.X_OK):
            raise ConfigError(
                f"exporter mode 'binary' requested but {binary} is missing or not "
                "executable; run 'lake build StructuredTraceV4' first"
            )
        return [str(binary)], "binary"
    if mode == "auto" and binary.is_file() and os.access(binary, os.X_OK):
        return [str(binary)], "binary"
    source = cfg.repo / DEFAULT_EXPORTER_SOURCE
    if not source.is_file():
        raise ConfigError(
            f"exporter source not found: {source} (apply the paper overlay first, "
            "or pass --exporter-cmd)"
        )
    return ["lake", "env", "lean", "--run", DEFAULT_EXPORTER_SOURCE], "lean-run"


def exporter_env(cfg: Config) -> dict[str, str]:
    env = os.environ.copy()
    candidates: list[Path] = []
    if os.environ.get("ELAN_HOME"):
        candidates.append(Path(os.environ["ELAN_HOME"]) / "bin")
    candidates.append(Path.home() / ".elan" / "bin")
    for candidate in candidates:
        if candidate.is_dir():
            env["PATH"] = f"{candidate}{os.pathsep}{env.get('PATH', '')}"
    env["NAZRIN_STRUCT_MAX_HEARTBEATS"] = str(cfg.max_heartbeats)
    env["NAZRIN_STRUCT_MAX_STEPS"] = str(cfg.max_steps)
    env["NAZRIN_STRUCT_RUN_ID"] = cfg.run_id
    env["NAZRIN_STRUCT_STEP_SCHEMA"] = str(cfg.envelope_schema)
    env.setdefault("PYTHONDONTWRITEBYTECODE", "1")
    return env


# ---------------------------------------------------------------------------
# Record handling
# ---------------------------------------------------------------------------


def work_path(cfg: Config, row: SliceRow) -> Path:
    return cfg.output_dir / "work" / f"{row.index:06d}-{sanitize(row.theorem)}.jsonl"


def scan_work_file(path: Path, theorem: str) -> dict[str, Any]:
    """Check one theorem's JSONL envelope and extract its summary record.

    Returns the step count (not the lines: a shard can be hundreds of MB), the
    summary, capped parse errors and capped envelope violations.
    """

    result: dict[str, Any] = {
        "step_count": 0,
        "summary": None,
        "parse_errors": [],
        "violations": [],
        "envelope_schemas": set(),
    }
    if not path.is_file():
        result["parse_errors"].append("missing work file")
        return result
    with path.open("rb") as handle:
        for line_number, raw_line in enumerate(handle, 1):
            line = raw_line.decode("utf-8", errors="strict").strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                if len(result["parse_errors"]) < 20:
                    result["parse_errors"].append(f"line {line_number}: invalid JSON: {exc}")
                continue
            if not isinstance(record, dict):
                if len(result["parse_errors"]) < 20:
                    result["parse_errors"].append(
                        f"line {line_number}: record is not a JSON object")
                continue
            kind = record.get("record")
            schema = record.get("schema")
            if isinstance(schema, int) and not isinstance(schema, bool):
                result["envelope_schemas"].add(schema)
            if kind == "theorem":
                result["summary"] = record
                continue
            if kind != "step":
                if len(result["violations"]) < 50:
                    result["violations"].append(
                        {"line": line_number, "reason": f"unknown record kind {kind!r}"})
                continue
            if record.get("schema_version") != SCHEMA_VERSION:
                if len(result["violations"]) < 50:
                    result["violations"].append({
                        "line": line_number,
                        "reason": f"schema_version {record.get('schema_version')!r} is not {SCHEMA_VERSION}",
                    })
                continue
            if schema not in ENVELOPE_SCHEMAS:
                if len(result["violations"]) < 50:
                    result["violations"].append(
                        {"line": line_number, "reason": f"envelope schema {schema!r}"})
                continue
            if record.get("theorem") != theorem:
                if len(result["violations"]) < 50:
                    result["violations"].append({
                        "line": line_number,
                        "reason": f"theorem {record.get('theorem')!r} does not match row",
                    })
                continue
            result["step_count"] += 1
    return result


def iter_step_lines(path: Path, theorem: str) -> Iterator[str]:
    """Yield the validated step lines of one work file, verbatim."""

    if not path.is_file():
        return
    with path.open("rb") as handle:
        for raw_line in handle:
            line = raw_line.decode("utf-8", errors="strict").strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not isinstance(record, dict) or record.get("record") != "step":
                continue
            if record.get("schema_version") != SCHEMA_VERSION:
                continue
            if record.get("schema") not in ENVELOPE_SCHEMAS:
                continue
            if record.get("theorem") != theorem:
                continue
            yield line


def classify_stderr(stderr: str, returncode: int | None) -> str:
    text = stderr.lower()
    if returncode in (-9, 137):
        return "killed"
    if "stack overflow" in text:
        return "stack_overflow"
    if "deep recursion" in text:
        return "deep_recursion"
    if "maximum number of heartbeats" in text or "heartbeats" in text:
        if "preprocessexpr" in text:
            return "heartbeat.preprocessExpr"
        if "whnf" in text:
            return "heartbeat.whnf"
        return "heartbeat.other"
    if "unknown module" in text or "unknown constant" in text:
        return "lookup"
    if "could not resolve" in text and "import" in text:
        return "import"
    return "crash"


def run_theorem(cfg: Config, row: SliceRow, exporter: list[str],
                exporter_mode: str) -> dict[str, Any]:
    out_path = work_path(cfg, row)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    argv = [*exporter, row.module, row.theorem, str(out_path)]
    started = time.monotonic()
    stage_override: str | None = None
    stderr_tail = ""
    stdout_tail = ""
    returncode: int | None = None
    timed_out = False
    launch_error = ""
    process: subprocess.Popen[str] | None = None
    try:
        process = subprocess.Popen(
            argv,
            cwd=str(cfg.repo),
            env=exporter_env(cfg),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        try:
            stdout, stderr = process.communicate(timeout=cfg.timeout_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            stage_override = "wall_timeout"
            try:
                os.killpg(os.getpgid(process.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                stdout, stderr = process.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                stdout, stderr = "", ""
            stderr_tail = ((stderr or "") if isinstance(stderr, str) else "")[-4000:]
            stdout_tail = ((stdout or "") if isinstance(stdout, str) else "")[-1000:]
            out_path.write_text("", encoding="utf-8")  # never keep a half-written file
            raise
        returncode = process.returncode
        stderr_tail = (stderr or "")[-4000:]
        stdout_tail = (stdout or "")[-1000:]
    except subprocess.TimeoutExpired:
        # The timeout branch above already killed the whole process group.
        timed_out = True
        stage_override = "wall_timeout"
        out_path.write_text("", encoding="utf-8")
    except OSError as exc:
        launch_error = f"{type(exc).__name__}: {exc}"
        stage_override = "launch_error"
        try:
            out_path.write_text("", encoding="utf-8")
        except OSError:
            pass
    wall_ms = int((time.monotonic() - started) * 1000)

    scanned = scan_work_file(out_path, row.theorem)
    summary: dict[str, Any] | None = scanned["summary"]
    parse_errors: list[str] = scanned["parse_errors"]
    violations: list[dict[str, Any]] = scanned["violations"]

    if summary is not None:
        if summary.get("schema_version") != SCHEMA_VERSION:
            parse_errors.append(
                f"summary schema_version {summary.get('schema_version')!r} is not "
                f"{SCHEMA_VERSION}")
            summary = None
        elif summary.get("theorem") != row.theorem or summary.get("module") != row.module:
            parse_errors.append("summary theorem/module does not match the slice row")
            summary = None

    synthesized = summary is None
    if synthesized:
        stage = stage_override or classify_stderr(stderr_tail, returncode) or "no_summary"
        message = (stderr_tail or stdout_tail or launch_error or "").strip()[-1500:]
        summary = {
            "schema": cfg.envelope_schema,
            "schema_version": SCHEMA_VERSION,
            "record": "theorem",
            "run_id": cfg.run_id,
            "theorem": row.theorem,
            "module": row.module,
            "status": "failure",
            "stage": stage,
            "message": message or "exporter produced no summary record",
            "steps": scanned["step_count"],
            "label_rejections": 0,
            "unmodeled_steps": 0,
            "max_heartbeats": cfg.max_heartbeats,
            "max_steps": cfg.max_steps,
            "elapsed_ms": wall_ms,
            "partial": True,
        }
    else:
        if stage_override is not None:
            summary["stage"] = stage_override
            summary["status"] = "failure"
            summary["partial"] = True
        if summary.get("status") == "success" and returncode not in (0, None):
            summary["status"] = "failure"
            summary["stage"] = "returncode"
            summary["partial"] = True
        summary.setdefault("elapsed_ms", wall_ms)
        summary.setdefault("status", "failure")
        summary.setdefault("stage", "unknown")
        summary.setdefault("steps", scanned["step_count"])
        summary["partial"] = bool(summary.get("partial")) or summary["status"] != "success"

    summary["synthetic_summary"] = synthesized
    summary["row_index"] = row.index
    summary["theorem"] = row.theorem
    summary["module"] = row.module
    summary["timeout_seconds"] = cfg.timeout_seconds
    summary["exporter_mode"] = exporter_mode
    summary["lean_argv"] = argv
    summary["stderr_tail"] = stderr_tail[-1500:]
    summary["wall_ms"] = wall_ms
    if timed_out:
        summary["timed_out"] = True
    if launch_error:
        summary["launch_error"] = launch_error
    if parse_errors:
        summary["parse_errors"] = parse_errors
    if violations:
        summary["envelope_violations"] = violations
    return {
        "row": row,
        "summary": summary,
        "step_count": scanned["step_count"],
        "envelope_schemas": sorted(scanned["envelope_schemas"]),
        "exporter_mode": exporter_mode,
    }


# ---------------------------------------------------------------------------
# Resume
# ---------------------------------------------------------------------------


def existing_summary(cfg: Config, row: SliceRow) -> dict[str, Any] | None:
    path = work_path(cfg, row)
    if not path.is_file():
        return None
    scanned = scan_work_file(path, row.theorem)
    if scanned["parse_errors"] or scanned["summary"] is None:
        return None
    summary = scanned["summary"]
    if summary.get("schema_version") != SCHEMA_VERSION:
        return None
    if summary.get("theorem") != row.theorem:
        return None
    return summary


def should_skip(cfg: Config, row: SliceRow) -> tuple[bool, dict[str, Any] | None]:
    if cfg.force or not cfg.resume:
        return False, None
    summary = existing_summary(cfg, row)
    if summary is None:
        return False, None
    if cfg.retry_failures and summary.get("status") != "success":
        return False, None
    return True, summary


# ---------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------


def stats_from_results(cfg: Config, results: Sequence[dict[str, Any]],
                       rows: Sequence[SliceRow], skipped: int,
                       written_steps: int) -> dict[str, Any]:
    statuses: dict[str, int] = {}
    stages: dict[str, int] = {}
    envelope: dict[str, int] = {}
    schema4_totals: dict[str, int] = {}
    steps_per_theorem: list[int] = []
    wall: list[int] = []
    synthetic = 0
    for item in results:
        summary = item["summary"]
        status = str(summary.get("status", "unknown"))
        statuses[status] = statuses.get(status, 0) + 1
        stage = str(summary.get("stage", "unknown"))
        stages[stage] = stages.get(stage, 0) + 1
        envelope_key = str(summary.get("schema", "?"))
        envelope[envelope_key] = envelope.get(envelope_key, 0) + 1
        steps_per_theorem.append(int(item["step_count"]))
        if summary.get("synthetic_summary"):
            synthetic += 1
        if isinstance(summary.get("wall_ms"), int):
            wall.append(summary["wall_ms"])
        details = summary.get("schema4")
        if isinstance(details, dict):
            for key, value in details.items():
                if isinstance(value, int) and not isinstance(value, bool):
                    schema4_totals[key] = schema4_totals.get(key, 0) + value

    success = statuses.get("success", 0)
    counted = sum(steps_per_theorem)
    return {
        "schema": 1,
        "record": "stats",
        "run_id": cfg.run_id,
        "shard_id": cfg.shard_id,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "slice": {
            "path": cfg.slice_path.name,
            "sha256": sha256_file(cfg.slice_path),
            "rows_total": cfg.rows_total,
            "rows_selected": cfg.rows_selected,
        },
        "theorems": {
            "requested": len(rows),
            "processed": len(results),
            "succeeded": success,
            "failed": len(results) - success,
            "resumed": skipped,
            "synthetic_summaries": synthetic,
            "timeouts": sum(1 for item in results if item["summary"].get("timed_out")),
            "success_rate": round(success / len(results), 6) if results else 0.0,
        },
        "steps": {
            "total": written_steps,
            "counted": counted,
            "consistent": written_steps == counted,
            "theorems_with_steps": sum(1 for count in steps_per_theorem if count),
            "min": min(steps_per_theorem) if steps_per_theorem else 0,
            "max": max(steps_per_theorem) if steps_per_theorem else 0,
            "mean": round(written_steps / len(results), 6) if results else 0.0,
        },
        "statuses": dict(sorted(statuses.items())),
        "stages": dict(sorted(stages.items())),
        "envelope_schemas": dict(sorted(envelope.items())),
        "schema4": dict(sorted(schema4_totals.items())),
        "wall_ms": {
            "total": sum(wall),
            "mean": round(statistics.mean(wall), 3) if wall else 0.0,
            "median": statistics.median(wall) if wall else 0.0,
            "max": max(wall) if wall else 0,
        },
        "config": {
            "jobs": cfg.jobs,
            "timeout_seconds": cfg.timeout_seconds,
            "max_heartbeats": cfg.max_heartbeats,
            "max_steps": cfg.max_steps,
            "envelope_schema": cfg.envelope_schema,
            "exporter_mode": cfg.exporter_mode,
            "resume": cfg.resume,
            "retry_failures": cfg.retry_failures,
        },
    }


def render_markdown(stats: dict[str, Any]) -> str:
    theorems = stats["theorems"]
    steps = stats["steps"]
    lines = [
        f"# Schema-4 shard {stats.get('shard_id')}",
        "",
        f"- run id: `{stats['run_id']}`",
        f"- slice: `{stats['slice']['path']}` "
        f"({stats['slice']['rows_selected']}/{stats['slice']['rows_total']} rows)",
        f"- theorems: {theorems['succeeded']}/{theorems['processed']} succeeded "
        f"({theorems['success_rate'] * 100:.1f}%), {theorems['failed']} failed, "
        f"{theorems['resumed']} resumed, {theorems['synthetic_summaries']} synthetic",
        f"- steps: {steps['total']} total, {steps['mean']} mean, "
        f"{steps['min']}..{steps['max']} per theorem",
        "",
        "## Stages",
        "",
        "| stage | theorems |",
        "|---|---|",
    ]
    for stage, count in stats["stages"].items():
        lines.append(f"| `{stage}` | {count} |")
    lines += ["", "## Statuses", "", "| status | theorems |", "|---|---|"]
    for status, count in stats["statuses"].items():
        lines.append(f"| `{status}` | {count} |")
    if stats["schema4"]:
        lines += ["", "## schema-4 counters (exporter summaries)", "",
                  "| counter | total |", "|---|---|"]
        for key, value in stats["schema4"].items():
            lines.append(f"| `{key}` | {value} |")
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Work archive
# ---------------------------------------------------------------------------


def archive_work(cfg: Config) -> dict[str, Any]:
    work = cfg.output_dir / "work"
    if not work.is_dir():
        return {}
    destination = cfg.output_dir / "work.tgz"
    tmp = destination.with_suffix(destination.suffix + ".tmp")
    files = sorted(path for path in work.rglob("*") if path.is_file())
    with tmp.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw,
                           compresslevel=1, mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode="w") as tar:
                for path in files:
                    info = tar.gettarinfo(str(path),
                                          arcname=str(path.relative_to(cfg.output_dir)))
                    info.mtime = 0
                    info.uid = info.gid = 0
                    info.uname = info.gname = ""
                    with path.open("rb") as handle:
                        tar.addfile(info, handle)
    os.replace(tmp, destination)
    digest = sha256_file(destination)
    return {
        "name": destination.name,
        "sha256": digest,
        "compressed_bytes": destination.stat().st_size,
        "files": len(files),
        "uncompressed_bytes": sum(path.stat().st_size for path in files),
    }


def remove_work(cfg: Config) -> None:
    work = cfg.output_dir / "work"
    if not work.is_dir():
        return
    for path in sorted(work.rglob("*"), reverse=True):
        if path.is_file() or path.is_symlink():
            path.unlink()
        elif path.is_dir():
            path.rmdir()
    work.rmdir()


# ---------------------------------------------------------------------------
# Main run
# ---------------------------------------------------------------------------


def write_theorems(path: Path, results: Sequence[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for item in results:
            handle.write(json.dumps(item["summary"], sort_keys=True,
                                    separators=(",", ":")) + "\n")


def write_steps(cfg: Config, rows: Sequence[SliceRow],
                results: dict[int, dict[str, Any]]) -> int:
    written = 0
    with (cfg.output_dir / "steps.jsonl").open("w", encoding="utf-8", newline="\n") as handle:
        for row in rows:
            if row.index not in results:
                continue
            for line in iter_step_lines(work_path(cfg, row), row.theorem):
                handle.write(line + "\n")
                written += 1
    return written


def finalize(cfg: Config, rows: Sequence[SliceRow], results: Sequence[dict[str, Any]],
             skipped: int, elapsed_seconds: float, *, archive: bool) -> dict[str, Any]:
    steps_path = cfg.output_dir / "steps.jsonl"
    theorems_path = cfg.output_dir / "theorems.jsonl"
    by_index = {item["row"].index: item for item in results}
    written = write_steps(cfg, rows, by_index)
    write_theorems(theorems_path, results)
    theorems_gz = gzip_file(theorems_path, cfg.output_dir / "theorems.jsonl.gz")
    steps_gz = gzip_file(steps_path, cfg.output_dir / "steps.jsonl.gz")
    if cfg.gzip_only:
        steps_path.unlink()
        theorems_path.unlink()

    stats = stats_from_results(cfg, results, rows, skipped, written)
    write_json(cfg.output_dir / "stats.json", stats)
    (cfg.output_dir / "stats.md").write_text(render_markdown(stats), encoding="utf-8")

    shard_tsv = cfg.output_dir / "shard.tsv"
    shard_tsv.write_bytes(cfg.slice_path.read_bytes())

    work = archive_work(cfg) if archive else {}
    if archive:
        remove_work(cfg)

    toolchain = next(
        (item["summary"].get("toolchain") for item in results
         if isinstance(item["summary"], dict) and item["summary"].get("toolchain")),
        None,
    )
    exporter_modes = sorted({item.get("exporter_mode") for item in results
                             if item.get("exporter_mode")})
    meta = {
        "schema": 1,
        "kind": "schema4-shard-meta",
        "run_id": cfg.run_id,
        "shard_id": cfg.shard_id,
        "schema_version": SCHEMA_VERSION,
        "envelope_schema": cfg.envelope_schema,
        "slice": {
            "name": cfg.slice_path.name,
            "sha256": sha256_file(cfg.slice_path),
            "rows_total": cfg.rows_total,
            "rows_selected": cfg.rows_selected,
        },
        "limit": cfg.limit,
        "window": {"start": cfg.window_start, "end": cfg.window_end},
        "rows": len(rows),
        "theorems": {
            "processed": stats["theorems"]["processed"],
            "succeeded": stats["theorems"]["succeeded"],
            "failed": stats["theorems"]["failed"],
            "resumed": stats["theorems"]["resumed"],
        },
        "steps": stats["steps"]["total"],
        "statuses": stats["statuses"],
        "stages": stats["stages"],
        "exporter": {
            "source": DEFAULT_EXPORTER_SOURCE,
            "modes": exporter_modes,
            "mode_requested": cfg.exporter_mode,
        },
        "toolchain": toolchain,
        "plan_sha256": cfg.plan_sha256,
        "elapsed_seconds": round(elapsed_seconds, 3),
        "artifacts": {
            "steps": {
                "name": steps_path.name,
                "sha256": steps_gz["uncompressed_sha256"],
                "bytes": steps_gz["uncompressed_bytes"],
                "gzip": steps_gz,
                "gzip_only": cfg.gzip_only,
            },
            "theorems": {
                "name": theorems_path.name,
                "sha256": theorems_gz["uncompressed_sha256"],
                "bytes": theorems_gz["uncompressed_bytes"],
                "gzip": theorems_gz,
                "gzip_only": cfg.gzip_only,
            },
            "work": work,
        },
    }
    write_json(cfg.output_dir / "meta.json", meta)

    provenance = {
        "schema": 1,
        "kind": "schema4-shard-provenance",
        "run_id": cfg.run_id,
        "shard_id": cfg.shard_id,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "exporter": DEFAULT_EXPORTER_SOURCE,
        "runner": "scripts/run_schema4_shard.py",
        "paper": ("Nazrin: An Atomic Neural Proof Automation Tactic in Lean 4; "
                  "§IV transposing atomization (pp.4-6), §V ExprGraph (pp.6-8), "
                  "§VI 3,000-step cap (p.8)"),
        "slice": str(cfg.slice_path),
        "slice_sha256": sha256_file(cfg.slice_path),
        "plan_sha256": cfg.plan_sha256,
        "window": {"start": cfg.window_start, "end": cfg.window_end, "limit": cfg.limit},
        "jobs": cfg.jobs,
        "timeout_seconds": cfg.timeout_seconds,
        "max_heartbeats": cfg.max_heartbeats,
        "max_steps": cfg.max_steps,
        "envelope_schema": cfg.envelope_schema,
        "exporter_mode": cfg.exporter_mode,
        "theorems": len(rows),
        "steps": stats["steps"]["total"],
        "toolchain": toolchain,
        "elapsed_seconds": round(elapsed_seconds, 3),
        "artifacts": meta["artifacts"],
    }
    write_json(cfg.output_dir / "provenance.json", provenance)
    write_json(cfg.output_dir / "state.json", {
        "completed": stats["theorems"]["processed"],
        "requested": len(rows),
        "succeeded": stats["theorems"]["succeeded"],
        "failed": stats["theorems"]["failed"],
        "steps": stats["steps"]["total"],
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
    })
    return stats


def select_rows(rows: Sequence[SliceRow], cfg: Config) -> list[SliceRow]:
    end = len(rows) if cfg.window_end < 0 else min(cfg.window_end, len(rows))
    start = max(0, cfg.window_start)
    selected = list(rows[start:end])
    if cfg.limit:
        selected = selected[: cfg.limit]
    return selected


def summarize_only(cfg: Config, rows: Sequence[SliceRow]) -> dict[str, Any]:
    results: list[dict[str, Any]] = []
    for row in rows:
        scanned = scan_work_file(work_path(cfg, row), row.theorem)
        summary = scanned["summary"]
        if summary is None or summary.get("schema_version") != SCHEMA_VERSION:
            summary = {
                "schema": cfg.envelope_schema,
                "schema_version": SCHEMA_VERSION,
                "record": "theorem",
                "run_id": cfg.run_id,
                "theorem": row.theorem,
                "module": row.module,
                "status": "failure",
                "stage": "missing_work",
                "message": "no usable work file",
                "steps": scanned["step_count"],
                "elapsed_ms": 0,
                "partial": True,
                "synthetic_summary": True,
            }
        results.append({"row": row, "summary": summary,
                        "step_count": scanned["step_count"],
                        "exporter_mode": cfg.exporter_mode})
    return finalize(cfg, rows, results, 0, 0.0, archive=False)


def run(cfg: Config, rows: Sequence[SliceRow], exporter: list[str],
        exporter_mode: str, log: Any = None) -> dict[str, Any]:
    cfg.output_dir.mkdir(parents=True, exist_ok=True)
    (cfg.output_dir / "work").mkdir(exist_ok=True)
    started = time.monotonic()

    results: dict[int, dict[str, Any]] = {}
    pending: list[SliceRow] = []
    skipped = 0
    for row in rows:
        skip, summary = should_skip(cfg, row)
        if skip and summary is not None:
            scanned = scan_work_file(work_path(cfg, row), row.theorem)
            summary.setdefault("row_index", row.index)
            summary["exporter_mode"] = exporter_mode
            results[row.index] = {"row": row, "summary": summary,
                                  "step_count": scanned["step_count"],
                                  "exporter_mode": exporter_mode}
            skipped += 1
        else:
            pending.append(row)

    lock = threading.Lock()
    completed = 0

    def task(row: SliceRow) -> dict[str, Any]:
        return run_theorem(cfg, row, exporter, exporter_mode)

    if pending:
        if cfg.jobs <= 1:
            for row in pending:
                results[row.index] = task(row)
                completed += 1
                if log:
                    log(f"[{completed}/{len(pending)}] {row.theorem} -> "
                        f"{results[row.index]['summary'].get('status')}")
        else:
            with concurrent.futures.ThreadPoolExecutor(max_workers=cfg.jobs) as pool:
                futures = {pool.submit(task, row): row for row in pending}
                for future in concurrent.futures.as_completed(futures):
                    row = futures[future]
                    try:
                        results[row.index] = future.result()
                    except Exception as exc:  # never lose a theorem attribution
                        results[row.index] = {
                            "row": row,
                            "summary": {
                                "schema": cfg.envelope_schema,
                                "schema_version": SCHEMA_VERSION,
                                "record": "theorem",
                                "run_id": cfg.run_id, "theorem": row.theorem,
                                "module": row.module, "status": "failure",
                                "stage": "runner_exception",
                                "message": f"{type(exc).__name__}: {exc}"[:1500],
                                "steps": 0, "elapsed_ms": 0, "partial": True,
                                "synthetic_summary": True,
                            },
                            "step_count": 0,
                            "exporter_mode": exporter_mode,
                        }
                    completed += 1
                    with lock:
                        if log:
                            log(f"[{completed}/{len(pending)}] {row.theorem} -> "
                                f"{results[row.index]['summary'].get('status')}")

    ordered = [results[row.index] for row in rows if row.index in results]
    return finalize(cfg, rows, ordered, skipped, time.monotonic() - started,
                    archive=cfg.archive_work)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run one schema-4 structured atomization-trace shard",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--slice", type=Path, required=True,
                        help="shard TSV with index/theorem/module columns")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repo", type=Path,
                        default=Path(os.environ.get("NAZRIN_DIR", ".")),
                        help="Lake project root that contains Standalone/")
    parser.add_argument("--start", type=int, default=0, help="first shard row (inclusive)")
    parser.add_argument("--end", type=int, default=-1, help="last shard row (exclusive); -1 = all")
    parser.add_argument("--limit", type=int, default=0, help="cap rows (0 = no cap)")
    parser.add_argument("--jobs", type=int, default=2, help="parallel theorem processes")
    parser.add_argument("--timeout-seconds", type=float, default=180.0,
                        help="wall-clock cap per theorem process")
    parser.add_argument("--max-heartbeats", type=int, default=200_000)
    parser.add_argument("--max-steps", type=int, default=3000,
                        help="atomization step cap per theorem (paper §VI p.8)")
    parser.add_argument("--envelope-schema", type=int, default=3, choices=(3, 4),
                        help="NAZRIN_STRUCT_STEP_SCHEMA: 3 (Gate 1.2/1.3 envelope) or 4")
    parser.add_argument("--run-id", default="")
    parser.add_argument("--shard-id", type=int, default=None)
    parser.add_argument("--plan-sha256", default="",
                        help="immutable plan digest; recorded in meta.json")
    parser.add_argument("--exporter-mode", choices=("auto", "lean-run", "binary"), default="auto")
    parser.add_argument("--exporter-cmd", default="",
                        help="explicit command prefix run in --repo; MODULE THEOREM OUT_PATH are appended")
    parser.add_argument("--no-resume", action="store_true",
                        help="re-run theorems even when a summary already exists")
    parser.add_argument("--retry-failures", action="store_true",
                        help="resume successes only; re-run failed theorems")
    parser.add_argument("--force", action="store_true",
                        help="proceed even when the output directory holds foreign data")
    parser.add_argument("--archive-work", action="store_true",
                        help="compress work/ into work.tgz and remove the raw directory")
    parser.add_argument("--gzip-only", action="store_true",
                        help="keep only steps.jsonl.gz/theorems.jsonl.gz (CI artifacts)")
    parser.add_argument("--summarize-only", action="store_true",
                        help="rebuild theorems/stats from existing work/ files")
    parser.add_argument("--quiet", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        rows, _ = read_slice(args.slice)
    except (OSError, ConfigError) as exc:
        print(f"run_schema4_shard: {exc}", file=sys.stderr)
        return 2

    output_dir: Path = args.output_dir
    if output_dir.exists() and any(output_dir.iterdir()):
        if (not args.summarize_only and not (output_dir / "provenance.json").exists()
                and not args.force):
            print(
                f"run_schema4_shard: {output_dir} exists and is not a schema-4 shard "
                "run; refusing to overwrite (use --force)",
                file=sys.stderr,
            )
            return 2
    if args.jobs < 1:
        print("run_schema4_shard: --jobs must be >= 1", file=sys.stderr)
        return 2
    if args.timeout_seconds <= 0:
        print("run_schema4_shard: --timeout-seconds must be positive", file=sys.stderr)
        return 2

    run_id = args.run_id or time.strftime("schema4-%Y%m%d-%H%M%S")
    cfg = Config(
        repo=args.repo,
        slice_path=args.slice,
        output_dir=output_dir,
        rows_total=len(rows),
        rows_selected=0,
        jobs=max(1, args.jobs),
        timeout_seconds=args.timeout_seconds,
        max_heartbeats=max(1, args.max_heartbeats),
        max_steps=max(1, args.max_steps),
        envelope_schema=args.envelope_schema,
        run_id=run_id,
        shard_id=args.shard_id,
        plan_sha256=args.plan_sha256,
        limit=args.limit,
        window_start=args.start,
        window_end=args.end,
        exporter_mode=args.exporter_mode,
        exporter_cmd=args.exporter_cmd,
        resume=not args.no_resume,
        retry_failures=args.retry_failures,
        force=args.force,
        archive_work=args.archive_work,
        gzip_only=args.gzip_only,
        quiet=args.quiet,
    )
    selected = select_rows(rows, cfg)
    cfg.rows_selected = len(selected)
    if not selected:
        print("run_schema4_shard: empty selection", file=sys.stderr)
        return 2

    if args.summarize_only:
        if not (output_dir / "work").is_dir():
            print("run_schema4_shard: --summarize-only needs the raw work/ directory",
                  file=sys.stderr)
            return 2
        stats = summarize_only(cfg, selected)
        print(f"schema4 shard summarised: {stats['theorems']['succeeded']}/"
              f"{stats['theorems']['processed']} theorems, {stats['steps']['total']} steps "
              f"-> {output_dir}", flush=True)
        return 0

    try:
        exporter, exporter_mode = resolve_exporter(cfg)
    except ConfigError as exc:
        print(f"run_schema4_shard: {exc}", file=sys.stderr)
        return 2
    cfg.exporter_mode = exporter_mode

    log = None if args.quiet else (lambda message: print(message, flush=True))
    stats = run(cfg, selected, exporter, exporter_mode, log=log)
    print(
        f"schema4 shard: {stats['theorems']['succeeded']}/{stats['theorems']['processed']} "
        f"theorems, {stats['steps']['total']} steps, {stats['theorems']['resumed']} resumed "
        f"-> {output_dir}",
        flush=True,
    )
    if stats["theorems"]["succeeded"] == 0:
        return 3
    if stats["theorems"]["processed"] != len(selected):
        return 3
    if not stats["steps"]["consistent"]:
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())