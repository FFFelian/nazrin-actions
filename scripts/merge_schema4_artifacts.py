#!/usr/bin/env python3
"""Validate and merge schema-4 structured-trace shard artifacts.

Each shard artifact produced by `.github/workflows/schema4-trace-export.yml`
contains `meta.json`, `steps.jsonl` (or `.jsonl.gz`), `theorems.jsonl`
(or `.jsonl.gz`), `stats.json`, `shard.tsv`, and the small provenance/state
files.  A shard is accepted only when

* its `meta.json` agrees with the immutable plan (shard id, file digest, row
  count, plan digest, slice digest, requested theorem count);
* its `shard.tsv` matches the plan digest and lists exactly the summaries, in
  the same order;
* every digest and record count in `meta.json` re-computes from the uploaded
  bytes;
* every step record is a schema-4 envelope whose `theorem` belongs to the
  shard, and step records never jump back to an earlier theorem;
* no theorem appears in two shards.

Rejected shards are reported, never silently mixed in.  Accepted records are
merged in plan order into `steps.jsonl`/`theorems.jsonl` plus statistics.
Nothing is back-filled and no record is rewritten: the merged JSONL is the
concatenation of the uploaded, already-validated exporter output.

Usage:

    python3 scripts/merge_schema4_artifacts.py \
      --plan plan/plan.json \
      --downloads downloaded-shards \
      --output schema4-package \
      --run-id 1234567890 --limit 0
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import statistics
import sys
import time
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence

SCHEMA_VERSION = 4
ENVELOPE_SCHEMAS = (3, 4)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def digest_and_size(path: Path) -> tuple[str, int]:
    """SHA-256 and size of the *logical* JSONL bytes.

    The shard artifact may carry `steps.jsonl.gz`; `meta.json` records the
    digest and size of the uncompressed stream, so a `.gz` member has to be
    decompressed before it is compared.
    """

    if path.suffix != ".gz":
        return sha256_file(path), path.stat().st_size
    digest = hashlib.sha256()
    size = 0
    with gzip.open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
            size += len(chunk)
    return digest.hexdigest(), size


def write_json(path: Path, value: Any) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, path)


def open_jsonl(path: Path) -> Iterator[str]:
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as handle:
            for line in handle:
                yield line
    else:
        with path.open("r", encoding="utf-8") as handle:
            for line in handle:
                yield line


def pick_artifact(directory: Path, stem: str) -> Path | None:
    plain = directory / f"{stem}.jsonl"
    compressed = directory / f"{stem}.jsonl.gz"
    if plain.is_file() and not plain.is_symlink():
        return plain
    if compressed.is_file() and not compressed.is_symlink():
        return compressed
    return None


def gzip_copy(source: Path, destination: Path, level: int = 1) -> dict[str, Any]:
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


def read_json(path: Path, label: str) -> dict[str, Any]:
    if not path.is_file() or path.is_symlink():
        raise ValueError(f"{label} is missing or not a regular file")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"{label} is not valid UTF-8 JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain a JSON object")
    return value


def hex_digest(value: object) -> bool:
    return (isinstance(value, str) and len(value) == 64
            and all(character in "0123456789abcdef" for character in value))


# ---------------------------------------------------------------------------
# Plan
# ---------------------------------------------------------------------------


def load_plan(path: Path | None, expected_count: int | None) -> dict[str, Any] | None:
    if path is None:
        return None
    plan = read_json(path, "plan")
    if plan.get("schema") != 1:
        raise ValueError("plan schema must be 1")
    count = plan.get("shard_count")
    if not isinstance(count, int) or isinstance(count, bool) or not 1 <= count <= 20:
        raise ValueError("plan shard_count must be an integer from 1 to 20")
    if expected_count is not None and count != expected_count:
        raise ValueError(f"plan shard_count {count} does not match dispatch count {expected_count}")
    shards = plan.get("shards")
    if not isinstance(shards, list) or len(shards) != count:
        raise ValueError("plan shards must be a list with shard_count entries")
    identifiers = [entry.get("id") for entry in shards]
    if identifiers != list(range(count)):
        raise ValueError("plan shard ids must be 0..shard_count-1")
    for entry in shards:
        if not isinstance(entry.get("rows"), int) or entry["rows"] < 1:
            raise ValueError(f"plan shard {entry.get('id')} has an invalid row count")
        if not hex_digest(entry.get("sha256")):
            raise ValueError(f"plan shard {entry.get('id')} has no valid digest")
    input_info = plan.get("input")
    if not isinstance(input_info, dict) or not hex_digest(input_info.get("sha256")):
        raise ValueError("plan input must carry a SHA-256 digest")
    return plan


def plan_shards(plan: dict[str, Any] | None, shard_count: int | None) -> list[dict[str, Any]]:
    if plan is not None:
        return list(plan["shards"])
    count = shard_count if shard_count is not None else 0
    if not 1 <= count <= 20:
        raise ValueError("without --plan, --shard-count from 1 to 20 is required")
    return [{"id": identifier, "file": "", "rows": -1, "sha256": ""}
            for identifier in range(count)]


def expected_rows(entry: dict[str, Any], limit: int) -> int:
    rows = entry.get("rows", -1)
    if not isinstance(rows, int) or rows < 0:
        return -1
    return min(rows, limit) if limit else rows


# ---------------------------------------------------------------------------
# Shard discovery and validation
# ---------------------------------------------------------------------------


def discover(downloads: Path) -> dict[int, Path]:
    found: dict[int, Path] = {}
    duplicates: list[str] = []
    for meta_path in sorted(downloads.rglob("meta.json")):
        if meta_path.is_symlink():
            continue
        try:
            meta = json.loads(meta_path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            continue
        if not isinstance(meta, dict) or meta.get("kind") != "schema4-shard-meta":
            continue
        identifier = meta.get("shard_id")
        if not isinstance(identifier, int) or isinstance(identifier, bool):
            continue
        if identifier in found:
            duplicates.append(f"shard {identifier} also at {found[identifier].parent}")
            continue
        found[identifier] = meta_path.parent
    if duplicates:
        raise ValueError("duplicate shard artifacts: " + "; ".join(duplicates))
    return found


def validate_shard(directory: Path, entry: dict[str, Any], plan_sha: str,
                   limit: int) -> dict[str, Any]:
    identifier = entry["id"]
    issues: list[str] = []
    meta = read_json(directory / "meta.json", f"shard {identifier} meta")
    if meta.get("schema") != 1 or meta.get("kind") != "schema4-shard-meta":
        raise ValueError("meta.json is not a schema-4 shard meta")
    if meta.get("shard_id") != identifier:
        raise ValueError(f"meta shard_id {meta.get('shard_id')!r} does not match plan id")
    if meta.get("schema_version") != SCHEMA_VERSION:
        raise ValueError(f"meta schema_version {meta.get('schema_version')!r} is not 4")
    if plan_sha and meta.get("plan_sha256") != plan_sha:
        issues.append("meta plan_sha256 does not match the immutable plan")
    slice_info = meta.get("slice") or {}
    if entry.get("file") and slice_info.get("name") not in (entry["file"], None):
        issues.append(
            f"meta slice name {slice_info.get('name')!r} is not plan file {entry['file']!r}")
    if isinstance(entry.get("rows"), int) and entry["rows"] > 0 and \
            slice_info.get("rows_total") != entry["rows"]:
        issues.append("meta slice rows_total does not match the plan shard rows")
    rows_selected = meta.get("rows")
    expected = expected_rows(entry, limit)
    if not isinstance(rows_selected, int) or rows_selected < 1:
        issues.append("meta rows is not a positive integer")
    elif expected >= 0 and rows_selected != expected:
        issues.append(f"meta rows {rows_selected} does not match expected {expected}")

    steps_path = pick_artifact(directory, "steps")
    theorems_path = pick_artifact(directory, "theorems")
    if steps_path is None:
        raise ValueError("steps.jsonl(.gz) is missing")
    if theorems_path is None:
        raise ValueError("theorems.jsonl(.gz) is missing")

    artifacts = meta.get("artifacts")
    if not isinstance(artifacts, dict):
        raise ValueError("meta artifacts section is missing")
    steps_meta = artifacts.get("steps") or {}
    theorems_meta = artifacts.get("theorems") or {}
    steps_digest, steps_size = digest_and_size(steps_path)
    theorems_digest, theorems_size = digest_and_size(theorems_path)
    if steps_meta.get("sha256") != steps_digest:
        issues.append("steps digest does not match meta")
    if theorems_meta.get("sha256") != theorems_digest:
        issues.append("theorems digest does not match meta")
    if isinstance(steps_meta.get("bytes"), int) and steps_meta["bytes"] != steps_size:
        issues.append("steps size does not match meta")
    if isinstance(theorems_meta.get("bytes"), int) and theorems_meta["bytes"] != theorems_size:
        issues.append("theorems size does not match meta")

    shard_tsv = directory / "shard.tsv"
    if not shard_tsv.is_file() or shard_tsv.is_symlink():
        raise ValueError("shard.tsv is missing")
    tsv_sha = sha256_file(shard_tsv)
    if entry.get("sha256") and tsv_sha != entry["sha256"]:
        issues.append("shard.tsv digest does not match the plan")
    theorems_in_order = read_shard_theorems(shard_tsv)

    summaries: list[dict[str, Any]] = list(iter_summaries(theorems_path))
    for summary in summaries:
        if summary.get("schema_version") != SCHEMA_VERSION:
            issues.append(f"summary {summary.get('theorem')!r} is not schema 4")
            break
        if summary.get("record") != "theorem":
            issues.append("theorems.jsonl contains a non-summary record")
            break
    summary_names = [summary.get("theorem") for summary in summaries]
    if len(set(summary_names)) != len(summary_names):
        issues.append("theorems.jsonl repeats a theorem")
    if summary_names != theorems_in_order[: len(summary_names)]:
        issues.append("theorems.jsonl does not follow the shard.tsv order")
    expected_theorems = meta.get("theorems") or {}
    if isinstance(expected_theorems.get("processed"), int) and \
            expected_theorems["processed"] != len(summaries):
        issues.append("theorem count does not match meta")
    if isinstance(rows_selected, int) and rows_selected != len(summaries):
        issues.append("summary count does not match meta rows")

    step_counts: dict[str, int] = {}
    problematic: list[str] = []
    previous_index = -1
    name_to_position = {name: position for position, name in enumerate(summary_names)}
    steps_total = 0
    if True:
        for line_number, line in enumerate(open_jsonl(steps_path), 1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                issues.append(f"steps line {line_number} is not JSON")
                break
            if not isinstance(record, dict) or record.get("record") != "step":
                issues.append(f"steps line {line_number} is not a step record")
                break
            if record.get("schema_version") != SCHEMA_VERSION:
                issues.append(f"steps line {line_number} is not schema 4")
                break
            if record.get("schema") not in ENVELOPE_SCHEMAS:
                issues.append(f"steps line {line_number} has an invalid envelope schema")
                break
            name = record.get("theorem")
            position = name_to_position.get(name)
            if position is None:
                issues.append(f"steps line {line_number} names a theorem outside this shard")
                break
            if position < previous_index:
                issues.append(f"steps line {line_number} jumps back to an earlier theorem")
                break
            previous_index = position
            step_counts[name] = step_counts.get(name, 0) + 1
            steps_total += 1
    if meta.get("steps") != steps_total:
        issues.append(f"step count {steps_total} does not match meta {meta.get('steps')!r}")
    for summary in summaries:
        name = summary.get("theorem")
        claimed = summary.get("steps")
        actual = step_counts.get(name, 0)
        if isinstance(claimed, int) and actual > claimed:
            problematic.append(f"{name}: {actual} > summary steps {claimed}")
        elif isinstance(claimed, int) and actual < claimed and not summary.get("envelope_violations") \
                and not summary.get("partial"):
            problematic.append(f"{name}: {actual} < summary steps {claimed}")
    if problematic:
        issues.append("step/summary counts disagree: " + "; ".join(problematic[:10]))

    return {
        "id": identifier,
        "file": entry.get("file"),
        "directory": str(directory),
        "rows": len(summaries),
        "steps": steps_total,
        "theorems": summaries,
        "steps_path": steps_path,
        "valid": not issues,
        "issues": issues,
        "slice_sha256": slice_info.get("sha256"),
        "meta": meta,
    }


def iter_summaries(path: Path) -> Iterator[dict[str, Any]]:
    for line_number, line in enumerate(open_jsonl(path), 1):
        text = line.strip()
        if not text:
            continue
        try:
            record = json.loads(text)
        except json.JSONDecodeError as exc:
            raise ValueError(f"{path.name}:{line_number}: invalid JSON: {exc}") from exc
        if not isinstance(record, dict):
            raise ValueError(f"{path.name}:{line_number}: record is not an object")
        yield record


def read_shard_theorems(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    if not lines:
        raise ValueError("shard.tsv is empty")
    header = lines[0].split("\t")
    if "theorem" not in header:
        raise ValueError("shard.tsv has no theorem column")
    position = header.index("theorem")
    names: list[str] = []
    for line_number, line in enumerate(lines[1:], 2):
        if not line.strip():
            continue
        cells = line.split("\t")
        if position >= len(cells):
            raise ValueError(f"shard.tsv:{line_number}: missing theorem column")
        names.append(cells[position])
    return names


# ---------------------------------------------------------------------------
# Merge
# ---------------------------------------------------------------------------


def merge(downloads: Path, output: Path, *, plan: dict[str, Any] | None,
          plan_sha: str, shard_count: int | None, limit: int,
          run_id: str, slice_hint: str = "") -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    entries = plan_shards(plan, shard_count)
    plan_input_sha = ""
    if plan is not None:
        plan_input_sha = plan["input"]["sha256"]
    discovered = discover(downloads)

    reports: list[dict[str, Any]] = []
    accepted: list[dict[str, Any]] = []
    missing: list[int] = []
    invalid: list[int] = []
    seen_theorems: set[str] = set()
    duplicates: list[str] = []

    for entry in entries:
        identifier = entry["id"]
        directory = discovered.get(identifier)
        if directory is None:
            missing.append(identifier)
            reports.append({"id": identifier, "status": "missing", "valid": False,
                            "rows": 0, "steps": 0, "issues": ["no artifact with meta.json"]})
            continue
        try:
            report = validate_shard(directory, entry, plan_sha, limit)
        except (OSError, ValueError, UnicodeDecodeError) as exc:
            invalid.append(identifier)
            reports.append({"id": identifier, "status": "invalid", "valid": False,
                            "rows": 0, "steps": 0, "issues": [str(exc)]})
            continue
        shard_names = [summary.get("theorem") for summary in report["theorems"]]
        clash = [name for name in shard_names if name in seen_theorems]
        if clash:
            duplicates.extend(clash[:10])
            report["status"] = "invalid"
            report["valid"] = False
            report["issues"].append(
                f"theorem duplicated in an earlier shard: {clash[:3]}")
            invalid.append(identifier)
            reports.append({key: report[key] for key in
                            ("id", "status", "valid", "rows", "steps", "issues")})
            continue
        seen_theorems.update(shard_names)
        report["status"] = "accepted" if report["valid"] else "invalid"
        if report["valid"]:
            accepted.append(report)
        else:
            invalid.append(identifier)
        reports.append({key: report[key] for key in
                        ("id", "status", "valid", "rows", "steps", "issues")})

    steps_out = output / "steps.jsonl"
    theorems_out = output / "theorems.jsonl"
    summaries: list[dict[str, Any]] = []
    with steps_out.open("w", encoding="utf-8", newline="\n") as step_handle, \
            theorems_out.open("w", encoding="utf-8", newline="\n") as theorem_handle:
        for report in accepted:
            for line in open_jsonl(report["steps_path"]):
                text = line.rstrip("\n")
                if text:
                    step_handle.write(text + "\n")
            for summary in report["theorems"]:
                summaries.append(summary)
                theorem_handle.write(json.dumps(summary, sort_keys=True,
                                               separators=(",", ":")) + "\n")

    steps_gz = gzip_copy(steps_out, output / "steps.jsonl.gz")
    theorems_gz = gzip_copy(theorems_out, output / "theorems.jsonl.gz")
    stats = summarize(summaries, reports, accepted, run_id, plan, slice_hint)
    write_json(output / "stats.json", stats)
    (output / "stats.md").write_text(render_markdown(stats), encoding="utf-8")

    complete = not missing and not invalid and len(accepted) == len(entries)
    totals = {
        "shards": len(entries),
        "accepted": len(accepted),
        "missing": len(missing),
        "invalid": len(invalid),
        "theorems": len(summaries),
        "steps": stats["steps"]["total"],
        "succeeded": stats["theorems"]["succeeded"],
        "failed": stats["theorems"]["failed"],
    }
    report = {
        "schema": 1,
        "kind": "schema4-merge-report",
        "run_id": run_id,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "complete": complete,
        "plan_sha256": plan_sha,
        "plan_input_sha256": plan_input_sha,
        "slice": slice_hint,
        "limit": limit,
        "shard_count": len(entries),
        "totals": totals,
        "missing_shards": missing,
        "invalid_shards": invalid,
        "duplicate_theorems": len(duplicates),
        "shards": reports,
        "artifacts": {
            "steps": {**{key: steps_gz[key] for key in
                         ("name", "sha256", "uncompressed_sha256")},
                      "bytes": steps_gz["uncompressed_bytes"]},
            "theorems": {**{key: theorems_gz[key] for key in
                           ("name", "sha256", "uncompressed_sha256")},
                         "bytes": theorems_gz["uncompressed_bytes"]},
        },
    }
    write_json(output / "merge-report.json", report)
    provenance = {
        "schema": 1,
        "kind": "schema4-package-provenance",
        "run_id": run_id,
        "generated_at": report["generated_at"],
        "plan_sha256": plan_sha,
        "plan_input_sha256": plan_input_sha,
        "slice": slice_hint,
        "merge_runner": "scripts/merge_schema4_artifacts.py",
        "exporter": "Standalone/StructuredTraceV4.lean",
        "paper": ("Nazrin: An Atomic Neural Proof Automation Tactic in Lean 4; "
                  "§IV atomization, §V ExprGraph, §VI evaluation"),
        "accepted_shards": [item["id"] for item in accepted],
        "complete": complete,
        "tools": {"generator": "scripts/run_schema4_shard.py"},
    }
    write_json(output / "provenance.json", provenance)
    return report


# ---------------------------------------------------------------------------
# Statistics
# ---------------------------------------------------------------------------


def summarize(summaries: Sequence[dict[str, Any]], reports: Sequence[dict[str, Any]],
              accepted: Sequence[dict[str, Any]], run_id: str,
              plan: dict[str, Any] | None, slice_hint: str) -> dict[str, Any]:
    statuses: dict[str, int] = {}
    stages: dict[str, int] = {}
    envelope: dict[str, int] = {}
    schema4_totals: dict[str, int] = {}
    steps_per_theorem: list[int] = []
    wall: list[int] = []
    for summary in summaries:
        status = str(summary.get("status", "unknown"))
        statuses[status] = statuses.get(status, 0) + 1
        stage = str(summary.get("stage", "unknown"))
        stages[stage] = stages.get(stage, 0) + 1
        key = str(summary.get("schema", "?"))
        envelope[key] = envelope.get(key, 0) + 1
        steps = summary.get("steps")
        steps_per_theorem.append(int(steps) if isinstance(steps, int) else 0)
        if isinstance(summary.get("wall_ms"), int):
            wall.append(summary["wall_ms"])
        details = summary.get("schema4")
        if isinstance(details, dict):
            for counter, value in details.items():
                if isinstance(value, int) and not isinstance(value, bool):
                    schema4_totals[counter] = schema4_totals.get(counter, 0) + value
    success = statuses.get("success", 0)
    total_steps = sum(steps_per_theorem)
    return {
        "schema": 1,
        "record": "stats",
        "run_id": run_id,
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "slice": {"hint": slice_hint,
                  "name": (plan or {}).get("input", {}).get("name", ""),
                  "sha256": (plan or {}).get("input", {}).get("sha256", "")},
        "shards": {
            "planned": len(reports),
            "accepted": len(accepted),
            "missing": sum(1 for report in reports if report["status"] == "missing"),
            "invalid": sum(1 for report in reports if report["status"] == "invalid"),
        },
        "theorems": {
            "processed": len(summaries),
            "succeeded": success,
            "failed": len(summaries) - success,
            "success_rate": round(success / len(summaries), 6) if summaries else 0.0,
        },
        "steps": {
            "total": total_steps,
            "theorems_with_steps": sum(1 for count in steps_per_theorem if count),
            "min": min(steps_per_theorem) if steps_per_theorem else 0,
            "max": max(steps_per_theorem) if steps_per_theorem else 0,
            "mean": round(total_steps / len(summaries), 6) if summaries else 0.0,
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
        "per_shard": [
            {"id": report["id"], "rows": report["rows"], "steps": report["steps"],
             "status": report["status"]} for report in reports
        ],
    }


def render_markdown(stats: dict[str, Any]) -> str:
    theorems = stats["theorems"]
    steps = stats["steps"]
    lines = [
        "# Schema-4 structured trace package",
        "",
        f"- run id: `{stats['run_id']}`",
        f"- slice: `{stats['slice']['name']}` "
        f"(`{(stats['slice']['sha256'] or '')[:16]}`)",
        f"- shards: {stats['shards']['accepted']}/{stats['shards']['planned']} accepted, "
        f"{stats['shards']['missing']} missing, {stats['shards']['invalid']} invalid",
        f"- theorems: {theorems['succeeded']}/{theorems['processed']} succeeded "
        f"({theorems['success_rate'] * 100:.1f}%)",
        f"- steps: {steps['total']} total, {steps['mean']} mean",
        "",
        "## Per shard",
        "",
        "| shard | status | rows | steps |",
        "|---|---|---|---|",
    ]
    for shard in stats["per_shard"]:
        lines.append(f"| {shard['id']} | `{shard['status']}` | {shard['rows']} | {shard['steps']} |")
    lines += ["", "## Stages", "", "| stage | theorems |", "|---|---|"]
    for stage, count in stats["stages"].items():
        lines.append(f"| `{stage}` | {count} |")
    if stats["schema4"]:
        lines += ["", "## schema-4 counters", "", "| counter | total |", "|---|---|"]
        for key, value in stats["schema4"].items():
            lines.append(f"| `{key}` | {value} |")
    lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument("--downloads", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--plan", type=Path, default=None)
    parser.add_argument("--expected-plan-sha", default="")
    parser.add_argument("--shard-count", type=int, default=None)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--run-id", default="")
    parser.add_argument("--slice", default="", help="slice path recorded in provenance")
    parser.add_argument("--step-summary", type=Path, default=None)
    args = parser.parse_args(argv)

    try:
        plan = load_plan(args.plan, args.shard_count) if args.plan else None
    except (OSError, ValueError) as exc:
        print(f"merge_schema4_artifacts: {exc}", file=sys.stderr)
        return 2
    plan_sha = args.expected_plan_sha
    if plan is not None and not hex_digest(plan_sha):
        plan_sha = sha256_file(args.plan)
    if not args.downloads.is_dir():
        print(f"merge_schema4_artifacts: {args.downloads} is not a directory", file=sys.stderr)
        return 2
    try:
        report = merge(
            args.downloads, args.output, plan=plan, plan_sha=plan_sha,
            shard_count=args.shard_count, limit=args.limit,
            run_id=args.run_id or time.strftime("schema4-merge-%Y%m%d-%H%M%S"),
            slice_hint=args.slice,
        )
    except (OSError, ValueError) as exc:
        print(f"merge_schema4_artifacts: {exc}", file=sys.stderr)
        return 2

    totals = report["totals"]
    print(
        f"schema4 merge: {totals['accepted']}/{totals['shards']} shards, "
        f"{totals['theorems']} theorems, {totals['steps']} steps, "
        f"complete={report['complete']} -> {args.output}",
        flush=True,
    )
    if args.step_summary:
        lines = [
            "### Schema-4 trace package",
            "",
            f"- shards accepted: {totals['accepted']}/{totals['shards']}",
            f"- theorems: {totals['succeeded']}/{totals['theorems']} succeeded",
            f"- steps: {totals['steps']}",
            f"- complete: `{report['complete']}`",
            "",
        ]
        with args.step_summary.open("a", encoding="utf-8") as handle:
            handle.write("\n".join(lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())