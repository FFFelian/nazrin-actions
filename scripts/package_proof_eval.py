#!/usr/bin/env python3
"""Validate and aggregate paper-aligned NPA proof-evaluation shard artifacts.

Each shard artifact is expected to contain ``results.jsonl``, ``summary.json``,
``shard.tsv``, and ``checkpoint.json``. A shard is accepted only when it is a
regular directory, its input TSV digest and theorem list match the immutable
plan, every result has a terminal status, the per-status counts agree with the
summary and the actual records, and the summary records the requested
checkpoint, module, device, and search parameters. Rejected shards are
reported and never merged.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import shutil
import sys
from datetime import datetime, timezone
from typing import Any


STATUSES = ("success", "failure", "timeout", "error")
REQUIRED_RESULT_FIELDS = ("theorem", "status", "elapsed_ms", "steps")


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _safe_file(path: Path) -> bool:
    return path.is_file() and not path.is_symlink()


def _read_json(path: Path, label: str) -> dict[str, Any]:
    if not _safe_file(path):
        raise ValueError(f"{label} is missing, unsafe, or not a regular file")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"{label} is not valid UTF-8 JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise ValueError(f"{label} must contain a JSON object")
    return value


def _read_jsonl(path: Path, label: str) -> list[dict[str, Any]]:
    if not _safe_file(path):
        raise ValueError(f"{label} is missing, unsafe, or not a regular file")
    records: list[dict[str, Any]] = []
    try:
        with path.open(encoding="utf-8", errors="strict") as handle:
            for line_number, line in enumerate(handle, 1):
                if not line.strip():
                    continue
                try:
                    value = json.loads(line)
                except json.JSONDecodeError as exc:
                    raise ValueError(f"{label}:{line_number}: invalid JSON: {exc}") from exc
                if not isinstance(value, dict):
                    raise ValueError(f"{label}:{line_number}: expected a JSON object")
                records.append(value)
    except OSError as exc:
        raise ValueError(f"{label}: cannot read: {exc}") from exc
    return records


def _write_json(path: Path, value: dict[str, Any]) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def _write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.write_text(
        "".join(json.dumps(record, ensure_ascii=False, separators=(",", ":")) + "\n"
                for record in records),
        encoding="utf-8",
    )


def _is_hex_digest(value: object) -> bool:
    return (isinstance(value, str) and len(value) == 64
            and all(character in "0123456789abcdef" for character in value))


def _is_count(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def _plan_shards(plan: dict[str, Any], expected_count: int | None) -> list[dict[str, Any]]:
    if plan.get("schema") != 1:
        raise ValueError("plan schema must be 1")
    count = plan.get("shard_count")
    if not _is_count(count) or not 1 <= count <= 20:
        raise ValueError("plan shard_count must be an integer from 1 to 20")
    if expected_count is not None and count != expected_count:
        raise ValueError(f"plan shard_count {count} does not match dispatch count {expected_count}")
    shards = plan.get("shards")
    if not isinstance(shards, list) or len(shards) != count:
        raise ValueError("plan shards must be a list with shard_count entries")
    total = plan.get("total_rows")
    if not _is_count(total) or total < 1:
        raise ValueError("plan total_rows must be a positive integer")
    input_info = plan.get("input")
    if not isinstance(input_info, dict):
        raise ValueError("plan input metadata is missing")
    columns = input_info.get("columns")
    theorem_column = input_info.get("theorem_column")
    if not isinstance(columns, list) or columns.count("theorem") != 1:
        raise ValueError("plan input must contain exactly one theorem column")
    if not _is_count(theorem_column) or theorem_column >= len(columns):
        raise ValueError("plan input theorem_column is invalid")
    if columns[theorem_column] != "theorem":
        raise ValueError("plan input theorem_column does not point at the theorem column")

    checked: list[dict[str, Any]] = []
    for index, entry in enumerate(shards):
        if not isinstance(entry, dict):
            raise ValueError(f"plan shard {index} must be an object")
        shard_id = entry.get("id")
        name = entry.get("file")
        rows = entry.get("rows")
        digest = entry.get("sha256")
        if not _is_count(shard_id) or shard_id != index:
            raise ValueError(f"plan shard IDs must be sequential; expected {index}")
        if not isinstance(name, str) or Path(name).name != name or not name.endswith(".tsv"):
            raise ValueError(f"plan shard {index} has an unsafe file name")
        if not _is_count(rows) or rows < 1:
            raise ValueError(f"plan shard {index} has an invalid row count")
        if not _is_hex_digest(digest):
            raise ValueError(f"plan shard {index} has an invalid SHA256")
        checked.append(entry)
    if sum(int(entry["rows"]) for entry in checked) != total:
        raise ValueError("plan total_rows does not equal the sum of shard rows")
    return checked


def _shard_theorems(path: Path, entry: dict[str, Any]) -> list[str]:
    if not _safe_file(path):
        raise ValueError("shard.tsv is missing or unsafe")
    payload = path.read_bytes()
    if _sha256(payload) != entry["sha256"]:
        raise ValueError("shard.tsv digest does not match the plan")
    try:
        text = payload.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise ValueError(f"shard.tsv is not valid UTF-8: {exc}") from exc
    lines = text.splitlines()
    if not lines:
        raise ValueError("shard.tsv is empty")
    if any(line == "" for line in lines):
        raise ValueError("shard.tsv contains blank lines")
    header = lines[0].split("\t")
    positions = [index for index, name in enumerate(header) if name == "theorem"]
    if len(positions) != 1:
        raise ValueError("shard.tsv must contain exactly one theorem column")
    position = positions[0]
    names: list[str] = []
    for line_number, line in enumerate(lines[1:], start=2):
        fields = line.split("\t")
        if len(fields) != len(header):
            raise ValueError(f"shard.tsv:{line_number}: expected {len(header)} columns")
        name = fields[position]
        if not name:
            raise ValueError(f"shard.tsv:{line_number}: empty theorem name")
        names.append(name)
    if len(names) != entry["rows"]:
        raise ValueError(
            f"shard.tsv has {len(names)} theorem rows, expected {entry['rows']}"
        )
    if len(set(names)) != len(names):
        raise ValueError("shard.tsv contains duplicate theorem names")
    return names


def _validate_result(record: dict[str, Any], index: int) -> str:
    for field in REQUIRED_RESULT_FIELDS:
        if field not in record:
            raise ValueError(f"results.jsonl record {index} lacks {field}")
    theorem = record.get("theorem")
    status = record.get("status")
    elapsed = record.get("elapsed_ms")
    steps = record.get("steps")
    if not isinstance(theorem, str) or not theorem:
        raise ValueError(f"results.jsonl record {index} has an invalid theorem")
    if status not in STATUSES:
        raise ValueError(f"results.jsonl record {index} has an invalid status {status!r}")
    if (not isinstance(elapsed, (int, float)) or isinstance(elapsed, bool)
            or not math.isfinite(float(elapsed)) or elapsed < 0):
        raise ValueError(f"results.jsonl record {index} has an invalid elapsed_ms")
    if not _is_count(steps):
        raise ValueError(f"results.jsonl record {index} has an invalid step count")
    return str(status)


def _validate_summary(
    summary: dict[str, Any],
    *,
    expected_total: int,
    expected_checkpoint: str,
    expected_time_limit: float,
    expected_max_steps: int,
    expected_top_k: int,
) -> None:
    for field in ("total", *STATUSES):
        if not _is_count(summary.get(field)):
            raise ValueError(f"summary {field} must be a nonnegative integer")
    if summary["total"] != expected_total:
        raise ValueError("summary total does not match the shard row count")
    if sum(summary[field] for field in STATUSES) != summary["total"]:
        raise ValueError("summary status counts do not sum to total")
    if summary.get("module") != "Mathlib":
        raise ValueError("summary module must be Mathlib")
    if summary.get("policy") != "npa":
        raise ValueError("summary policy must be npa")
    if summary.get("mock") is not False:
        raise ValueError("summary must record a non-mock evaluation")
    if str(summary.get("checkpoint_sha256", "")).lower() != expected_checkpoint:
        raise ValueError("summary checkpoint_sha256 does not match the dispatch digest")
    checkpoint = summary.get("checkpoint")
    if isinstance(checkpoint, dict) and checkpoint.get("sha256") is not None:
        if str(checkpoint["sha256"]).lower() != expected_checkpoint:
            raise ValueError("summary checkpoint.sha256 does not match the dispatch digest")
    if float(summary.get("time_limit_seconds", summary.get("time_limit", -1))) != expected_time_limit:
        raise ValueError("summary time limit does not match the dispatch value")
    if summary.get("max_steps") != expected_max_steps:
        raise ValueError("summary max_steps does not match the dispatch value")
    if summary.get("top_k") != expected_top_k:
        raise ValueError("summary top_k does not match the dispatch value")
    if summary.get("device") != "cpu":
        raise ValueError("summary device must be cpu")


def _validate_shard(
    entry: dict[str, Any],
    artifact_dir: Path,
    *,
    checkpoint_sha256: str,
    time_limit: float,
    max_steps: int,
    top_k: int,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    issues: list[str] = []
    shard_id = int(entry["id"])
    for name in ("results.jsonl", "summary.json", "shard.tsv", "checkpoint.json"):
        if not _safe_file(artifact_dir / name):
            issues.append(f"{name} is missing or unsafe")
    if issues:
        return {"id": shard_id, "file": entry["file"], "rows": entry["rows"],
                "sha256": entry["sha256"], "valid": False, "issues": issues}, []

    try:
        names = _shard_theorems(artifact_dir / "shard.tsv", entry)
    except ValueError as exc:
        return {"id": shard_id, "file": entry["file"], "rows": entry["rows"],
                "sha256": entry["sha256"], "valid": False, "issues": [str(exc)]}, []

    try:
        results = _read_jsonl(artifact_dir / "results.jsonl", "results.jsonl")
        statuses = [_validate_result(record, index) for index, record in enumerate(results)]
        summary = _read_json(artifact_dir / "summary.json", "summary.json")
        _validate_summary(
            summary,
            expected_total=len(names),
            expected_checkpoint=checkpoint_sha256,
            expected_time_limit=time_limit,
            expected_max_steps=max_steps,
            expected_top_k=top_k,
        )
        if len(results) != len(names):
            raise ValueError(
                f"results.jsonl has {len(results)} records, expected {len(names)}"
            )
        observed = [str(record["theorem"]) for record in results]
        if observed != names:
            raise ValueError("results.jsonl theorem order does not match shard.tsv")
        if len(set(observed)) != len(observed):
            raise ValueError("results.jsonl contains duplicate theorem names")
        computed = {status: statuses.count(status) for status in STATUSES}
        for status in STATUSES:
            if summary[status] != computed[status]:
                raise ValueError(f"summary {status} does not match results.jsonl")
        checkpoint_path = artifact_dir / "checkpoint.json"
        if checkpoint_path.exists():
            checkpoint = _read_json(checkpoint_path, "checkpoint.json")
            if str(checkpoint.get("sha256", "")).lower() != checkpoint_sha256:
                raise ValueError("checkpoint.json digest does not match the dispatch digest")
    except (TypeError, ValueError) as exc:
        return {"id": shard_id, "file": entry["file"], "rows": entry["rows"],
                "sha256": entry["sha256"], "valid": False, "issues": [str(exc)]}, []

    report = {
        "id": shard_id,
        "file": entry["file"],
        "rows": entry["rows"],
        "sha256": entry["sha256"],
        "valid": True,
        "issues": [],
        "counts": {
            "total": len(results),
            **computed,
        },
        "summary_sha256": _sha256((artifact_dir / "summary.json").read_bytes()),
        "results_sha256": _sha256((artifact_dir / "results.jsonl").read_bytes()),
    }
    return report, results


def package(
    plan_path: Path,
    downloads: Path,
    output: Path,
    *,
    run_id: str,
    shard_count: int | None = None,
    expected_plan_sha: str | None = None,
    checkpoint_sha256: str = "",
    time_limit: float = 15.0,
    max_steps: int = 100,
    top_k: int = 5,
    source_ref: str = "",
    mathlib_commit: str = "",
    theorems_path: str = "",
    prepare_result: str = "",
    shards_result: str = "",
) -> dict[str, Any]:
    checkpoint_sha256 = checkpoint_sha256.strip()
    if checkpoint_sha256:
        if not _is_hex_digest(checkpoint_sha256.lower()):
            raise ValueError("checkpoint_sha256 must be a 64-character hexadecimal digest")
        checkpoint_sha256 = checkpoint_sha256.lower()
    else:
        checkpoint_sha256 = ""
    if time_limit <= 0:
        raise ValueError("time_limit must be positive")
    if max_steps < 1 or top_k < 1:
        raise ValueError("max_steps and top_k must be positive")

    output.mkdir(parents=True, exist_ok=True)
    shards_out = output / "shards"
    shards_out.mkdir(exist_ok=True)
    plan_out = output / "plan"
    plan_out.mkdir(exist_ok=True)

    issues: list[str] = []
    if not checkpoint_sha256:
        issues.append("checkpoint digest unavailable; prepare did not validate a checkpoint")
    missing: list[int] = []
    invalid: list[int] = []
    merged: list[dict[str, Any]] = []
    shard_reports: list[dict[str, Any]] = []
    plan: dict[str, Any] = {}
    plan_shards: list[dict[str, Any]] = []
    plan_sha: str | None = None
    total_input_rows: int | None = None
    validated = 0

    try:
        if not _safe_file(plan_path):
            raise ValueError("canonical plan unavailable; prepare failed or plan artifact is missing")
        plan_sha = _sha256(plan_path.read_bytes())
        if expected_plan_sha and plan_sha != expected_plan_sha:
            raise ValueError("plan digest mismatch")
        plan = _read_json(plan_path, "plan.json")
        plan_shards = _plan_shards(plan, shard_count)
        total_input_rows = int(plan["total_rows"])
    except Exception as exc:
        issues.append(str(exc))
        if shard_count is not None:
            missing = list(range(shard_count))

    for entry in plan_shards:
        shard_id = int(entry["id"])
        artifact_dir = downloads / f"paper-proof-eval-shard-{shard_id:02d}-{run_id}"
        if not artifact_dir.is_dir() or artifact_dir.is_symlink():
            missing.append(shard_id)
            report = {
                "id": shard_id,
                "file": entry["file"],
                "rows": entry["rows"],
                "sha256": entry["sha256"],
                "valid": False,
                "issues": ["artifact directory is missing"],
            }
        else:
            report, records = _validate_shard(
                entry,
                artifact_dir,
                checkpoint_sha256=checkpoint_sha256,
                time_limit=time_limit,
                max_steps=max_steps,
                top_k=top_k,
            )
        shard_reports.append(report)
        if report.get("valid"):
            validated += 1
            merged.extend(records)
            destination = shards_out / f"shard-{shard_id:02d}"
            destination.mkdir(exist_ok=True)
            for name in ("results.jsonl", "summary.json", "shard.tsv", "checkpoint.json"):
                source = artifact_dir / name
                if _safe_file(source):
                    shutil.copy2(source, destination / name)
        else:
            invalid.append(shard_id)
            issues.extend(f"shard {shard_id:02d}: {message}"
                          for message in report.get("issues", []))

    if plan:
        try:
            shutil.copy2(plan_path, plan_out / "plan.json")
            for entry in plan_shards:
                source = plan_path.parent / entry["file"]
                if _safe_file(source):
                    shutil.copy2(source, plan_out / entry["file"])
                else:
                    issues.append(f"plan shard missing: {entry['file']}")
        except OSError as exc:
            issues.append(f"could not preserve plan: {exc}")

    totals = {
        "total": len(merged),
        **{status: sum(1 for record in merged if record["status"] == status)
           for status in STATUSES},
    }
    totals["success_rate"] = (
        totals["success"] / totals["total"] if totals["total"] else 0.0
    )
    complete = bool(plan) and not issues and validated == len(plan_shards) \
        and total_input_rows is not None and len(merged) == total_input_rows
    status = "complete" if complete else "incomplete"

    if missing:
        issues.append(f"missing shards: {missing}")
    if invalid and set(invalid) != set(missing):
        issues.append(f"invalid shards: {invalid}")

    _write_jsonl(output / "results.jsonl", merged)
    summary = {
        "schema": 1,
        "workflow": "paper-proof-eval",
        "experiment": "Paper-aligned NPA 15-second proof evaluation",
        "status": status,
        "complete": complete,
        "run_id": run_id,
        "source_ref": source_ref,
        "mathlib_commit": mathlib_commit,
        "theorems": theorems_path,
        "theorems_sha256": plan.get("input", {}).get("sha256") if plan else None,
        "shard_count": shard_count if shard_count is not None else len(plan_shards),
        "shards_expected": len(plan_shards) if plan_shards else shard_count,
        "shards_validated": validated,
        "total_input_rows": total_input_rows,
        "total": totals["total"],
        "success": totals["success"],
        "failure": totals["failure"],
        "timeout": totals["timeout"],
        "error": totals["error"],
        "success_rate": totals["success_rate"],
        "time_limit_seconds": time_limit,
        "max_steps": max_steps,
        "top_k": top_k,
        "device": "cpu",
        "module": "Mathlib",
        "checkpoint_sha256": checkpoint_sha256,
        "generated_at": datetime.now(timezone.utc).isoformat(),
    }
    report = {
        "schema": 1,
        "workflow": "paper-proof-eval",
        "status": status,
        "complete": complete,
        "issues": issues,
        "missing_shards": sorted(set(missing)),
        "invalid_shards": sorted(set(invalid)),
        "prepare_result": prepare_result,
        "shards_result": shards_result,
        "plan_sha256": plan_sha,
        "expected_plan_sha256": expected_plan_sha,
        "plan": {
            "total_rows": total_input_rows,
            "shard_count": len(plan_shards) if plan_shards else shard_count,
        },
        "inputs": {
            "theorems": theorems_path,
            "checkpoint_sha256": checkpoint_sha256,
            "time_limit": time_limit,
            "max_steps": max_steps,
            "top_k": top_k,
            "device": "cpu",
            "module": "Mathlib",
            "source_ref": source_ref,
            "mathlib_commit": mathlib_commit,
        },
        "totals": totals,
        "shards": shard_reports,
    }
    _write_json(output / "evaluation-summary.json", summary)
    _write_json(output / "evaluation-report.json", report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--downloads", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--expected-plan-sha", default="")
    parser.add_argument("--shard-count", type=int)
    parser.add_argument("--checkpoint-sha256", required=True)
    parser.add_argument("--time-limit", type=float, default=15.0)
    parser.add_argument("--max-steps", type=int, default=100)
    parser.add_argument("--top-k", type=int, default=5)
    parser.add_argument("--source-ref", default="")
    parser.add_argument("--mathlib-commit", default="")
    parser.add_argument("--theorems", default="")
    parser.add_argument("--prepare-result", default="")
    parser.add_argument("--shards-result", default="")
    parser.add_argument("--step-summary", type=Path)
    args = parser.parse_args()

    try:
        report = package(
            args.plan,
            args.downloads,
            args.output,
            run_id=args.run_id,
            shard_count=args.shard_count,
            expected_plan_sha=args.expected_plan_sha or None,
            checkpoint_sha256=args.checkpoint_sha256,
            time_limit=args.time_limit,
            max_steps=args.max_steps,
            top_k=args.top_k,
            source_ref=args.source_ref,
            mathlib_commit=args.mathlib_commit,
            theorems_path=args.theorems,
            prepare_result=args.prepare_result,
            shards_result=args.shards_result,
        )
    except Exception as exc:
        print(f"package_proof_eval: {exc}", file=sys.stderr)
        return 1

    if args.step_summary is not None:
        summary = json.loads((args.output / "evaluation-summary.json").read_text(encoding="utf-8"))
        lines = [
            "## Paper-aligned NPA proof evaluation",
            "",
            f"- Status: **{summary['status']}**",
            f"- Validated shards: {summary['shards_validated']}/{summary['shards_expected']}",
            f"- Theorems evaluated: {summary['total']}",
            f"- Success/failure/timeout/error: {summary['success']}/{summary['failure']}/"
            f"{summary['timeout']}/{summary['error']}",
            f"- Success rate: {summary['success_rate']:.4f}",
            "",
        ]
        args.step_summary.write_text("\n".join(lines), encoding="utf-8")

    print(json.dumps({
        "complete": report["complete"],
        "shards_validated": len([shard for shard in report["shards"] if shard.get("valid")]),
        "total": report["totals"]["total"],
        "success": report["totals"]["success"],
        "failure": report["totals"]["failure"],
        "timeout": report["totals"]["timeout"],
        "error": report["totals"]["error"],
        "issues": report["issues"],
    }, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
