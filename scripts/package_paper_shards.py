#!/usr/bin/env python3
"""Validate and merge PaperTraceExport shard artifacts.

Each shard artifact is expected to contain ``steps.jsonl``, ``graphs.jsonl``,
``failures.jsonl``, ``meta.json``, and ``shard.tsv``.  A shard is accepted only
when its files are regular, its meta counts agree with the JSONL files, and its
input digest and requested-row count agree with the immutable plan.  Accepted
records are merged in plan order; rejected shards are reported, not silently
mixed in.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
from typing import Any


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
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def _plan_shards(plan: dict[str, Any], expected_count: int | None) -> list[dict[str, Any]]:
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
    total = plan.get("total_rows")
    if not isinstance(total, int) or isinstance(total, bool) or total < 1:
        raise ValueError("plan total_rows must be a positive integer")
    if plan.get("input", {}).get("columns", []) and "theorem" not in plan["input"]["columns"]:
        raise ValueError("plan input lacks a theorem column")

    checked: list[dict[str, Any]] = []
    for index, entry in enumerate(shards):
        if not isinstance(entry, dict):
            raise ValueError(f"plan shard {index} must be an object")
        shard_id = entry.get("id")
        name = entry.get("file")
        rows = entry.get("rows")
        digest = entry.get("sha256")
        if not isinstance(shard_id, int) or isinstance(shard_id, bool) or shard_id != index:
            raise ValueError(f"plan shard IDs must be sequential; expected {index}")
        if not isinstance(name, str) or Path(name).name != name or not name.endswith(".tsv"):
            raise ValueError(f"plan shard {index} has an unsafe file name")
        if not isinstance(rows, int) or isinstance(rows, bool) or rows < 1:
            raise ValueError(f"plan shard {index} has an invalid row count")
        if not _is_hex_digest(digest):
            raise ValueError(f"plan shard {index} has an invalid SHA256")
        checked.append(entry)
    if sum(int(entry["rows"]) for entry in checked) != total:
        raise ValueError("plan total_rows does not equal the sum of shard rows")
    return checked


def _validate_shard(
    entry: dict[str, Any],
    artifact_dir: Path,
    limit: int,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, list[dict[str, Any]]]]:
    issues: list[str] = []
    shard_id = int(entry["id"])
    expected_requested = min(int(entry["rows"]), limit) if limit > 0 else int(entry["rows"])

    for name in ("steps.jsonl", "graphs.jsonl", "failures.jsonl", "meta.json"):
        if not _safe_file(artifact_dir / name):
            issues.append(f"{name} is missing or unsafe")
    if issues:
        return {"id": shard_id, "valid": False, "issues": issues}, {}, {}

    meta = _read_json(artifact_dir / "meta.json", "meta.json")
    records = {
        "steps": _read_jsonl(artifact_dir / "steps.jsonl", "steps.jsonl"),
        "graphs": _read_jsonl(artifact_dir / "graphs.jsonl", "graphs.jsonl"),
        "failures": _read_jsonl(artifact_dir / "failures.jsonl", "failures.jsonl"),
    }

    if meta.get("schema") != 1:
        issues.append("meta schema must be 1")
    if meta.get("module") != "Mathlib":
        issues.append("meta module must be Mathlib")
    if meta.get("input_sha256") != entry["sha256"]:
        issues.append("meta input_sha256 does not match the plan shard digest")
    if meta.get("theorems_requested") != expected_requested:
        issues.append(
            f"meta theorems_requested {meta.get('theorems_requested')!r} "
            f"does not match expected {expected_requested}"
        )
    for field, actual in (("steps", len(records["steps"])),
                          ("graphs", len(records["graphs"])),
                          ("theorems_failed", len(records["failures"]))):
        value = meta.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value != actual:
            issues.append(f"meta {field} {value!r} does not match {actual} records")
    requested = meta.get("theorems_requested")
    succeeded = meta.get("theorems_succeeded")
    failed = meta.get("theorems_failed")
    if not all(isinstance(value, int) and not isinstance(value, bool)
               for value in (requested, succeeded, failed)):
        issues.append("meta theorem counts must be integers")
    elif succeeded + failed != requested:
        issues.append("meta theorem_succeeded + theorem_failed does not equal requested")

    for index, step in enumerate(records["steps"]):
        if step.get("schema") != 1 or not isinstance(step.get("theorem"), str) \
                or not isinstance(step.get("step"), int) or not isinstance(step.get("goal_id"), str):
            issues.append(f"steps.jsonl record {index} lacks the required schema fields")
            break
    for index, graph in enumerate(records["graphs"]):
        if graph.get("schema") != 1 or not isinstance(graph.get("theorem"), str) \
                or not isinstance(graph.get("goal_id"), str) or not isinstance(graph.get("graph"), dict):
            issues.append(f"graphs.jsonl record {index} lacks the required schema fields")
            break
    for index, failure in enumerate(records["failures"]):
        if not isinstance(failure.get("theorem"), str) \
                or not isinstance(failure.get("stage"), str) \
                or not isinstance(failure.get("message"), str):
            issues.append(f"failures.jsonl record {index} lacks the required fields")
            break

    shard_tsv = artifact_dir / "shard.tsv"
    if _safe_file(shard_tsv):
        digest = _sha256(shard_tsv.read_bytes())
        if digest != entry["sha256"]:
            issues.append("shard.tsv digest does not match the plan")
    else:
        issues.append("shard.tsv is missing or unsafe")

    summary = {
        "id": shard_id,
        "file": entry["file"],
        "rows": entry["rows"],
        "sha256": entry["sha256"],
        "artifact": artifact_dir.name,
        "valid": not issues,
        "issues": issues,
        "meta_sha256": _sha256((artifact_dir / "meta.json").read_bytes()),
        "counts": {
            "requested": requested,
            "succeeded": succeeded,
            "failed": failed,
            "steps": len(records["steps"]),
            "graphs": len(records["graphs"]),
            "failures": len(records["failures"]),
            "warnings": meta.get("warnings"),
            "unmodeled_steps": meta.get("unmodeled_steps"),
            "elapsed_ms": meta.get("elapsed_ms"),
        },
    }
    return summary, meta, records if not issues else {}


def package(
    plan_path: Path,
    downloads: Path,
    output: Path,
    *,
    run_id: str,
    limit: int = 0,
    expected_plan_sha: str | None = None,
    shard_count: int | None = None,
    source_ref: str = "",
    mathlib_commit: str = "",
    slice_path: str = "",
    prepare_result: str = "",
    shards_result: str = "",
) -> dict[str, Any]:
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    output.mkdir(parents=True, exist_ok=True)
    shards_dir = output / "shards"
    plan_out = output / "plan"
    shards_dir.mkdir(exist_ok=True)
    plan_out.mkdir(exist_ok=True)

    issues: list[str] = []
    missing: list[int] = []
    invalid: list[int] = []
    merged: dict[str, list[dict[str, Any]]] = {"steps": [], "graphs": [], "failures": []}
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
        artifact_dir = downloads / f"paper-trace-shard-{shard_id:02d}-{run_id}"
        try:
            if not artifact_dir.is_dir() or artifact_dir.is_symlink():
                raise ValueError("artifact directory is missing")
            report, _meta, records = _validate_shard(entry, artifact_dir, limit)
        except Exception as exc:
            report = {"id": shard_id, "file": entry["file"], "rows": entry["rows"],
                      "sha256": entry["sha256"], "valid": False,
                      "issues": [str(exc)]}
            records = {}
        shard_reports.append(report)
        if report.get("valid"):
            validated += 1
            for key in merged:
                merged[key].extend(records.get(key, []))
            destination = shards_dir / f"shard-{shard_id:02d}"
            destination.mkdir(exist_ok=True)
            for name in ("steps.jsonl", "graphs.jsonl", "failures.jsonl", "meta.json", "shard.tsv"):
                source = artifact_dir / name
                if _safe_file(source):
                    shutil.copy2(source, destination / name)
        else:
            invalid.append(shard_id)
            if report.get("issues") and report["issues"] == ["artifact directory is missing"]:
                missing.append(shard_id)
            issues.extend(f"shard {shard_id:02d}: {message}" for message in report.get("issues", []))

    if plan:
        try:
            shutil.copy2(plan_path, plan_out / "plan.json")
            for entry in plan_shards:
                source = plan_path.parent / entry["file"]
                if not _safe_file(source):
                    issues.append(f"plan shard missing: {entry['file']}")
                else:
                    shutil.copy2(source, plan_out / entry["file"])
        except OSError as exc:
            issues.append(f"could not preserve plan: {exc}")

    merged["steps"] = [record for record in merged["steps"] if isinstance(record, dict)]
    _write_jsonl(output / "steps.jsonl", merged["steps"])
    _write_jsonl(output / "graphs.jsonl", merged["graphs"])
    _write_jsonl(output / "failures.jsonl", merged["failures"])

    warnings = 0
    unmodeled = 0
    elapsed = 0
    requested = succeeded = failed = 0
    for report in shard_reports:
        if not report.get("valid"):
            continue
        counts = report.get("counts", {})
        for source, key in (("warnings", "warnings"), ("unmodeled_steps", "unmodeled_steps"),
                            ("elapsed_ms", "elapsed_ms")):
            value = counts.get(source)
            if isinstance(value, int) and not isinstance(value, bool):
                if source == "warnings":
                    warnings += value
                elif source == "unmodeled_steps":
                    unmodeled += value
                else:
                    elapsed += value
        requested += int(counts.get("requested", 0))
        succeeded += int(counts.get("succeeded", 0))
        failed += int(counts.get("failed", 0))

    complete = bool(plan) and not issues and validated == len(plan_shards)
    status = "complete" if complete else "incomplete"
    if missing:
        issues.append(f"missing shards: {missing}")
    if invalid and set(invalid) != set(missing):
        issues.append(f"invalid shards: {invalid}")

    summary = {
        "schema": 1,
        "workflow": "paper-trace-export",
        "status": status,
        "complete": complete,
        "run_id": run_id,
        "source_ref": source_ref,
        "mathlib_commit": mathlib_commit,
        "slice": slice_path,
        "shard_count": shard_count if shard_count is not None else len(plan_shards),
        "limit": limit,
        "total_input_rows": total_input_rows,
        "shards_expected": shard_count if shard_count is not None else len(plan_shards),
        "shards_validated": validated,
        "theorems_requested": requested,
        "theorems_succeeded": succeeded,
        "theorems_failed": failed,
        "steps": len(merged["steps"]),
        "graphs": len(merged["graphs"]),
        "failures": len(merged["failures"]),
        "warnings": warnings,
        "unmodeled_steps": unmodeled,
        "elapsed_ms": elapsed,
    }
    report = {
        "schema": 1,
        "status": status,
        "complete": complete,
        "issues": issues,
        "missing_shards": missing,
        "invalid_shards": invalid,
        "plan_sha256": plan_sha,
        "expected_plan_sha256": expected_plan_sha,
        "plan": {
            "total_rows": total_input_rows,
            "shard_count": len(plan_shards),
        },
        "job_results": {"prepare": prepare_result, "shards": shards_result},
        "totals": {
            "theorems_requested": requested,
            "theorems_succeeded": succeeded,
            "theorems_failed": failed,
            "steps": len(merged["steps"]),
            "graphs": len(merged["graphs"]),
            "failures": len(merged["failures"]),
            "warnings": warnings,
            "unmodeled_steps": unmodeled,
            "elapsed_ms": elapsed,
        },
        "shards": shard_reports,
    }
    _write_json(output / "package-summary.json", summary)
    _write_json(output / "package-report.json", report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--downloads", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--expected-plan-sha", default="")
    parser.add_argument("--shard-count", type=int)
    parser.add_argument("--source-ref", default="")
    parser.add_argument("--mathlib-commit", default="")
    parser.add_argument("--slice", default="")
    parser.add_argument("--prepare-result", default="")
    parser.add_argument("--shards-result", default="")
    parser.add_argument("--step-summary", type=Path)
    args = parser.parse_args()

    try:
        report = package(
            args.plan, args.downloads, args.output,
            run_id=args.run_id,
            limit=args.limit,
            expected_plan_sha=args.expected_plan_sha or None,
            shard_count=args.shard_count,
            source_ref=args.source_ref,
            mathlib_commit=args.mathlib_commit,
            slice_path=args.slice,
            prepare_result=args.prepare_result,
            shards_result=args.shards_result,
        )
    except Exception as exc:
        print(f"package_paper_shards: {exc}", file=sys.stderr)
        return 1

    if args.step_summary is not None:
        summary = json.loads((args.output / "package-summary.json").read_text(encoding="utf-8"))
        lines = [
            "## Paper trace export package",
            "",
            f"- Status: **{summary['status']}**",
            f"- Validated shards: {summary['shards_validated']}/{summary['shards_expected']}",
            f"- Theorems requested: {summary['theorems_requested']}",
            f"- Theorems succeeded/failed: {summary['theorems_succeeded']}/{summary['theorems_failed']}",
            f"- Steps/graphs/failures: {summary['steps']}/{summary['graphs']}/{summary['failures']}",
            "",
        ]
        args.step_summary.write_text("\n".join(lines), encoding="utf-8")

    print(json.dumps({
        "complete": report["complete"],
        "shards_validated": len([s for s in report["shards"] if s.get("valid")]),
        "steps": report["totals"]["steps"],
        "issues": report["issues"],
    }, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
