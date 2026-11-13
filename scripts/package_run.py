#!/usr/bin/env python3
"""Validate and package namespaced outputs from matrix atomization shards."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import tarfile
from typing import Any

from plan_shards import HEADER, parse_inventory, stable_shard
from run_shard import terminal_coverage


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _safe_child(root: Path, name: object) -> Path | None:
    if not isinstance(name, str) or not name or Path(name).name != name:
        return None
    candidate = root / name
    if candidate.is_symlink() or not candidate.is_file():
        return None
    return candidate


def _copy_tree_without_symlinks(source: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    for item in source.iterdir():
        target = destination / item.name
        if item.is_symlink():
            (destination / f"{item.name}.rejected-symlink.txt").write_text(
                "Symlink omitted from package.\n", encoding="utf-8"
            )
        elif item.is_dir():
            _copy_tree_without_symlinks(item, target)
        elif item.is_file():
            shutil.copy2(item, target)


def _summary_dirs(artifacts_root: Path) -> list[tuple[Path, dict[str, Any]]]:
    found = []
    for summary_path in sorted(artifacts_root.rglob("shard-summary.json")):
        if summary_path.is_symlink():
            continue
        try:
            value = json.loads(summary_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(value, dict) and isinstance(value.get("shard_id"), int):
            found.append((summary_path.parent, value))
    return found


def _validate_plan(plan: dict[str, Any], plan_dir: Path) -> tuple[list[dict[str, Any]], list[str]]:
    if plan.get("schema") != 1 or not isinstance(plan.get("shards"), list):
        raise ValueError("unsupported or malformed shard plan")
    count = plan.get("shard_count")
    if not isinstance(count, int) or count != len(plan["shards"]) or count < 1:
        raise ValueError("plan shard_count does not match shard entries")
    source_commit = plan.get("source_commit")
    if not isinstance(source_commit, str) or not re.fullmatch(r"[0-9a-fA-F]{40}", source_commit):
        raise ValueError("plan source_commit must be a full 40-character Git SHA")
    inventory_meta = plan.get("inventory")
    if not isinstance(inventory_meta, dict):
        raise ValueError("plan inventory metadata must be an object")
    if (not isinstance(inventory_meta.get("rows"), int)
            or not isinstance(inventory_meta.get("sha256"), str)
            or not re.fullmatch(r"[0-9a-fA-F]{64}", inventory_meta["sha256"])):
        raise ValueError("plan inventory metadata must contain a row count and SHA-256 digest")
    inventory_rows: list[dict[str, Any]] = []
    issues: list[str] = []
    seen_ids: set[int] = set()
    seen_indexes: set[int] = set()
    seen_names: set[tuple[str, str]] = set()
    for item in plan["shards"]:
        if not isinstance(item, dict) or not isinstance(item.get("id"), int):
            raise ValueError("malformed shard entry")
        shard_id = item["id"]
        if shard_id in seen_ids or not 0 <= shard_id < count:
            raise ValueError(f"duplicate or out-of-range shard id: {shard_id}")
        seen_ids.add(shard_id)
        shard_path = _safe_child(plan_dir, item.get("inventory"))
        if shard_path is None:
            issues.append(f"plan inventory missing or unsafe for shard {shard_id}")
            continue
        if sha256(shard_path) != item.get("sha256"):
            issues.append(f"plan inventory digest mismatch for shard {shard_id}")
            continue
        try:
            rows = parse_inventory(shard_path)
        except (OSError, ValueError) as exc:
            issues.append(f"plan inventory malformed for shard {shard_id}: {exc}")
            continue
        if len(rows) != item.get("rows"):
            issues.append(f"plan row count mismatch for shard {shard_id}")
        for row in rows:
            key = (row["index"], str(row["theorem"]), str(row["module"]))
            name_key = (str(row["module"]), str(row["theorem"]))
            if row["index"] in seen_indexes:
                issues.append(f"duplicate theorem index in plan: {row['index']}")
            if name_key in seen_names:
                issues.append(f"duplicate theorem assignment in plan: {name_key}")
            seen_indexes.add(row["index"])
            seen_names.add(name_key)
            expected = stable_shard(str(row["module"]), str(row["theorem"]), count)
            if expected != shard_id:
                issues.append(f"theorem assigned to wrong shard {shard_id}: {key}")
        inventory_rows.extend(rows)
    expected_rows = plan.get("inventory", {}).get("rows")
    if len(inventory_rows) != expected_rows:
        issues.append(f"planned rows {len(inventory_rows)} do not match inventory total {expected_rows}")

    canonical_rows: list[dict[str, Any]] | None = None
    canonical_path = _safe_child(plan_dir, "canonical-inventory.tsv")
    if canonical_path is None:
        issues.append("canonical inventory is missing or unsafe")
    else:
        if sha256(canonical_path) != plan.get("inventory", {}).get("sha256"):
            issues.append("canonical inventory digest mismatch")
        try:
            canonical_rows = parse_inventory(canonical_path)
        except (OSError, ValueError) as exc:
            issues.append(f"canonical inventory is malformed: {exc}")
        if canonical_rows is not None:
            shard_keys = {(r["index"], str(r["theorem"]), str(r["module"])) for r in inventory_rows}
            canonical_keys = {(r["index"], str(r["theorem"]), str(r["module"])) for r in canonical_rows}
            if len(canonical_rows) != expected_rows or canonical_keys != shard_keys:
                issues.append("shard inventories are not an exact partition of the canonical inventory")
    if canonical_rows is not None and len(canonical_rows) == expected_rows:
        inventory_rows = canonical_rows
    if "runtime_provenance_sha256" in plan:
        runtime = _safe_child(plan_dir, "runtime-provenance.json")
        if runtime is None or sha256(runtime) != plan["runtime_provenance_sha256"]:
            issues.append("plan runtime provenance missing or digest mismatch")
        else:
            try:
                identity = json.loads(runtime.read_text(encoding="utf-8"))
                if any(identity.get(key) != plan.get(key) for key in ("source_commit", "mathlib_commit", "runtime_manifest_sha256")):
                    issues.append("plan runtime identity mismatch")
            except (ValueError, AttributeError):
                issues.append("malformed plan runtime provenance")
    return inventory_rows, issues


def package(plan_path: Path, artifacts_root: Path, destination: Path) -> dict[str, Any]:
    plan_path = plan_path.resolve()
    plan_dir = plan_path.parent
    artifacts_root = artifacts_root.resolve()
    destination = destination.resolve()
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    if not isinstance(plan, dict):
        raise ValueError("plan root must be an object")
    planned_rows, issues = _validate_plan(plan, plan_dir)
    plan_issues = list(issues)
    count = plan["shard_count"]
    expected_by_id = {item["id"]: item for item in plan["shards"]}
    planned_by_id = {shard_id: [] for shard_id in range(count)}
    for row in planned_rows:
        shard_id = stable_shard(str(row["module"]), str(row["theorem"]), count)
        planned_by_id[shard_id].append(row)

    by_id: dict[int, list[tuple[Path, dict[str, Any]]]] = {}
    classified_dirs: set[Path] = set()
    for path, summary in _summary_dirs(artifacts_root):
        resolved = path.resolve()
        if resolved == artifacts_root or artifacts_root not in resolved.parents:
            issues.append(f"shard summary escapes artifact root: {path}")
            continue
        classified_dirs.add(resolved)
        by_id.setdefault(summary["shard_id"], []).append((path, summary))

    unclassified_paths: list[Path] = []
    for candidate in sorted(artifacts_root.iterdir()):
        resolved = candidate.resolve()
        contains_classified = any(
            resolved == shard_dir or resolved in shard_dir.parents for shard_dir in classified_dirs
        )
        if not contains_classified:
            unclassified_paths.append(candidate)
            issues.append(f"unclassified result artifact: {candidate.name}")
    unexpected = sorted(set(by_id) - set(range(count)))
    for shard_id in unexpected:
        issues.append(f"unexpected result artifact for shard {shard_id}")

    missing: list[int] = []
    duplicates: list[int] = []
    shard_reports: list[dict[str, Any]] = []
    covered: set[tuple[int, str, str]] = set()
    staged = destination / "package-content"
    if staged.exists():
        raise FileExistsError(f"refusing to overwrite existing package staging directory: {staged}")
    (staged / "shards").mkdir(parents=True)
    packaged_plan = staged / "plan"
    packaged_plan.mkdir()
    plan_names = {"plan.json", "canonical-inventory.tsv", "runtime-provenance.json"}
    plan_names.update(
        name for item in plan.get("shards", []) if isinstance(item, dict)
        for name in [item.get("inventory")]
        if isinstance(name, str) and re.fullmatch(r"shard-[0-9]{2,3}\.tsv", name)
    )
    for name in sorted(plan_names):
        source_path = plan_dir / name
        target_path = packaged_plan / name
        if source_path.is_symlink():
            target_path.write_text("Rejected symlink in plan artifact.\n", encoding="utf-8")
        elif source_path.is_file():
            shutil.copy2(source_path, target_path)

    for integration in sorted(plan_dir.glob("integration-attempt-*")):
        if integration.is_dir() and not integration.is_symlink():
            _copy_tree_without_symlinks(integration, packaged_plan / integration.name)

    for shard_id in range(count):
        matches = by_id.get(shard_id, [])
        planned = planned_by_id[shard_id]
        if not matches:
            missing.append(shard_id)
            shard_reports.append({"shard_id": shard_id, "status": "missing_artifact",
                                  "pending_rows": len(planned)})
            continue
        if len(matches) != 1:
            duplicates.append(shard_id)
            issues.append(f"multiple result artifacts for shard {shard_id}")
            shard_reports.append({"shard_id": shard_id, "status": "duplicate_artifact",
                                  "pending_rows": len(planned)})
            for index, (artifact_dir, _summary) in enumerate(matches):
                _copy_tree_without_symlinks(artifact_dir, staged / "shards" / f"duplicate-{shard_id:02d}-{index}")
            continue

        artifact_dir, summary = matches[0]
        entry = expected_by_id[shard_id]
        trusted = not plan_issues
        summary_source = summary.get("source_commit")
        plan_source = plan.get("source_commit")
        if (not isinstance(summary_source, str) or not isinstance(plan_source, str)
                or summary_source.lower() != plan_source.lower()):
            issues.append(f"source commit mismatch for shard {shard_id}")
            trusted = False
        if "runtime_manifest_sha256" in plan:
            runtime_file = _safe_child(artifact_dir, "runtime-provenance.json")
            if (summary.get("runtime_manifest_sha256") != plan["runtime_manifest_sha256"]
                    or runtime_file is None or sha256(runtime_file) != plan["runtime_provenance_sha256"]):
                issues.append(f"runtime provenance mismatch for shard {shard_id}")
                trusted = False
        if summary.get("inventory_sha256") != entry.get("sha256"):
            issues.append(f"inventory digest mismatch for shard result {shard_id}")
            trusted = False
        shard_input = _safe_child(artifact_dir, "shard-input.tsv")
        if shard_input is None or sha256(shard_input) != entry.get("sha256"):
            issues.append(f"shard input missing or digest mismatch for result {shard_id}")
            trusted = False

        rows: list[dict[str, Any]] = []
        if trusted:
            try:
                rows = parse_inventory(shard_input)
            except (OSError, ValueError) as exc:
                issues.append(f"malformed shard input for result {shard_id}: {exc}")
                trusted = False
            if trusted and len(rows) != entry.get("rows"):
                issues.append(f"result row count mismatch for shard {shard_id}")
                trusted = False

        if trusted:
            _pending_rows, recomputed = terminal_coverage(rows, artifact_dir)
            row_keys = {(r["index"], str(r["theorem"]), str(r["module"])) for r in rows}
            pending_keys = {(r["index"], str(r["theorem"]), str(r["module"]))
                            for r in _pending_rows}
        else:
            _pending_rows = planned
            row_keys = set()
            pending_keys = {(r["index"], str(r["theorem"]), str(r["module"])) for r in planned}
            recomputed = {"inventory_rows": len(planned), "terminal_rows": 0,
                          "pending_rows": len(planned), "terminal_status_counts": {},
                          "invalid_ledger_rows": 0, "unknown_ledger_rows": 0,
                          "missing_terminal_artifacts": 0}

        shard_invalid = False
        if summary.get("inventory_rows") != entry.get("rows"):
            issues.append(f"summary inventory row count mismatch for shard {shard_id}")
            shard_invalid = True
        if summary.get("pending_rows") != recomputed["pending_rows"]:
            issues.append(f"summary pending row count mismatch for shard {shard_id}")
            shard_invalid = True
        if summary.get("terminal_rows") != recomputed["terminal_rows"]:
            issues.append(f"summary terminal row count mismatch for shard {shard_id}")
            shard_invalid = True
        if summary.get("terminal_status_counts") != recomputed["terminal_status_counts"]:
            issues.append(f"summary terminal status counts mismatch for shard {shard_id}")
            shard_invalid = True
        shard_status = summary.get("status")
        if shard_status == "failed":
            issues.append(f"shard {shard_id} failed; retaining validated terminal outcomes")
        elif shard_status not in {"finished", "interrupted"}:
            issues.append(f"shard {shard_id} status is {shard_status!r}")
            shard_invalid = True
        elif shard_status == "interrupted":
            issues.append(f"shard {shard_id} stopped before its full inventory completed")
        elif summary.get("supervisor_exit_code") != 0:
            issues.append(f"finished shard {shard_id} has a nonzero supervisor exit code")
            shard_invalid = True
        if summary.get("timeout_seconds_per_theorem") != 30:
            issues.append(f"shard {shard_id} did not use the fixed 30-second theorem timeout")
            shard_invalid = True
        if summary.get("lean_internal_workers") != 2:
            issues.append(f"shard {shard_id} did not use two Lean internal workers")
            shard_invalid = True
        for stat_key in ("invalid_ledger_rows", "unknown_ledger_rows", "missing_terminal_artifacts"):
            if recomputed[stat_key]:
                issues.append(f"shard {shard_id} has {recomputed[stat_key]} {stat_key}")
                shard_invalid = True
        for item_path in artifact_dir.rglob("*"):
            if item_path.is_symlink():
                issues.append(f"symlink in shard artifact {shard_id}: {item_path.relative_to(artifact_dir)}")
                shard_invalid = True
                break
        if shard_invalid:
            trusted = False
            recomputed["terminal_rows"] = 0
            recomputed["pending_rows"] = len(planned)
            recomputed["terminal_status_counts"] = {}
        elif trusted:
            covered.update(row_keys - pending_keys)
        _copy_tree_without_symlinks(artifact_dir, staged / "shards" / f"shard-{shard_id:02d}")
        shard_reports.append({
            "shard_id": shard_id,
            "status": summary.get("status"),
            "inventory_rows": entry.get("rows"),
            "terminal_rows": recomputed["terminal_rows"],
            "pending_rows": recomputed["pending_rows"],
            "terminal_status_counts": recomputed["terminal_status_counts"],
            "return_code": summary.get("supervisor_exit_code"),
        })

    for shard_id in unexpected:
        matches = by_id[shard_id]
        shard_reports.append({"shard_id": shard_id, "status": "unexpected_artifact",
                              "artifact_count": len(matches), "pending_rows": 0})
        for index, (artifact_dir, _summary) in enumerate(matches):
            _copy_tree_without_symlinks(artifact_dir, staged / "shards" / f"unexpected-{shard_id}-{index}")

    for index, artifact_path in enumerate(unclassified_paths):
        target = staged / "shards" / f"unclassified-{index:03d}-{artifact_path.name}"
        if artifact_path.is_dir() and not artifact_path.is_symlink():
            _copy_tree_without_symlinks(artifact_path, target)
        elif artifact_path.is_symlink():
            target.write_text(f"Rejected symlink artifact: {artifact_path.name}\\n", encoding="utf-8")
        else:
            shutil.copy2(artifact_path, target, follow_symlinks=False)
        shard_reports.append({"status": "unclassified_artifact", "path": artifact_path.name,
                              "pending_rows": None})

    canonical_keys = {(r["index"], str(r["theorem"]), str(r["module"])) for r in planned_rows}
    covered &= canonical_keys
    pending_all = [row for row in planned_rows
                   if (row["index"], str(row["theorem"]), str(row["module"])) not in covered]
    (staged / "pending-inventory.tsv").write_text(
        HEADER + "\n" + "".join(
            f"{row['index']}\t{row['theorem']}\t{row['module']}\n" for row in pending_all
        ),
        encoding="utf-8",
    )
    complete = not missing and not duplicates and not unexpected and not issues and not pending_all
    report = {
        "schema": 1,
        "status": "complete" if complete else "incomplete",
        "complete": complete,
        "source_commit": plan.get("source_commit"),
        "inventory_rows": plan.get("inventory", {}).get("rows"),
        "planned_shards": count,
        "completed_terminal_rows": len(covered),
        "pending_rows": len(pending_all),
        "missing_shards": missing,
        "duplicate_shards": duplicates,
        "issues": issues,
        "shards": shard_reports,
    }
    (staged / "package-report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    destination.mkdir(parents=True, exist_ok=True)
    archive = destination / "nazrin-atomization-results.tar.gz"
    with tarfile.open(archive, "w:gz") as tar:
        tar.add(staged, arcname="nazrin-atomization-results")
    return {**report, "archive": str(archive)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--artifacts", type=Path, required=True,
                        help="directory containing downloaded per-shard artifact subdirectories")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = package(args.plan, args.artifacts, args.output)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))
    # Incomplete runs are still packaged successfully; CI should fail after artifact upload.
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
