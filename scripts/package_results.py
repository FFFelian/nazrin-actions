#!/usr/bin/env python3
"""Verify and combine downloaded shard result archives."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import tarfile
from collections import Counter, defaultdict

HEADER = "index\ttheorem\tmodule"
TERMINAL = {"success", "failure", "timeout", "crash", "invalid_symbol"}


def safe_extract(archive: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive, "r:gz") as tar:
        members = tar.getmembers()
        for member in members:
            path = PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts or not (member.isfile() or member.isdir()):
                raise ValueError(f"unsafe archive member {member.name!r}")
            target = destination.joinpath(*path.parts)
            if not target.resolve().is_relative_to(destination.resolve()):
                raise ValueError(f"archive member escapes extraction root: {member.name!r}")
        for member in members:
            target = destination.joinpath(*PurePosixPath(member.name).parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            source = tar.extractfile(member)
            if source is None:
                raise ValueError(f"cannot read archive member {member.name!r}")
            with source, target.open("wb") as output:
                while chunk := source.read(1024 * 1024):
                    output.write(chunk)


def read_rows(path: Path) -> list[dict]:
    rows = []
    with path.open(encoding="utf-8", newline="") as handle:
        if handle.readline().rstrip("\r\n") != HEADER:
            raise ValueError(f"invalid inventory header: {path}")
        for line_number, line in enumerate(handle, 2):
            fields = line.rstrip("\r\n").split("\t")
            if len(fields) != 3 or not fields[0].isdecimal() or not fields[1] or not fields[2]:
                raise ValueError(f"invalid inventory row in {path}:{line_number}")
            rows.append({"index": int(fields[0]), "theorem": fields[1], "module": fields[2]})
    return rows


def load_records(root: Path, rows: list[dict]) -> tuple[dict[tuple[str, str], dict], list[str]]:
    expected = {(str(r["module"]), str(r["theorem"])) for r in rows}
    records: dict[tuple[str, str], dict] = {}
    errors: list[str] = []
    for ledger in root.rglob(".bounded-results.jsonl"):
        with ledger.open(encoding="utf-8", errors="replace") as handle:
            for line_number, line in enumerate(handle, 1):
                try:
                    item = json.loads(line)
                    status = item.get("status")
                    if status not in TERMINAL:
                        continue
                    key = (item["module"], item["theorem"])
                    if key not in expected:
                        errors.append(f"unexpected ledger theorem {key[1]} in {ledger}")
                        continue
                    if key in records:
                        errors.append(f"duplicate terminal theorem {key[1]}")
                    records[key] = item
                except (json.JSONDecodeError, KeyError, TypeError, AttributeError):
                    errors.append(f"invalid ledger row {ledger}:{line_number}")
    return records, errors


def package(plan_path: Path, plan_dir: Path, artifacts_dir: Path, output_dir: Path) -> dict:
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    shard_count = int(plan["shard_count"])
    output_dir.mkdir(parents=True, exist_ok=True)
    extracted = output_dir / "shards"
    if extracted.exists():
        raise FileExistsError(f"refusing to overwrite existing extraction directory: {extracted}")
    extracted.mkdir()

    available: set[int] = set()
    archive_errors: list[str] = []
    for archive in sorted(artifacts_dir.rglob("shard-*.tar.gz")):
        stem = archive.name.removesuffix(".tar.gz")
        try:
            shard_id = int(stem.split("-")[1])
        except (IndexError, ValueError):
            continue
        if not 0 <= shard_id < shard_count:
            archive_errors.append(f"unexpected shard ID {shard_id} in {archive}")
            continue
        if shard_id in available:
            archive_errors.append(f"duplicate archive for shard {shard_id}")
            continue
        target = extracted / f"shard-{shard_id:02d}"
        try:
            safe_extract(archive, target)
            available.add(shard_id)
        except (OSError, ValueError, tarfile.TarError) as exc:
            archive_errors.append(f"invalid archive {archive}: {exc}")

    all_rows: list[dict] = []
    missing_plan_shards: list[int] = []
    shard_summaries: list[dict] = []
    for shard in plan["shards"]:
        shard_id = int(shard["id"])
        inventory_path = plan_dir / shard["inventory"]
        rows = read_rows(inventory_path)
        inventory_sha = hashlib.sha256(inventory_path.read_bytes()).hexdigest()
        if inventory_sha != shard.get("sha256"):
            missing_plan_shards.append(shard_id)
            shard_summaries.append({"id": shard_id, "status": "plan_inventory_hash_mismatch", "input": len(rows), "terminal": 0, "deferred": len(rows)})
            all_rows.extend(rows)
            continue
        all_rows.extend(rows)
        root = extracted / f"shard-{shard_id:02d}"
        if shard_id not in available:
            missing_plan_shards.append(shard_id)
            shard_summaries.append({"id": shard_id, "status": "missing_artifact", "input": len(rows), "terminal": 0, "deferred": len(rows)})
            continue
        manifest_path = root / "shard-manifest.json"
        if not manifest_path.is_file():
            shard_summaries.append({"id": shard_id, "status": "invalid_artifact", "input": len(rows), "terminal": 0, "deferred": len(rows)})
            missing_plan_shards.append(shard_id)
            continue
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        identity_errors = []
        if int(manifest.get("shard_id", -1)) != shard_id:
            identity_errors.append("shard ID does not match artifact name")
        if int(manifest.get("input_rows", -1)) != len(rows):
            identity_errors.append("manifest input row count does not match plan")
        if manifest.get("inventory_sha256") != shard.get("sha256"):
            identity_errors.append("manifest inventory hash does not match plan")
        deferred_path = root / "deferred.tsv"
        deferred_rows = read_rows(deferred_path) if deferred_path.is_file() else rows
        if any((str(r["module"]), str(r["theorem"])) not in {(str(x["module"]), str(x["theorem"])) for x in rows} for r in deferred_rows):
            identity_errors.append("deferred inventory contains rows outside this shard")
        deferred_count = len(deferred_rows)
        if identity_errors:
            missing_plan_shards.append(shard_id)
        shard_summaries.append({"id": shard_id, "status": "invalid_artifact" if identity_errors else manifest.get("status", "unknown"), "identity_errors": identity_errors, "input": len(rows), "terminal": int(manifest.get("terminal_rows", 0)), "deferred": deferred_count, "reported_counts": manifest.get("terminal_status_counts", {})})

    records, ledger_errors = load_records(extracted, all_rows)
    expected = {(str(r["module"]), str(r["theorem"])) for r in all_rows}
    deferred = [r for r in all_rows if (str(r["module"]), str(r["theorem"])) not in records]
    counts = Counter(item.get("status", "unknown") for item in records.values())
    coverage_ok = len(expected) == len(all_rows) and not ledger_errors and not missing_plan_shards and not deferred
    report = {
        "schema": 1,
        "complete": coverage_ok,
        "inventory_rows": len(all_rows),
        "unique_inventory_theorems": len(expected),
        "terminal_rows": len(records),
        "deferred_rows": len(deferred),
        "terminal_status_counts": dict(sorted(counts.items())),
        "missing_shard_ids": missing_plan_shards,
        "ledger_errors": ledger_errors,
        "shards": shard_summaries,
    }
    (output_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    with (output_dir / "deferred.tsv").open("w", encoding="utf-8", newline="") as handle:
        handle.write(HEADER + "\n")
        for row in deferred:
            handle.write(f"{row['index']}\t{row['theorem']}\t{row['module']}\n")

    summary = [
        "# Nazrin Atomization Package",
        "",
        f"- Complete: **{coverage_ok}**",
        f"- Inventory: {len(all_rows)} rows; {len(expected)} unique theorem/module pairs",
        f"- Terminal: {len(records)}; deferred: {len(deferred)}",
        f"- Missing/invalid shards: {missing_plan_shards}",
        f"- Ledger errors: {len(ledger_errors)}",
        f"- Statuses: `{json.dumps(dict(sorted(counts.items())), sort_keys=True)}`",
        "",
        "A terminal outcome includes success, failure, timeout, and crash; it is not a success rate.",
    ]
    (output_dir / "summary.md").write_text("\n".join(summary) + "\n", encoding="utf-8")

    import tarfile
    bundle_path = output_dir / "atomization-results.tar.gz"
    with tarfile.open(bundle_path, "w:gz", compresslevel=1) as tar:
        for item in sorted(extracted.iterdir()):
            tar.add(item, arcname=f"shards/{item.name}")
        tar.add(output_dir / "report.json", arcname="report.json")
        tar.add(output_dir / "summary.md", arcname="summary.md")
        tar.add(output_dir / "deferred.tsv", arcname="deferred.tsv")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--plan-dir", type=Path, required=True)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = package(args.plan, args.plan_dir, args.artifacts, args.output)
    print(json.dumps(result, indent=2))
    return 0 if result["complete"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
