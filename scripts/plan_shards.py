#!/usr/bin/env python3
"""Validate an inventory and assign each theorem to one deterministic shard."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

HEADER = "index\ttheorem\tmodule"


def parse_inventory(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    indexes: set[int] = set()
    names: set[tuple[str, str]] = set()
    with path.open(encoding="utf-8", newline="") as handle:
        if handle.readline().rstrip("\r\n") != HEADER:
            raise ValueError(f"inventory must start with {HEADER!r}")
        for line_number, line in enumerate(handle, 2):
            fields = line.rstrip("\r\n").split("\t")
            if len(fields) != 3 or not all(fields):
                raise ValueError(f"malformed inventory row at line {line_number}")
            raw_index, theorem, module = fields
            if not raw_index.isdecimal():
                raise ValueError(f"invalid inventory index at line {line_number}")
            index = int(raw_index)
            key = (module, theorem)
            if index in indexes:
                raise ValueError(f"duplicate inventory index {index}")
            if key in names:
                raise ValueError(f"duplicate theorem {theorem!r} in module {module!r}")
            indexes.add(index)
            names.add(key)
            rows.append({"index": index, "theorem": theorem, "module": module})
    return rows


def stable_shard(module: str, theorem: str, shard_count: int) -> int:
    key = f"{module}\0{theorem}".encode("utf-8")
    value = int.from_bytes(hashlib.sha256(key).digest()[:8], "big")
    return value % shard_count


def plan(inventory: Path, output: Path, shard_count: int, source_commit: str) -> dict:
    if not 1 <= shard_count <= 128:
        raise ValueError("shard count must be between 1 and 128")
    if source_commit and not re.fullmatch(r"[0-9a-fA-F]{40}", source_commit):
        raise ValueError("source commit must be a full 40-character Git SHA")

    rows = parse_inventory(inventory)
    output.mkdir(parents=True, exist_ok=True)
    buckets: list[list[dict[str, object]]] = [[] for _ in range(shard_count)]
    for row in rows:
        shard = stable_shard(str(row["module"]), str(row["theorem"]), shard_count)
        buckets[shard].append(row)

    inventory_bytes = inventory.read_bytes()
    inventory_sha = hashlib.sha256(inventory_bytes).hexdigest()
    canonical_path = output / "canonical-inventory.tsv"
    canonical_path.write_bytes(inventory_bytes)
    shards = []
    for shard_id, bucket in enumerate(buckets):
        name = f"shard-{shard_id:02d}.tsv"
        path = output / name
        with path.open("w", encoding="utf-8", newline="") as handle:
            handle.write(HEADER + "\n")
            for row in bucket:
                handle.write(f"{row['index']}\t{row['theorem']}\t{row['module']}\n")
        shards.append({
            "id": shard_id,
            "inventory": name,
            "rows": len(bucket),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        })

    result = {
        "schema": 1,
        "algorithm": "sha256(module + NUL + theorem), first 64 bits modulo shard_count",
        "source_commit": source_commit.lower(),
        "inventory": {"rows": len(rows), "sha256": inventory_sha},
        "shard_count": shard_count,
        "shards": shards,
    }
    (output / "plan.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--shards", type=int, default=10)
    parser.add_argument("--source-commit", default="")
    args = parser.parse_args()
    result = plan(args.inventory, args.output, args.shards, args.source_commit)
    print(json.dumps({"rows": result["inventory"]["rows"], "shard_count": result["shard_count"], "sizes": [s["rows"] for s in result["shards"]]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
