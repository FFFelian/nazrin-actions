#!/usr/bin/env python3
"""Deterministically split a theorem-list TSV into contiguous balanced shards.

The input must have a header row and a ``theorem`` column.  Every other column
is preserved verbatim.  Contiguous ranges are used so that the original order
(including ``index``/``topo_rank``) remains meaningful within each shard.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


MAX_SHARDS = 20


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_table(path: Path) -> tuple[list[str], list[list[str]], bytes]:
    """Read and validate a UTF-8 TSV with a unique, non-empty theorem column."""
    raw = path.read_bytes()
    try:
        text = raw.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise ValueError(f"{path}: input is not valid UTF-8") from exc

    lines = text.splitlines()
    if not lines:
        raise ValueError(f"{path}: empty input")
    if any(line == "" for line in lines):
        raise ValueError(f"{path}: blank lines are not allowed")

    header = lines[0].split("\t")
    if any(cell == "" for cell in header):
        raise ValueError(f"{path}: header contains an empty column name")
    if len(set(header)) != len(header):
        raise ValueError(f"{path}: header contains duplicate column names")
    theorem_columns = [index for index, name in enumerate(header) if name == "theorem"]
    if len(theorem_columns) != 1:
        raise ValueError(f"{path}: header must contain exactly one 'theorem' column")

    rows: list[list[str]] = []
    seen: set[str] = set()
    for line_number, line in enumerate(lines[1:], start=2):
        fields = line.split("\t")
        if len(fields) != len(header):
            raise ValueError(
                f"{path}:{line_number}: expected {len(header)} columns, got {len(fields)}"
            )
        theorem = fields[theorem_columns[0]]
        if theorem == "":
            raise ValueError(f"{path}:{line_number}: empty theorem name")
        if theorem in seen:
            raise ValueError(f"{path}:{line_number}: duplicate theorem {theorem!r}")
        seen.add(theorem)
        rows.append(fields)

    if not rows:
        raise ValueError(f"{path}: no data rows")
    return header, rows, raw


def plan(input_path: Path, output: Path, shard_count: int) -> dict:
    """Write shard TSVs and a deterministic plan.json; return the plan object."""
    if not 1 <= shard_count <= MAX_SHARDS:
        raise ValueError(f"shard count must be between 1 and {MAX_SHARDS}")

    header, rows, raw = read_table(input_path)
    total = len(rows)
    if shard_count > total:
        raise ValueError(
            f"shard count {shard_count} exceeds the {total} input data rows; "
            "empty shards are not supported"
        )

    base, remainder = divmod(total, shard_count)
    width = max(2, len(str(shard_count - 1)))
    output.mkdir(parents=True, exist_ok=True)
    header_line = "\t".join(header) + "\n"

    shards: list[dict[str, object]] = []
    start = 0
    for shard_id in range(shard_count):
        size = base + (1 if shard_id < remainder else 0)
        stop = start + size
        name = f"shard-{shard_id:0{width}d}.tsv"
        payload = header_line + "".join("\t".join(row) + "\n" for row in rows[start:stop])
        encoded = payload.encode("utf-8")
        path = output / name
        path.write_bytes(encoded)
        shards.append({
            "id": shard_id,
            "file": name,
            "rows": size,
            "first_data_row": start,
            "last_data_row": stop - 1,
            "sha256": _sha256(encoded),
        })
        start = stop
    assert start == total

    result = {
        "schema": 1,
        "algorithm": "contiguous balanced partition; first remainder shards get one extra row",
        "input": {
            "name": input_path.name,
            "sha256": _sha256(raw),
            "rows": total,
            "columns": header,
            "theorem_column": header.index("theorem"),
        },
        "shard_count": shard_count,
        "total_rows": total,
        "shards": shards,
    }
    (output / "plan.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="theorem-list TSV")
    parser.add_argument("--output", type=Path, required=True, help="plan output directory")
    parser.add_argument("--shards", type=int, default=10, help="number of shards (1-20)")
    args = parser.parse_args()

    try:
        result = plan(args.input, args.output, args.shards)
    except (OSError, ValueError) as exc:
        print(f"plan_paper_shards: {exc}", file=sys.stderr)
        return 2

    print(json.dumps({
        "total_rows": result["total_rows"],
        "shard_count": result["shard_count"],
        "sizes": [shard["rows"] for shard in result["shards"]],
    }, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
