#!/usr/bin/env python3
"""Deterministic stand-in for `Standalone/StructuredTraceV4.lean`.

The real exporter needs a built Lean/Mathlib tree, which unit tests must not
require.  This fixture speaks the same CLI and JSONL envelope:

    python3 fake_schema4_exporter.py MODULE THEOREM OUTPUT_PATH

It emits schema-4 step records plus one summary record.  A theorem name
containing ``Slow`` sleeps (to exercise the wall-clock timeout), ``Crash`` exits
without a summary (to exercise the synthetic-failure path), and ``Fail`` emits a
failure summary.  Everything else succeeds.

Environment:
    FAKE_EXPORTER_STEPS   number of step records (default 2)
    FAKE_EXPORTER_SLEEP   seconds to sleep for a ``Slow`` theorem (default 30)
    FAKE_EXPORTER_BYTES   approximate payload bytes per step (default 900)
"""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path


def payload(index: int, size: int) -> dict:
    graph = {
        "schema": 3,
        "theorem": None,
        "module": None,
        "goals": [{"id": "g0", "root": index}],
        "nodes": [{"node": node, "kind": "APP", "children": [node + 1]} for node in range(8)],
        "edges": [{"src": 0, "dst": 1, "kind": "child"}],
        "fvars": [],
        "constants": [{"name": "Nat.add", "id": "0" * 16}],
        "loci": [{"goal_id": "g0", "node": 1, "position": 0}],
        "coupled": {"groups": [], "goal_edges": []},
    }
    filler = "x" * max(0, size)
    return {"goal_state_graph": graph, "filler": filler}


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print("usage: fake_schema4_exporter.py MODULE THEOREM OUTPUT_PATH", file=sys.stderr)
        return 1
    module, theorem, output = argv
    run_id = os.environ.get("NAZRIN_STRUCT_RUN_ID", "fixture")
    envelope = int(os.environ.get("NAZRIN_STRUCT_STEP_SCHEMA", "3") or 3)
    steps = int(os.environ.get("FAKE_EXPORTER_STEPS", "2") or 0)
    size = int(os.environ.get("FAKE_EXPORTER_BYTES", "900") or 0)

    if "Slow" in theorem:
        time.sleep(float(os.environ.get("FAKE_EXPORTER_SLEEP", "30")))
    if "Crash" in theorem:
        print("boom: process died before writing a summary", file=sys.stderr)
        return 1

    failed = "Fail" in theorem
    bad_schema = os.environ.get("FAKE_EXPORTER_BAD_SCHEMA") == "1"
    emitted = 1 if failed else steps
    path = Path(output)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for index in range(emitted):
            record = {
                "schema": envelope,
                "schema_version": 3 if (bad_schema and index == 0) else 4,
                "record": "step",
                "run_id": run_id,
                "theorem": theorem,
                "module": module,
                "step": index,
                "goal_id": f"{theorem}:g0",
                "tactic": {"kind": "intro" if index == 0 else "exact"},
                "labels": [],
                "candidates": {
                    "free_variables": [],
                    "locus_candidates": [],
                },
                **payload(index, size),
            }
            record["goal_state_graph"]["theorem"] = theorem
            record["goal_state_graph"]["module"] = module
            handle.write(json.dumps(record, sort_keys=True) + "\n")
        summary = {
            "schema": envelope,
            "schema_version": 4,
            "record": "theorem",
            "run_id": run_id,
            "theorem": theorem,
            "module": module,
            "status": "failure" if failed else "success",
            "stage": "tactic_rejected" if failed else "ok",
            "message": "fixture failure" if failed else "",
            "steps": emitted,
            "label_rejections": 0,
            "unmodeled_steps": 0,
            "max_heartbeats": int(os.environ.get("NAZRIN_STRUCT_MAX_HEARTBEATS", "0") or 0),
            "max_steps": int(os.environ.get("NAZRIN_STRUCT_MAX_STEPS", "0") or 0),
            "schema4": {
                "premise_mode": "graph",
                "graph_steps": emitted,
                "premise_steps": emitted,
                "locus_steps": 0,
                "coupled_steps": 0,
                "graph_nodes_total": 8 * emitted,
            },
            "toolchain": "fixture",
            "elapsed_ms": 1,
        }
        handle.write(json.dumps(summary, sort_keys=True) + "\n")
    return 2 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))