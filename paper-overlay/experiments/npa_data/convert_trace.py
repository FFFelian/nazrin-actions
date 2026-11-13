#!/usr/bin/env python3
"""Convert PaperTraceExport output into the NPA training JSONL contract.

Inputs:
  steps.jsonl   one atomization step per row, containing ``goal_graph`` and
                ``tactic`` (or a sibling ``graphs.jsonl`` keyed by goal_id)
  graphs.jsonl  optional goal_id -> ExprGraph table

Output records follow ``experiments/npa_training/dataset.py``: a graph over
uppercase ``NodeKind`` names, pointer/categorical tactic parameters, candidate
blocks, children, and a theorem-hash split.  Parameters that the current
schema cannot represent are omitted rather than fabricated.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

try:  # package import (python -m ...)
    from experiments.paper_aligned_npa import (
        CATEGORY_VALUES,
        TACTIC_PARAMETERS,
        TacticKind,
        tactic_kind_from_name,
    )
    from experiments.npa_training.dataset import SPLIT_NAMES, split_for_theorem
except ModuleNotFoundError:  # direct script execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from experiments.paper_aligned_npa import (  # type: ignore
        CATEGORY_VALUES,
        TACTIC_PARAMETERS,
        TacticKind,
        tactic_kind_from_name,
    )
    from experiments.npa_training.dataset import SPLIT_NAMES, split_for_theorem  # type: ignore


NODE_KIND_MAP = {
    "const": "CONST",
    "app": "APP",
    "bvar": "BVAR",
    "fvar": "FVAR",
    "sort": "SORT",
    "lit": "LITERAL",
    "mvar": "MVAR",
    "forallE": "FORALL",
    "lam": "LAMBDA",
    "letE": "LET",
    "proj": "PROJECTION",
}



def normalize_position(position: str) -> str:
    """The NPA loader requires non-empty strings; encode the v1 root `""` as `root`."""

    return "root" if position == "" else position


class ConversionError(ValueError):
    """Raised when a trace record cannot be converted safely."""


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            try:
                value = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ConversionError(f"{path}:{line_number}: invalid JSON: {exc}") from exc
            if not isinstance(value, dict):
                raise ConversionError(f"{path}:{line_number}: expected a JSON object")
            records.append(value)
    return records


def _features(node: Mapping[str, Any], root: int, max_depth: int, out_degree: Mapping[int, int]) -> list[float]:
    node_id = int(node["id"])
    depth = int(node.get("depth", 0))
    max_children = max(out_degree.values(), default=0)
    return [
        depth / max_depth if max_depth > 0 else 0.0,
        1.0 if node_id == root else 0.0,
        out_degree.get(node_id, 0) / max_children if max_children > 0 else 0.0,
    ]


def convert_graph(graph: Mapping[str, Any]) -> dict[str, Any]:
    """Convert one v1 ExprGraph to the ``npa_training.dataset`` graph schema."""

    if not isinstance(graph, Mapping):
        raise ConversionError("graph must be an object")
    if graph.get("schema") != 1:
        raise ConversionError(f"unsupported graph schema {graph.get('schema')!r}")
    raw_nodes = graph.get("nodes")
    if not isinstance(raw_nodes, list) or not raw_nodes:
        raise ConversionError("graph.nodes must be a non-empty list")
    root = graph.get("root")
    if not isinstance(root, int) or isinstance(root, bool) or not 0 <= root < len(raw_nodes):
        raise ConversionError(f"graph.root {root!r} outside node range")

    out_degree: dict[int, int] = {}
    for edge in graph.get("edges", []):
        source = edge.get("src", edge.get("source"))
        if isinstance(source, int):
            out_degree[source] = out_degree.get(source, 0) + 1
    max_depth = max(int(node.get("depth", 0)) for node in raw_nodes)

    nodes: list[dict[str, Any]] = []
    for index, node in enumerate(raw_nodes):
        if not isinstance(node, Mapping):
            raise ConversionError(f"graph.nodes[{index}] must be an object")
        if node.get("id") != index:
            raise ConversionError(f"graph.nodes[{index}].id must equal {index}")
        kind = NODE_KIND_MAP.get(str(node.get("kind")))
        if kind is None:
            raise ConversionError(f"unknown v1 node kind {node.get('kind')!r}")
        converted: dict[str, Any] = {
            "id": index,
            "kind": kind,
            "features": _features(node, root, max_depth, out_degree),
        }
        if kind == "CONST":
            name = node.get("const")
            if not isinstance(name, str) or not name:
                raise ConversionError(f"const node {index} lacks a name")
            converted["constant"] = name
        nodes.append(converted)

    edges: list[dict[str, Any]] = []
    for edge_index, edge in enumerate(graph.get("edges", [])):
        if not isinstance(edge, Mapping):
            raise ConversionError(f"graph.edges[{edge_index}] must be an object")
        source = edge.get("src", edge.get("source"))
        target = edge.get("dst", edge.get("target"))
        edge_type = edge.get("type")
        if not isinstance(source, int) or not isinstance(target, int):
            raise ConversionError(f"edge {edge_index} endpoints must be integers")
        if not 0 <= source < len(nodes) or not 0 <= target < len(nodes):
            raise ConversionError(f"edge {edge_index} endpoint outside graph")
        if not isinstance(edge_type, str) or not edge_type:
            raise ConversionError(f"edge {edge_index} needs a string type")
        edges.append({"source": source, "target": target, "type": edge_type})

    constants: list[str] = []
    for entry in graph.get("constants", []):
        name = entry.get("name") if isinstance(entry, Mapping) else entry
        if not isinstance(name, str) or not name:
            raise ConversionError("graph.constants entries must have names")
        if name not in constants:
            constants.append(name)

    fvars: list[dict[str, Any]] = []
    for entry in graph.get("fvars", []):
        if not isinstance(entry, Mapping):
            raise ConversionError("graph.fvars entries must be objects")
        name = entry.get("name")
        node = entry.get("node")
        if not isinstance(name, str) or not name:
            raise ConversionError("fvar name must be a non-empty string")
        if not isinstance(node, int) or not 0 <= node < len(nodes):
            raise ConversionError(f"fvar {name!r} node outside graph")
        item = {"name": name, "node": node}
        if "type_node" in entry:
            item["type_node"] = entry["type_node"]
        fvars.append(item)

    loci: list[dict[str, Any]] = []
    for entry in graph.get("loci", []):
        if not isinstance(entry, Mapping):
            raise ConversionError("graph.loci entries must be objects")
        position = entry.get("position")
        node = entry.get("node")
        if not isinstance(position, str) or not isinstance(node, int):
            raise ConversionError("locus needs string position and integer node")
        if not 0 <= node < len(nodes):
            raise ConversionError(f"locus {position!r} node outside graph")
        loci.append({"position": normalize_position(position), "node": node})

    relations = sorted({edge["type"] for edge in edges})
    return {
        "schema": 1,
        "root": root,
        "nodes": nodes,
        "edges": edges,
        "relations": relations,
        "constants": [{"name": name} for name in constants],
        "fvars": fvars,
        "loci": loci,
    }


def _tactic_premise_label(tactic: Mapping[str, Any]) -> str | None:
    """Return the tactic's premise label if it is a non-empty string."""

    raw = tactic.get("parameters", {})
    if not isinstance(raw, Mapping):
        return None
    value = raw.get("premise")
    if isinstance(value, str) and value:
        return value
    return None


def _filter_parameters(
    tactic: Mapping[str, Any],
    constants: Sequence[str],
    fvar_names: Sequence[str],
    locus_positions: Sequence[str],
) -> dict[str, Any]:
    name = tactic.get("kind")
    if not isinstance(name, str) or not name:
        raise ConversionError("tactic.kind must be a non-empty string")
    try:
        kind = tactic_kind_from_name(name)
    except ValueError as exc:
        raise ConversionError(str(exc)) from exc
    raw = tactic.get("parameters", {})
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise ConversionError("tactic.parameters must be an object")
    if kind == TacticKind.OTHER:
        return {}
    allowed = TACTIC_PARAMETERS[kind]
    # A premise labels a theorem applied by the tactic; it is not required to
    # occur in the goal graph, so the current tactic's own label is also a
    # legal premise value.
    premise_label = _tactic_premise_label(tactic)
    allowed_premises = set(constants)
    if premise_label is not None:
        allowed_premises.add(premise_label)
    out: dict[str, Any] = {}
    for parameter in allowed:
        if parameter not in raw:
            continue
        value = raw[parameter]
        if value is None:
            continue
        if parameter == "premise":
            if not isinstance(value, str) or value not in allowed_premises:
                continue
        elif parameter == "free_variable":
            if not isinstance(value, str) or value not in set(fvar_names):
                continue
        elif parameter == "locus":
            value = normalize_position(value) if isinstance(value, str) else value
            if not isinstance(value, str) or value not in set(locus_positions):
                continue
        elif parameter in CATEGORY_VALUES:
            if not isinstance(value, str) or value not in CATEGORY_VALUES[parameter]:
                continue
        else:  # pragma: no cover - schema change guard
            continue
        out[parameter] = value
    return out


def convert_record(
    step: Mapping[str, Any],
    graph: Mapping[str, Any],
    *,
    split: str | None = None,
) -> dict[str, Any]:
    """Convert one step row and its graph into an NPA record."""

    theorem = step.get("theorem")
    if not isinstance(theorem, str) or not theorem:
        raise ConversionError("step.theorem must be a non-empty string")
    goal_id = step.get("goal_id")
    if not isinstance(goal_id, str) or not goal_id:
        raise ConversionError("step.goal_id must be a non-empty string")
    index = step.get("step")
    if not isinstance(index, int) or isinstance(index, bool) or index < 0:
        raise ConversionError("step.step must be a non-negative integer")
    tactic = step.get("tactic")
    if not isinstance(tactic, Mapping):
        raise ConversionError("step.tactic must be an object")

    converted_graph = convert_graph(graph)
    constants = [entry["name"] for entry in converted_graph["constants"]]
    fvar_names = [entry["name"] for entry in converted_graph["fvars"]]
    all_locus_positions = [entry["position"] for entry in converted_graph["loci"]]
    # A pointer head scores node indices, and condensation can make several
    # positions point at one node.  Keep one candidate per distinct node;
    # labels may still use any position because the loader resolves positions
    # through the full graph.loci table.
    locus_candidates: list[str] = []
    seen_locus_nodes: set[int] = set()
    for entry in converted_graph["loci"]:
        if entry["node"] not in seen_locus_nodes:
            seen_locus_nodes.add(entry["node"])
            locus_candidates.append(entry["position"])
    parameters = _filter_parameters(tactic, constants, fvar_names, all_locus_positions)

    # The applied theorem usually does not occur in the goal expression.  Keep
    # its label as a premise candidate without inventing a graph node or a
    # graph constant entry.
    premise_candidates = list(constants)
    premise_label = _tactic_premise_label(tactic)
    if premise_label is not None and premise_label not in constants:
        premise_candidates.append(premise_label)

    resolved_split = split or split_for_theorem(theorem)
    if resolved_split not in SPLIT_NAMES:
        raise ConversionError(f"unknown split {resolved_split!r}")

    children = step.get("children", [])
    if not isinstance(children, list) or any(not isinstance(child, str) or not child for child in children):
        raise ConversionError("step.children must be a list of goal ids")

    return {
        "theorem": theorem,
        "step": index,
        "goal_id": goal_id,
        "split": resolved_split,
        "graph": converted_graph,
        "tactic": {"kind": tactic["kind"], "parameters": parameters},
        "candidates": {
            "premise": {"items": premise_candidates, "mask": [True] * len(premise_candidates)},
            "free_variable": {"items": fvar_names, "mask": [True] * len(fvar_names)},
            "locus": {"items": locus_candidates, "mask": [True] * len(locus_candidates)},
        },
        "children": children,
    }


def load_graphs(path: Path | None) -> dict[str, dict[str, Any]]:
    if path is None or not path.is_file():
        return {}
    graphs: dict[str, dict[str, Any]] = {}
    for row in _read_jsonl(path):
        goal_id = row.get("goal_id")
        graph = row.get("graph")
        if isinstance(goal_id, str) and isinstance(graph, Mapping):
            graphs[goal_id] = dict(graph)
    return graphs


def convert_files(steps_path: Path, graphs_path: Path | None = None) -> list[dict[str, Any]]:
    """Read steps (+ optional graphs) and return converted NPA records."""

    steps = _read_jsonl(steps_path)
    graph_table = load_graphs(graphs_path)
    records: list[dict[str, Any]] = []
    seen: set[tuple[str, str]] = set()
    for row in steps:
        goal_id = row.get("goal_id")
        graph = row.get("goal_graph")
        if not isinstance(graph, Mapping):
            graph = graph_table.get(goal_id) if isinstance(goal_id, str) else None
        if not isinstance(graph, Mapping):
            raise ConversionError(f"no graph for step {row.get('theorem')!r}/{goal_id!r}")
        record = convert_record(row, graph)
        key = (record["theorem"], record["goal_id"])
        if key in seen:
            raise ConversionError(f"duplicate theorem/goal_id pair {key!r}")
        seen.add(key)
        records.append(record)
    return records


def write_dataset(records: Iterable[Mapping[str, Any]], output_dir: Path) -> dict[str, int]:
    output_dir.mkdir(parents=True, exist_ok=True)
    buckets: dict[str, list[dict[str, Any]]] = {name: [] for name in SPLIT_NAMES}
    all_records: list[dict[str, Any]] = []
    for record in records:
        split = record["split"]
        buckets[split].append(dict(record))
        all_records.append(dict(record))
    for split, rows in buckets.items():
        with (output_dir / f"{split}.jsonl").open("w", encoding="utf-8") as handle:
            for row in rows:
                handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n")
    with (output_dir / "all.jsonl").open("w", encoding="utf-8") as handle:
        for row in all_records:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n")
    summary = {name: len(rows) for name, rows in buckets.items()}
    summary["all"] = len(all_records)
    (output_dir / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=Path, required=True, help="PaperTraceExport steps.jsonl")
    parser.add_argument("--graphs", type=Path, default=None, help="optional graphs.jsonl")
    parser.add_argument("--output-dir", type=Path, required=True, help="directory for NPA JSONL files")
    args = parser.parse_args(argv)
    records = convert_files(args.steps, args.graphs)
    summary = write_dataset(records, args.output_dir)
    print(f"converted {len(records)} step(s) -> {args.output_dir} ({summary})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
