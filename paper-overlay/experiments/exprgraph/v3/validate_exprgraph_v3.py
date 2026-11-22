#!/usr/bin/env python3
"""Validate schema-3 (goal-edge / global-constant) ExprGraph JSONL.

Only the Python standard library is used.  The field contract is documented in
``experiments/exprgraph/v3/schema-v3.md``; the samples are produced by
``experiments/exprgraph/v3/ExprGraphV3Samples.lean``.

Usage:
    python3 validate_exprgraph_v3.py FILE.jsonl [FILE.jsonl ...]
    python3 validate_exprgraph_v3.py --stats FILE.jsonl
    python3 validate_exprgraph_v3.py --alpha FILE.jsonl CASE_A CASE_B

Each line is either a raw graph object, or a case wrapper produced by the
sampler::

    {"case": "...", "result": "ok",   "graph": {...}, "canonical": "..."}
    {"case": "...", "result": "none", "graph": null,
     "warnings": ["..."], "note": "..."}

A ``graph: null`` line is accepted only when the case declares ``result:
none`` *and* carries at least one warning: the exporter is required to explain
why the graph is missing, never to drop it silently.

Exit codes: 0 = all inputs valid (or the alpha pair matches), 1 = invalid
input (or the alpha pair differs), 2 = usage or I/O error.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import deque
from pathlib import Path
from typing import Any, Deque, Dict, Iterable, List, Mapping, Sequence, Set, Tuple

SCHEMA_VERSION = 3


def global_constant_id(name: str) -> str:
    """Mirror of `ExprGraphV3.globalConstantId` (FNV-1a 64, 16 hex digits).

    This is a cross-graph identity, not a security hash.  Keeping the Python
    implementation independent is useful: every sample checks that Lean and
    this validator agree byte-for-byte on the ids.
    """
    value = 14695981039346656037
    for byte in name.encode("utf-8"):
        value ^= byte
        value = (value * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return f"{value:016x}"


NODE_KINDS = {
    "app",
    "const",
    "fvar",
    "bvar",
    "sort",
    "lit",
    "lam",
    "forallE",
    "letE",
    "proj",
    "mvar",
}

# Fixed relation order; also the canonical child traversal order.
EDGE_RANK: Dict[str, int] = {
    "app_fn": 0,
    "app_arg": 1,
    "binder_type": 2,
    "binder_body": 3,
    "let_type": 4,
    "let_value": 5,
    "let_body": 6,
    "proj_struct": 7,
    "fvar_type": 8,
    "fvar_value": 9,
}
EDGE_TYPES = set(EDGE_RANK)

# parent kind -> required (edge type, SubExpr.Pos coordinate) children
STRUCTURAL_CHILDREN: Dict[str, Tuple[Tuple[str, int], ...]] = {
    "app": (("app_fn", 0), ("app_arg", 1)),
    "lam": (("binder_type", 0), ("binder_body", 1)),
    "forallE": (("binder_type", 0), ("binder_body", 1)),
    "letE": (("let_type", 0), ("let_value", 1), ("let_body", 2)),
    "proj": (("proj_struct", 0),),
}

# Atom kinds carry no outgoing edges at all (fvar additionally has the
# metadata edges `fvar_type` / `fvar_value`).
LEAF_KINDS = {"const", "sort", "lit", "bvar", "mvar"}

# Kinds whose node is a unique expression occurrence, so its `position`/`depth`
# are read off the parent.  Condensed atoms (const/sort/lit/fvar/mvar) keep the
# position of their *first* occurrence, which may be in another goal or in a
# metadata subgraph, so they are exempt.
UNIQUE_OCCURRENCE_KINDS = {"app", "lam", "forallE", "letE", "proj", "bvar"}


class ValidationError(ValueError):
    """Raised when a case or a graph violates the schema-3 contract."""


# --------------------------------------------------------------------------- #
# Small typed accessors
# --------------------------------------------------------------------------- #


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def _require_int(value: Any, message: str, *, minimum: int | None = None) -> int:
    _require(_is_int(value), f"{message}: expected int, got {type(value).__name__}")
    if minimum is not None:
        _require(value >= minimum, f"{message}: expected >= {minimum}, got {value}")
    return value


def _require_str(value: Any, message: str, *, allow_empty: bool = False) -> str:
    _require(
        isinstance(value, str), f"{message}: expected string, got {type(value).__name__}"
    )
    if not allow_empty:
        _require(value != "", f"{message}: must not be empty")
    return value


def _get_list(obj: Mapping[str, Any], key: str, context: str = "graph") -> List[Any]:
    _require(key in obj, f"{context}: missing field {key!r}")
    value = obj[key]
    _require(isinstance(value, list), f"{context}: {key} must be an array")
    return value


def parse_position(position: Any, *, context: str) -> Tuple[int, ...]:
    """Parse dot-separated `SubExpr.Pos`; the root is the empty string."""
    _require_str(position, context, allow_empty=True)
    if position == "":
        return ()
    parts = position.split(".")
    for part in parts:
        _require(
            part.isdigit(), f"{context}: malformed coordinate {part!r} in {position!r}"
        )
    coords = tuple(int(part) for part in parts)
    for coord in coords:
        _require(coord <= 3, f"{context}: coordinate {coord} exceeds SubExpr.Pos.maxChildren")
    return coords


def child_position(parent: str, coordinate: int) -> str:
    return str(coordinate) if parent == "" else f"{parent}.{coordinate}"


# --------------------------------------------------------------------------- #
# Graph validation
# --------------------------------------------------------------------------- #


def validate_graph(graph: Any, *, context: str = "graph") -> None:
    """Validate one decoded schema-3 graph.  Raises ValidationError."""
    _require(isinstance(graph, dict), f"{context}: graph must be a JSON object")
    _require(
        _is_int(graph.get("schema")) and graph["schema"] == SCHEMA_VERSION,
        f"{context}: schema must be {SCHEMA_VERSION}, got {graph.get('schema')!r}",
    )
    _require_str(graph.get("theorem"), f"{context}: theorem", allow_empty=True)
    if "module" in graph:
        _require_str(graph["module"], f"{context}: module", allow_empty=True)
    if "constant" in graph:
        _require_str(graph["constant"], f"{context}: constant")

    nodes = _get_list(graph, "nodes", context)
    _require(len(nodes) > 0, f"{context}: graph has no nodes")
    node_count = len(nodes)

    # ---- goals ----------------------------------------------------------
    goals = _get_list(graph, "goals", context)
    _require(
        len(goals) > 0,
        f"{context}: goals must not be empty "
        "(an empty goal list is a bad input, not an empty proof state)",
    )
    goal_ids: List[str] = []
    goal_index: Dict[str, int] = {}
    goal_roots: List[int] = []
    fvar_counts: List[int] = []
    for index, goal in enumerate(goals):
        label = f"{context}: goals[{index}]"
        _require(isinstance(goal, dict), f"{label} is not an object")
        goal_id = _require_str(goal.get("goal_id"), f"{label}.goal_id")
        _require(
            goal_id not in goal_index,
            f"{label}: duplicate goal id {goal_id!r}",
        )
        root = _require_int(goal.get("root"), f"{label}.root", minimum=0)
        _require(root < node_count, f"{label}: root {root} is outside the node array")
        fvar_count = _require_int(goal.get("fvar_count"), f"{label}.fvar_count", minimum=0)
        goal_ids.append(goal_id)
        goal_index[goal_id] = index
        goal_roots.append(root)
        fvar_counts.append(fvar_count)

    # ---- nodes ----------------------------------------------------------
    positions: List[str] = []
    const_nodes: Dict[str, int] = {}
    fvar_nodes: Dict[int, int] = {}
    mvar_nodes: Dict[int, int] = {}
    for index, node in enumerate(nodes):
        label = f"{context}: nodes[{index}]"
        _require(isinstance(node, dict), f"{label} is not an object")
        node_id = _require_int(node.get("id"), f"{label}.id", minimum=0)
        _require(
            node_id == index,
            f"{label}.id must equal its array index (ids are contiguous), got {node_id}",
        )
        kind = _require_str(node.get("kind"), f"{label}.kind")
        _require(kind in NODE_KINDS, f"{label}: unknown kind {kind!r}")
        position = _require_str(node.get("position"), f"{label}.position", allow_empty=True)
        parse_position(position, context=f"{label}.position")
        positions.append(position)
        _require_int(node.get("depth"), f"{label}.depth", minimum=0)
        owner = _require_str(node.get("goal"), f"{label}.goal", allow_empty=True)
        _require(
            owner == "" or owner in goal_index,
            f"{label}.goal {owner!r} is not a declared goal id",
        )
        if kind == "const":
            name = _require_str(node.get("const"), f"{label}.const")
            levels = node.get("level")
            _require(
                isinstance(levels, list) and all(isinstance(level, str) for level in levels),
                f"{label}.level must be an array of strings",
            )
            gid = _require_str(node.get("global_id"), f"{label}.global_id")
            _require(
                gid == global_constant_id(name),
                f"{label}.global_id {gid!r} does not equal the stable id "
                f"{global_constant_id(name)!r} for {name!r}",
            )
            _require(
                name not in const_nodes,
                f"{label}: constant {name!r} has two const nodes "
                f"({const_nodes.get(name)} and {index}); condensation violated",
            )
            const_nodes[name] = index
        elif kind == "fvar":
            fvar_index = _require_int(node.get("fvar"), f"{label}.fvar", minimum=0)
            _require(
                fvar_index not in fvar_nodes,
                f"{label}: fvar index {fvar_index} uses two nodes",
            )
            fvar_nodes[fvar_index] = index
        elif kind == "mvar":
            mvar_index = _require_int(node.get("mvar"), f"{label}.mvar", minimum=0)
            _require(
                mvar_index not in mvar_nodes,
                f"{label}: mvar index {mvar_index} uses two nodes",
            )
            mvar_nodes[mvar_index] = index
        elif kind == "sort":
            _require_str(node.get("sort"), f"{label}.sort")
        elif kind == "lit":
            _require_str(node.get("lit"), f"{label}.lit", allow_empty=True)
            _require(
                node.get("litType") in {"nat", "string"},
                f"{label}.litType must be 'nat' or 'string'",
            )
        elif kind == "bvar":
            _require_int(node.get("bvar"), f"{label}.bvar", minimum=0)
        elif kind == "proj":
            _require_str(node.get("projStruct"), f"{label}.projStruct")
            _require_int(node.get("projField"), f"{label}.projField", minimum=0)

    # ---- edges ----------------------------------------------------------
    edges = _get_list(graph, "edges", context)
    outgoing: List[List[Tuple[str, int]]] = [[] for _ in range(node_count)]
    incoming: List[int] = [0] * node_count
    seen_edges: Set[Tuple[int, int, str]] = set()
    for index, edge in enumerate(edges):
        label = f"{context}: edges[{index}]"
        _require(isinstance(edge, dict), f"{label} is not an object")
        src = _require_int(edge.get("src"), f"{label}.src", minimum=0)
        dst = _require_int(edge.get("dst"), f"{label}.dst", minimum=0)
        edge_type = _require_str(edge.get("type"), f"{label}.type")
        _require(edge_type in EDGE_TYPES, f"{label}: unknown edge type {edge_type!r}")
        _require(src < node_count, f"{label}: src {src} is out of range")
        _require(dst < node_count, f"{label}: dst {dst} is out of range")
        _require(src != dst, f"{label}: self edge at node {src}")
        key = (src, dst, edge_type)
        _require(key not in seen_edges, f"{label}: duplicate edge {key}")
        seen_edges.add(key)
        outgoing[src].append((edge_type, dst))
        incoming[dst] += 1

    # Structural children of compound nodes, and no structural children on atoms.
    for index, node in enumerate(nodes):
        kind: str = node["kind"]
        children = outgoing[index]
        label = f"{context}: node {index} ({kind})"
        if kind in STRUCTURAL_CHILDREN:
            required = [edge_type for edge_type, _ in STRUCTURAL_CHILDREN[kind]]
            actual = [edge_type for edge_type, _ in children]
            _require(
                sorted(actual) == sorted(required),
                f"{label} has edges {sorted(actual)}, expected {sorted(required)}",
            )
            for edge_type, coordinate in STRUCTURAL_CHILDREN[kind]:
                matches = [dst for edge, dst in children if edge == edge_type]
                _require(
                    len(matches) == 1, f"{label} must have exactly one {edge_type}"
                )
                child = nodes[matches[0]]
                expected = child_position(node["position"], coordinate)
                if child["kind"] in UNIQUE_OCCURRENCE_KINDS:
                    _require(
                        child["position"] == expected,
                        f"{label}'s {edge_type} child has position "
                        f"{child['position']!r}, expected {expected!r}",
                    )
                    _require(
                        child["depth"] == node["depth"] + 1,
                        f"{label}'s {edge_type} child has depth {child['depth']}, "
                        f"expected {node['depth'] + 1}",
                    )
        elif kind in LEAF_KINDS:
            _require(not children, f"{label} must not have outgoing edges")
        else:  # fvar
            for edge_type, _ in children:
                _require(
                    edge_type in {"fvar_type", "fvar_value"},
                    f"{label} may only have fvar_type/fvar_value edges, got {edge_type!r}",
                )
            _require(
                sum(1 for edge, _ in children if edge == "fvar_type") == 1,
                f"{label} must have exactly one fvar_type edge",
            )
            _require(
                sum(1 for edge, _ in children if edge == "fvar_value") <= 1,
                f"{label} must have at most one fvar_value edge",
            )

    # ---- fvars ----------------------------------------------------------
    fvars = _get_list(graph, "fvars", context)
    fvar_indices: Dict[int, Mapping[str, Any]] = {}
    fvar_goal_lists: Dict[int, List[str]] = {}
    for index, fvar in enumerate(fvars):
        label = f"{context}: fvars[{index}]"
        _require(isinstance(fvar, dict), f"{label} is not an object")
        decl_index = _require_int(fvar.get("index"), f"{label}.index", minimum=0)
        _require(
            decl_index not in fvar_indices,
            f"{label}: duplicate fvar index {decl_index}",
        )
        _require_str(fvar.get("name"), f"{label}.name")
        node_id = _require_int(fvar.get("node"), f"{label}.node", minimum=0)
        _require(node_id < node_count, f"{label}.node {node_id} is out of range")
        _require(
            nodes[node_id]["kind"] == "fvar",
            f"{label}.node {node_id} is not a fvar node",
        )
        # `fvars[].index` is the declaration-order table index; the node's
        # `fvar` payload is the builder's occurrence-order id (see schema-v3.md).
        # They need not be equal, but the table and the fvar nodes must form a
        # bijection by node id (checked below).
        type_node = _require_int(fvar.get("type_node"), f"{label}.type_node", minimum=0)
        _require(type_node < node_count, f"{label}.type_node {type_node} is out of range")
        _require(
            ("fvar_type", type_node) in outgoing[node_id],
            f"{label}: node {node_id} has no fvar_type edge to type_node {type_node}",
        )
        expected_values: List[int] = []
        if "value_node" in fvar and fvar["value_node"] is not None:
            value_node = _require_int(
                fvar["value_node"], f"{label}.value_node", minimum=0
            )
            _require(
                value_node < node_count, f"{label}.value_node {value_node} is out of range"
            )
            _require(
                ("fvar_value", value_node) in outgoing[node_id],
                f"{label}: node {node_id} has no fvar_value edge to {value_node}",
            )
            expected_values.append(value_node)
        # Reverse direction: the metadata edges of the node must be exactly the
        # ones the table records, so a missing `value_node` cannot hide a value.
        actual_types = [dst for edge, dst in outgoing[node_id] if edge == "fvar_type"]
        _require(
            actual_types == [type_node],
            f"{label}: node {node_id} has fvar_type edges to {actual_types}, "
            f"expected exactly [{type_node}]",
        )
        actual_values = [dst for edge, dst in outgoing[node_id] if edge == "fvar_value"]
        _require(
            actual_values == expected_values,
            f"{label}: node {node_id} has fvar_value edges to {actual_values}, "
            f"expected {expected_values}",
        )
        decl_goals = _get_list(fvar, "goals", label)
        _require(len(decl_goals) > 0, f"{label}.goals must not be empty")
        for goal_id in decl_goals:
            _require(isinstance(goal_id, str), f"{label}.goals entries must be strings")
            _require(
                goal_id in goal_index,
                f"{label}.goals mentions unknown goal id {goal_id!r}",
            )
        _require(
            len(set(decl_goals)) == len(decl_goals),
            f"{label}.goals contains a duplicate goal id",
        )
        expected_order = [gid for gid in goal_ids if gid in set(decl_goals)]
        _require(
            decl_goals == expected_order,
            f"{label}.goals {decl_goals} must follow goal order {expected_order}",
        )
        fvar_indices[decl_index] = fvar
        fvar_goal_lists[decl_index] = decl_goals

    for fvar_index, node_id in fvar_nodes.items():
        _require(
            fvar_index in fvar_indices,
            f"{context}: fvar node {node_id} (index {fvar_index}) is missing "
            "from the fvars table",
        )
    _require(
        {fvar["node"] for fvar in fvars} == set(fvar_nodes.values()),
        f"{context}: the fvars table must list every fvar node exactly once",
    )
    for goal_index_, goal_id in enumerate(goal_ids):
        declared = sum(
            1 for goals_of_fvar in fvar_goal_lists.values() if goal_id in goals_of_fvar
        )
        _require(
            declared == fvar_counts[goal_index_],
            f"{context}: goal {goal_id!r} declares fvar_count={fvar_counts[goal_index_]} "
            f"but {declared} fvars list it",
        )

    # ---- constants ------------------------------------------------------
    constants = _get_list(graph, "constants", context)
    constant_table: Dict[str, int] = {}
    constant_ids: Dict[str, str] = {}
    constant_nodes: Set[int] = set()
    for index, constant in enumerate(constants):
        label = f"{context}: constants[{index}]"
        _require(isinstance(constant, dict), f"{label} is not an object")
        name = _require_str(constant.get("name"), f"{label}.name")
        gid = _require_str(constant.get("global_id"), f"{label}.global_id")
        node_id = _require_int(constant.get("node"), f"{label}.node", minimum=0)
        _require(node_id < node_count, f"{label}.node {node_id} is out of range")
        _require(
            nodes[node_id]["kind"] == "const",
            f"{label}.node {node_id} is not a const node",
        )
        _require(
            nodes[node_id]["const"] == name,
            f"{label}.name {name!r} does not match node {node_id}",
        )
        _require(
            nodes[node_id].get("global_id") == gid,
            f"{label}: node {node_id} global_id does not match the constants table",
        )
        _require(
            gid == global_constant_id(name),
            f"{label}: global_id {gid!r} is not the stable id for {name!r}",
        )
        _require(name not in constant_table, f"{label}: duplicate constant {name!r}")
        _require(
            gid not in constant_ids.values(),
            f"{label}: duplicate global_id {gid!r} for distinct constants",
        )
        _require(
            node_id not in constant_nodes,
            f"{label}: const node {node_id} appears twice",
        )
        constant_table[name] = node_id
        constant_ids[name] = gid
        constant_nodes.add(node_id)
    _require(
        constant_table == const_nodes,
        f"{context}: constants table is not a bijection with const nodes; "
        f"table={sorted(constant_table)}, nodes={sorted(const_nodes)}",
    )

    # ---- loci -----------------------------------------------------------
    loci = _get_list(graph, "loci", context)
    locus_nodes: Dict[Tuple[str, str], int] = {}
    for index, locus in enumerate(loci):
        label = f"{context}: loci[{index}]"
        _require(isinstance(locus, dict), f"{label} is not an object")
        goal_id = _require_str(locus.get("goal_id"), f"{label}.goal_id")
        _require(
            goal_id in goal_index, f"{label}.goal_id {goal_id!r} is not a declared goal"
        )
        position = _require_str(locus.get("position"), f"{label}.position", allow_empty=True)
        parse_position(position, context=f"{label}.position")
        node_id = _require_int(locus.get("node"), f"{label}.node", minimum=0)
        _require(node_id < node_count, f"{label}.node {node_id} is out of range")
        key = (goal_id, position)
        _require(key not in locus_nodes, f"{label}: duplicate locus {key}")
        locus_nodes[key] = node_id
    for goal_id, root in zip(goal_ids, goal_roots):
        _require(
            (goal_id, "") in locus_nodes,
            f"{context}: goal {goal_id!r} has no root locus ''",
        )
        _require(
            locus_nodes[(goal_id, "")] == root,
            f"{context}: goal {goal_id!r} root locus points at "
            f"{locus_nodes[(goal_id, '')]}, expected {root}",
        )

    # ---- coupled goal graph ---------------------------------------------
    coupled = graph.get("coupled")
    _require(isinstance(coupled, dict), f"{context}: coupled must be an object")
    goal_edges = _get_list(coupled, "goal_edges", f"{context}: coupled")
    groups = _get_list(coupled, "groups", f"{context}: coupled")

    edge_map: Dict[Tuple[str, str], List[int]] = {}
    edge_order: List[Tuple[str, str]] = []
    for index, edge in enumerate(goal_edges):
        label = f"{context}: coupled.goal_edges[{index}]"
        _require(isinstance(edge, dict), f"{label} is not an object")
        src = _require_str(edge.get("src"), f"{label}.src")
        dst = _require_str(edge.get("dst"), f"{label}.dst")
        _require(src in goal_index, f"{label}: unknown src goal {src!r}")
        _require(dst in goal_index, f"{label}: unknown dst goal {dst!r}")
        _require(src != dst, f"{label}: self edge {src!r}")
        _require(
            goal_index[src] < goal_index[dst],
            f"{label}: src must precede dst in goal order",
        )
        key = (src, dst)
        _require(key not in edge_map, f"{label}: duplicate goal edge {key}")
        fvars = _get_list(edge, "fvars", label)
        for fvar in fvars:
            _require_int(fvar, f"{label}.fvars entry", minimum=0)
            _require(fvar in fvar_indices, f"{label}: unknown fvar index {fvar}")
            endpoints = set(fvar_goal_lists[fvar])
            _require(
                src in endpoints or dst in endpoints,
                f"{label}: fvar {fvar} is not declared by either endpoint",
            )
        _require(
            fvars == sorted(set(fvars)),
            f"{label}.fvars must be sorted and unique",
        )
        edge_map[key] = [int(v) for v in fvars]
        edge_order.append(key)
    _require(
        edge_order == sorted(edge_order, key=lambda pair: (goal_index[pair[0]], goal_index[pair[1]])),
        f"{context}: coupled.goal_edges must be sorted by goal order",
    )

    # Every shared fvar must contribute an edge for every pair of its declaring
    # goals.  Target-only edges (mvar references) have no observable fvar and
    # are accepted as explicit graph facts.
    for decl_index, goals_of_fvar in fvar_goal_lists.items():
        if len(goals_of_fvar) < 2:
            continue
        ordered = sorted(goals_of_fvar, key=lambda goal_id: goal_index[goal_id])
        for left_index in range(len(ordered)):
            for right_index in range(left_index + 1, len(ordered)):
                src, dst = ordered[left_index], ordered[right_index]
                _require(
                    (src, dst) in edge_map,
                    f"{context}: shared fvar {decl_index} has no goal edge {src!r}->{dst!r}",
                )
                _require(
                    decl_index in edge_map[(src, dst)],
                    f"{context}: goal edge {src!r}->{dst!r} does not carry shared fvar {decl_index}",
                )

    # Groups are connected components of goal_edges; group fvars are the union
    # of fvars on edges internal to the component.
    parent = {goal_id: goal_id for goal_id in goal_ids}

    def find(item: str) -> str:
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    for src, dst in edge_order:
        parent[find(dst)] = find(src)
    components: Dict[str, List[str]] = {}
    for goal_id in goal_ids:
        components.setdefault(find(goal_id), []).append(goal_id)
    expected_groups: List[Tuple[List[str], List[int]]] = []
    for members in sorted(components.values(), key=lambda group: goal_index[group[0]]):
        if len(members) < 2:
            continue
        member_set = set(members)
        union_fvars: Set[int] = set()
        for (src, dst), fvars in edge_map.items():
            if src in member_set and dst in member_set:
                union_fvars.update(fvars)
        expected_groups.append((members, sorted(union_fvars)))

    reported_groups: List[Tuple[List[str], List[int]]] = []
    goals_with_group: Set[str] = set()
    for index, group in enumerate(groups):
        label = f"{context}: coupled.groups[{index}]"
        _require(isinstance(group, dict), f"{label} is not an object")
        group_goals = _get_list(group, "goals", label)
        group_fvars = _get_list(group, "fvars", label)
        _require(len(group_goals) >= 2, f"{label} must couple at least two goals")
        for goal_id in group_goals:
            _require(isinstance(goal_id, str), f"{label}.goals entries must be strings")
            _require(goal_id in goal_index, f"{label}: unknown goal id {goal_id!r}")
            _require(
                goal_id not in goals_with_group,
                f"{label}: goal {goal_id!r} appears in two coupled groups",
            )
            goals_with_group.add(goal_id)
        _require(
            group_goals == sorted(group_goals, key=lambda g: goal_index[g]),
            f"{label}.goals must be sorted by goal order",
        )
        for decl_index in group_fvars:
            _require_int(decl_index, f"{label}.fvars entry", minimum=0)
            _require(decl_index in fvar_indices, f"{label}: unknown fvar index {decl_index}")
        _require(
            group_fvars == sorted(set(group_fvars)),
            f"{label}.fvars must be sorted and unique",
        )
        reported_groups.append((list(group_goals), [int(v) for v in group_fvars]))

    _require(
        reported_groups == expected_groups,
        f"{context}: coupled groups {reported_groups} do not match the connected "
        f"components of goal_edges {expected_groups}",
    )

    # ---- parse warnings -------------------------------------------------
    warnings = _get_list(graph, "parse_warnings", context)
    for index, warning in enumerate(warnings):
        _require(
            isinstance(warning, str),
            f"{context}: parse_warnings[{index}] must be a string",
        )


# --------------------------------------------------------------------------- #
# Cases and files
# --------------------------------------------------------------------------- #


def _case_name(line: Mapping[str, Any], fallback: str) -> str:
    name = line.get("case")
    return name if isinstance(name, str) else fallback


def validate_case(line: Any, *, context: str) -> Tuple[str, bool]:
    """Validate one JSONL case.

    Returns ``(case name, had_graph)``.  ``graph: null`` lines are validated as
    explicit "no graph" results.
    """
    _require(isinstance(line, dict), f"{context}: line must be a JSON object")
    name = _case_name(line, context)
    if "graph" in line:
        graph = line["graph"]
        if graph is None:
            _require(
                line.get("result") == "none",
                f"{context} ({name}): graph is null but result is "
                f"{line.get('result')!r}; omit the line or set result='none'",
            )
            warnings = line.get("warnings")
            _require(
                isinstance(warnings, list) and len(warnings) > 0,
                f"{context} ({name}): a missing graph must carry at least one warning",
            )
            for index, warning in enumerate(warnings):
                _require(
                    isinstance(warning, str),
                    f"{context} ({name}): warnings[{index}] must be a string",
                )
            if "canonical" in line:
                _require(
                    line["canonical"] is None,
                    f"{context} ({name}): a missing graph cannot have a canonical form",
                )
            return name, False
        _require(
            line.get("result", "ok") == "ok",
            f"{context} ({name}): a graph must have result 'ok'",
        )
        if "canonical" in line:
            _require_str(
                line["canonical"], f"{context} ({name}): canonical", allow_empty=True
            )
        validate_graph(graph, context=f"{context} ({name})")
        return name, True
    # A bare graph object is accepted too (direct graph JSONL).
    _require(
        _is_int(line.get("schema")),
        f"{context}: line is neither a case wrapper nor a graph object",
    )
    validate_graph(line, context=f"{context} ({name})")
    return name, True


def read_cases(path: Path) -> List[Dict[str, Any]]:
    cases: List[Dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_number, raw in enumerate(handle, start=1):
            stripped = raw.strip()
            if not stripped:
                continue
            try:
                decoded = json.loads(stripped)
            except json.JSONDecodeError as error:
                raise ValidationError(f"{path}:{line_number}: invalid JSON ({error})") from error
            _require(
                isinstance(decoded, dict),
                f"{path}:{line_number}: each line must be a JSON object",
            )
            cases.append(decoded)
    return cases


def validate_file(path: Path) -> Tuple[List[Dict[str, Any]], int, int]:
    """Validate one JSONL file.

    Returns ``(cases, graph count, skipped count)``.
    """
    cases = read_cases(path)
    _require(len(cases) > 0, f"{path}: file contains no cases")
    seen: Set[str] = set()
    graphs = 0
    for index, case in enumerate(cases, start=1):
        name, had_graph = validate_case(case, context=f"{path}:{index}")
        _require(name not in seen, f"{path}:{index}: duplicate case name {name!r}")
        seen.add(name)
        graphs += 1 if had_graph else 0
    return cases, graphs, len(cases) - graphs


def case_graph(case: Mapping[str, Any]) -> Mapping[str, Any]:
    if "graph" in case:
        graph = case["graph"]
    else:
        graph = case
    _require(
        isinstance(graph, dict),
        f"case {case.get('case')!r} has no graph to compare",
    )
    return graph


def stored_canonical(case: Mapping[str, Any]) -> str | None:
    canonical = case.get("canonical")
    return canonical if isinstance(canonical, str) else None


# --------------------------------------------------------------------------- #
# Canonical (alpha) form
# --------------------------------------------------------------------------- #


def _node_payload(node: Mapping[str, Any], fvar_canon: Mapping[int, int],
                  mvar_canon: Mapping[int, int], original: int) -> str:
    kind = node["kind"]
    if kind == "const":
        levels = ",".join(node.get("level") or [])
        return f"{node['const']}[{levels}]"
    if kind == "sort":
        return node["sort"]
    if kind == "lit":
        return f"{node['litType']}:{node['lit']}"
    if kind == "bvar":
        return f"bvar{node['bvar']}"
    if kind == "fvar":
        return f"fvar{fvar_canon.get(original, node['fvar'])}"
    if kind == "mvar":
        return f"mvar{mvar_canon.get(original, node['mvar'])}"
    if kind == "proj":
        return f"{node['projStruct']}.{node['projField']}"
    return "-"


def _is_universe_name_char(char: str) -> bool:
    return char.isalnum() or char in "_.'"


def _universe_token_reserved(token: str) -> bool:
    return token in {"Sort", "Type", "Prop", "max", "imax", "succ"} or token.isdigit()


def _rename_universe_text(text: str, state: Dict[str, int], next_index: List[int]) -> str:
    out: List[str] = []
    index = 0
    while index < len(text):
        char = text[index]
        if not _is_universe_name_char(char):
            out.append(char)
            index += 1
            continue
        start = index
        while index < len(text) and _is_universe_name_char(text[index]):
            index += 1
        token = text[start:index]
        if _universe_token_reserved(token):
            out.append(token)
        else:
            mapped = state.get(token)
            if mapped is None:
                mapped = next_index[0]
                state[token] = mapped
                next_index[0] += 1
            out.append(f"u{mapped}")
    return "".join(out)


def _rename_const_payload(payload: str, state: Dict[str, int], next_index: List[int]) -> str:
    if "[" not in payload:
        return payload
    prefix, rest = payload.split("[", 1)
    if "]" not in rest:
        return payload
    levels, tail = rest.split("]", 1)
    return f"{prefix}[{_rename_universe_text(levels, state, next_index)}]{tail}"


def _rename_universe_lines(lines: List[str]) -> List[str]:
    state: Dict[str, int] = {}
    next_index = [0]
    out: List[str] = []
    for line in lines:
        parts = line.split(" ", 3)
        if len(parts) == 4 and parts[0] == "node":
            node_id, kind, payload = parts[1], parts[2], parts[3]
            if kind == "sort":
                payload = _rename_universe_text(payload, state, next_index)
            elif kind == "const":
                payload = _rename_const_payload(payload, state, next_index)
            out.append(f"node {node_id} {kind} {payload}")
        else:
            out.append(line)
    return out


def canonical_form(graph: Mapping[str, Any]) -> str:
    """Metadata-free canonical text form of a schema-3 graph.

    Mirrors ``ExprGraphV3.alphaNormalizeV3`` (Lean) closely enough that equality of
    two canonical forms is the same relation: node/fvar/mvar ids are renumbered
    by a deterministic traversal from the goal roots, and every name- or
    position-bearing field is dropped.
    """
    nodes = graph["nodes"]
    edges = graph["edges"]
    goals = graph["goals"]
    node_count = len(nodes)

    adjacency: List[List[Tuple[str, int]]] = [[] for _ in range(node_count)]
    for edge in edges:
        src, dst = edge["src"], edge["dst"]
        if 0 <= src < node_count and 0 <= dst < node_count:
            adjacency[src].append((edge["type"], dst))
    for children in adjacency:
        children.sort(key=lambda child: EDGE_RANK.get(child[0], 10))

    goal_ids = [goal["goal_id"] for goal in goals]
    goal_index = {goal_id: index for index, goal_id in enumerate(goal_ids)}
    roots = [goal["root"] for goal in goals]

    order: List[int] = []
    seen: Set[int] = set()
    fvar_canon: Dict[int, int] = {}
    mvar_canon: Dict[int, int] = {}

    def visit(starts: Iterable[int]) -> None:
        stack: Deque[int] = deque(starts)
        while stack:
            node_id = stack.popleft()
            if node_id in seen or node_id >= node_count:
                continue
            seen.add(node_id)
            order.append(node_id)
            if nodes[node_id]["kind"] == "fvar":
                fvar_canon[node_id] = len(fvar_canon)
            elif nodes[node_id]["kind"] == "mvar":
                mvar_canon[node_id] = len(mvar_canon)
            children = [dst for _, dst in adjacency[node_id]]
            stack.extendleft(reversed(children))

    visit(roots)
    for fvar in graph["fvars"]:
        visit([fvar["node"], fvar["type_node"]])
        if fvar.get("value_node") is not None:
            visit([fvar["value_node"]])
    visit(range(node_count))

    canon = {node_id: index for index, node_id in enumerate(order)}

    def canon_id(node_id: int) -> int:
        return canon.get(node_id, node_id)

    lines: List[str] = ["exprgraph-v3-canonical"]
    if graph.get("constant") is not None:
        lines.append(f"constant {graph['constant']}")
    lines.append(f"goals {len(goals)}")
    for index, root in enumerate(roots):
        lines.append(f"goal {index} root {canon_id(root)}")
    for position in order:
        node = nodes[position]
        lines.append(
            f"node {canon[position]} {node['kind']} "
            f"{_node_payload(node, fvar_canon, mvar_canon, position)}"
        )
    for position in order:
        for edge_type, dst in adjacency[position]:
            lines.append(f"edge {canon[position]} {edge_type} {canon_id(dst)}")
    for constant in sorted(graph["constants"], key=lambda entry: entry["name"]):
        lines.append(
            f"const {constant['name']} {constant['global_id']} "
            f"{canon_id(constant['node'])}"
        )

    fvar_lines: List[Tuple[int, str]] = []
    fvar_index_to_canon: Dict[int, int] = {}
    for fvar in graph["fvars"]:
        canon_index = fvar_canon.get(fvar["node"], fvar["index"])
        fvar_index_to_canon[fvar["index"]] = canon_index
        base = (
            f"fvar {canon_index} node {canon_id(fvar['node'])} "
            f"type {canon_id(fvar['type_node'])}"
        )
        if fvar.get("value_node") is not None:
            base += f" value {canon_id(fvar['value_node'])}"
        fvar_lines.append((canon_index, base))
    for _, line in sorted(fvar_lines, key=lambda entry: entry[0]):
        lines.append(line)

    for mvar in graph.get("mvars") or []:
        lines.append(
            f"mvar {mvar_canon.get(mvar['node'], mvar['index'])} "
            f"node {canon_id(mvar['node'])}"
        )

    coupled = graph["coupled"]
    for group in coupled["groups"]:
        group_goals = sorted(goal_index[g] for g in group["goals"])
        group_fvars = sorted(
            fvar_index_to_canon.get(index, index) for index in group["fvars"]
        )
        joined_goals = ",".join(str(index) for index in group_goals)
        joined_fvars = ",".join(str(index) for index in group_fvars)
        lines.append(f"coupled-group [{joined_goals}] [{joined_fvars}]")

    for edge in coupled["goal_edges"]:
        src = goal_index[edge["src"]]
        dst = goal_index[edge["dst"]]
        edge_fvars = sorted(
            fvar_index_to_canon.get(index, index) for index in edge["fvars"]
        )
        joined_fvars = ",".join(str(index) for index in edge_fvars)
        lines.append(f"goal-edge {src} {dst} [{joined_fvars}]")

    locus_pairs = sorted(
        (goal_index[locus["goal_id"]], canon_id(locus["node"])) for locus in graph["loci"]
    )
    for goal_position, node_id in locus_pairs:
        lines.append(f"locus {goal_position} {node_id}")

    return "\n".join(_rename_universe_lines(lines))


def alpha_equivalent(left: Mapping[str, Any], right: Mapping[str, Any]) -> bool:
    return canonical_form(left) == canonical_form(right)


# --------------------------------------------------------------------------- #
# Statistics and CLI
# --------------------------------------------------------------------------- #


def graph_stats(graph: Mapping[str, Any]) -> Dict[str, int]:
    shared = [fvar for fvar in graph["fvars"] if len(fvar["goals"]) >= 2]
    coupled = graph["coupled"]
    groups = coupled["groups"]
    return {
        "goals": len(graph["goals"]),
        "nodes": len(graph["nodes"]),
        "edges": len(graph["edges"]),
        "loci": len(graph["loci"]),
        "fvars": len(graph["fvars"]),
        "shared_fvars": len(shared),
        "coupled_groups": len(groups),
        "coupled_goals": sum(len(group["goals"]) for group in groups),
        "goal_edges": len(coupled["goal_edges"]),
        "constants": len(graph["constants"]),
    }


def summarise(cases: Sequence[Mapping[str, Any]]) -> Dict[str, int]:
    totals = {
        "graphs": 0,
        "goals": 0,
        "nodes": 0,
        "edges": 0,
        "loci": 0,
        "fvars": 0,
        "shared_fvars": 0,
        "coupled_groups": 0,
        "coupled_goals": 0,
        "goal_edges": 0,
        "constants": 0,
    }
    for case in cases:
        graph = case.get("graph")
        if not isinstance(graph, dict):
            continue
        totals["graphs"] += 1
        for key, value in graph_stats(graph).items():
            totals[key] += value
    return totals


def render_stats(totals: Mapping[str, int]) -> str:
    return " ".join(f"{key}={value}" for key, value in totals.items())


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="validate_exprgraph_v3.py",
        description=(
            "Validate schema-3 ExprGraph JSONL (goal-edge ExprGraph), compare "
            "alpha-normalized cases, and report graph statistics."
        ),
        epilog=(
            "exit codes: 0 = valid, 1 = invalid or alpha mismatch, 2 = usage error"
        ),
    )
    parser.add_argument("files", nargs="*", metavar="FILE", help="JSONL file(s) to validate")
    parser.add_argument(
        "--alpha",
        nargs=3,
        metavar=("FILE", "CASE_A", "CASE_B"),
        help="compare the canonical forms of two cases in FILE",
    )
    parser.add_argument(
        "--stats",
        action="store_true",
        help="print aggregate graph statistics after validation",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="only print errors and the statistics requested explicitly",
    )
    return parser


def run_alpha(path: Path, name_a: str, name_b: str) -> int:
    cases = read_cases(path)
    by_name: Dict[str, Mapping[str, Any]] = {}
    for case in cases:
        by_name[_case_name(case, "")] = case
    missing = [name for name in (name_a, name_b) if name not in by_name]
    if missing:
        raise ValidationError(
            f"{path}: no case named {', '.join(repr(name) for name in missing)}"
        )
    left, right = by_name[name_a], by_name[name_b]
    left_graph, right_graph = case_graph(left), case_graph(right)
    validate_graph(left_graph, context=f"{path} ({name_a})")
    validate_graph(right_graph, context=f"{path} ({name_b})")

    # The computed form is authoritative: it is an independent reimplementation
    # of the schema-3 canonical form, including the coupled groups' canonical
    # goal indices.  It matches `ExprGraphV2.alphaNormalize` byte-for-byte on
    # every checked-in graph.
    left_text = canonical_form(left_graph)
    right_text = canonical_form(right_graph)
    equal = left_text == right_text
    stored_left, stored_right = stored_canonical(left), stored_canonical(right)
    if stored_left is not None and stored_right is not None:
        if (stored_left == stored_right) != equal:
            print(
                f"warning: the stored canonical forms of {name_a}/{name_b} disagree "
                "with the computed verdict; the field may be stale",
                file=sys.stderr,
            )

    if equal:
        print(f"alpha: {name_a} == {name_b} (computed canonical forms)")
        return 0

    print(f"alpha: {name_a} != {name_b} (computed canonical forms)")
    left_lines = left_text.splitlines()
    right_lines = right_text.splitlines()
    for index in range(max(len(left_lines), len(right_lines))):
        left_line = left_lines[index] if index < len(left_lines) else "<missing>"
        right_line = right_lines[index] if index < len(right_lines) else "<missing>"
        if left_line != right_line:
            print(f"  first difference at line {index + 1}:")
            print(f"    {name_a}: {left_line}")
            print(f"    {name_b}: {right_line}")
            break
    return 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        if args.alpha:
            path = Path(args.alpha[0])
            return run_alpha(path, args.alpha[1], args.alpha[2])

        if not args.files:
            parser.error("at least one FILE is required (or use --alpha)")
        all_cases: List[Mapping[str, Any]] = []
        for name in args.files:
            path = Path(name)
            cases, graphs, skipped = validate_file(path)
            all_cases.extend(cases)
            if not args.quiet:
                suffix = f", {skipped} skipped" if skipped else ""
                print(f"OK {path}: {len(cases)} case(s), {graphs} graph(s){suffix}")
        if args.stats:
            print(f"stats {render_stats(summarise(all_cases))}")
        return 0
    except ValidationError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    except OSError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
