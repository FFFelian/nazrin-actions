#!/usr/bin/env python3
"""Validate schema-4 structured atomization traces (Gate 1.4a).

A schema-4 step record is a schema-3 step record plus the training inputs Gate
1.2 was missing:

  * ``goal_state_graph``      schema-3 ExprGraph of the complete pre-step goal state
  * ``premise_candidates``    ordered ``{name, id, origin}`` candidate table
  * ``candidates.locus_candidates``  full ``{position, index, node, scope}`` list
  * ``candidates.free_variable_nodes`` ``{name, graph_index, node, type_node}``
  * ``goal_state``            every goal + current goal + coupled groups
  * ``provenance``            per-step evidence (graph stats, label assertions)

The checker is independent of the exporter: it re-derives every assertion from
the embedded graph and the documented contract, and it delegates the graph
itself to the official schema-3 validator
(``experiments/exprgraph/v3/validate_exprgraph_v3.py``).

Rules, in the order they are applied:

1. **Envelope.**  ``schema`` is 3 (compatible) or 4 (strict); ``schema_version``
   is 4; ``record`` is ``step``; ``run_id``/``theorem``/``module``/``step``/
   ``goal_id`` are present.  The envelope schema is recorded once per run.
2. **Graph.**  ``goal_state_graph`` passes the schema-3 validator.  Its goal ids
   are exactly ``goal_state.goal_ids`` in the same order, the step's ``goal_id``
   is one of them, ``goal_state.goals`` equals the graph's ``goals`` (id, root,
   fvar_count), and ``goal_state.coupled`` equals the graph's ``coupled``.
3. **Free variables.**  ``candidates.free_variables`` is the graph's fvar table
   filtered by the current goal, in table order and with the graph's names;
   ``free_variable_count`` matches; every ``free_variable`` /
   ``site_free_variable`` label is that name at that index.
4. **Premise.**  Every item is ``{name, id, origin}`` with 16-hex-digit
   ``id == fnv1a64(name)`` and ``origin`` in ``{"graph", "label"}``.  In the
   default ``graph`` mode no item may carry ``origin == "label"`` (the answer is
   never pasted into the table).  When the record has a ``premise`` label it must
   be in the table, its ``index`` must be that position, and its ``id`` must
   match; when the label is absent the provenance must say
   ``label_missing == true`` rather than invent an entry.
5. **Locus.**  ``candidates.locus_candidates`` entries are
   ``{position, index, node, scope, scope_fvar?}`` with ``index`` equal to the
   list position, unique positions, ``node`` inside the graph, ``scope`` in
   ``{"goal", "hypotheses"}``.  For ``scope == "goal"`` every
   ``(goal_id, position)`` must be a graph locus with the same node.  A
   ``locus`` label must address its parameter, its index, its node and its scope;
   ``params.locus`` must equal ``labels.locus.position``.
6. **Parameters/labels.**  Pointer parameters (``premise``, ``free_variable``,
   ``site_free_variable``, ``locus``) each have a matching label and each label
   has a matching parameter.  Categorical parameters take a documented value.
7. **Target exclusion.**  No ``premise`` label may name the theorem itself or a
   name derived from it (``T.eq_1``, ``T._unary``, ``_private...T...``).
8. **Fail closed.**  A record with ``error`` must not carry a graph, candidate
   table or goal state, and its tactic parameters must be empty.  That is the
   "write an error, never a fake graph/table" path.

Usage::

    python3 experiments/npa_data/validate_structured_v4.py STEP_JSONL [STEP_JSONL ...]
    python3 experiments/npa_data/validate_structured_v4.py --stats steps.jsonl
    python3 experiments/npa_data/validate_structured_v4.py --require-graph steps.jsonl

Exit code 0 = every step valid, 1 = at least one invalid step or a strict-mode
violation, 2 = the input could not be read.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "exprgraph" / "v3"))

from validate_exprgraph_v3 import ValidationError, global_constant_id, validate_graph  # noqa: E402

STEP_SCHEMA_VALUES = (3, 4)
SCHEMA_VERSION = 4
POINTER_PARAMETERS = ("premise", "free_variable", "site_free_variable", "locus")
CATEGORY_VALUES: dict[str, tuple[str, ...]] = {
    "direction": ("forward", "backward"),
    "occurrence": ("all", "first", "last", "specified"),
    "cases_mode": ("constructors", "equations", "all"),
    "induction_mode": ("ordinary", "using", "cases"),
    "name_mode": ("auto", "explicit", "anonymous"),
    "target_mode": ("goal", "hypotheses", "all"),
}
META_PARAMETERS = ("argument_mode",)
LOCUS_SCOPES = ("goal", "hypotheses")
ORIGINS = ("graph", "label")
FNV_HEX = set("0123456789abcdef")


class RecordError(ValueError):
    """A schema-4 step record violates the documented contract."""


def _require(condition: Any, message: str) -> None:
    if not condition:
        raise RecordError(message)


def _mapping(value: Any, label: str) -> Mapping[str, Any]:
    _require(isinstance(value, Mapping), f"{label} must be an object")
    return value


def _list(value: Any, label: str) -> list[Any]:
    _require(isinstance(value, list), f"{label} must be a list")
    return list(value)


def _string(value: Any, label: str, *, allow_empty: bool = False) -> str:
    _require(isinstance(value, str), f"{label} must be a string")
    _require(allow_empty or bool(value), f"{label} must not be empty")
    return value


def _integer(value: Any, label: str, *, minimum: int = 0) -> int:
    _require(isinstance(value, int) and not isinstance(value, bool), f"{label} must be an integer")
    _require(value >= minimum, f"{label} must be >= {minimum}")
    return value


def _optional_int(value: Any, label: str) -> int | None:
    if value is None:
        return None
    return _integer(value, label)


def fnv1a64_id(name: str) -> str:
    return global_constant_id(name)


def normalize_position(position: str) -> str:
    return "root" if position == "" else position


def _fvar_rows(graph: Mapping[str, Any], goal_id: str) -> list[dict[str, Any]]:
    rows = []
    for entry in graph.get("fvars") or []:
        if not isinstance(entry, Mapping):
            continue
        if goal_id in (entry.get("goals") or []):
            rows.append(dict(entry))
    return rows


def _goal_rows(graph: Mapping[str, Any]) -> list[dict[str, Any]]:
    out = []
    for entry in graph.get("goals") or []:
        if not isinstance(entry, Mapping):
            continue
        out.append(
            {
                "goal_id": entry.get("goal_id"),
                "root": entry.get("root"),
                "fvar_count": entry.get("fvar_count"),
            }
        )
    return out


def _locus_map(graph: Mapping[str, Any]) -> dict[tuple[str, str], int]:
    out: dict[tuple[str, str], int] = {}
    for entry in graph.get("loci") or []:
        if not isinstance(entry, Mapping):
            continue
        key = (str(entry.get("goal_id")), normalize_position(str(entry.get("position"))))
        out[key] = int(entry.get("node"))
    return out


def _constant_names(graph: Mapping[str, Any]) -> list[str]:
    names = []
    for entry in graph.get("constants") or []:
        if isinstance(entry, Mapping) and isinstance(entry.get("name"), str):
            names.append(entry["name"])
    return names


def _is_target_derived(theorem: str, name: str) -> bool:
    if name == theorem or name.startswith(theorem + "."):
        return True
    return name.startswith("_private") and theorem in name


# ---------------------------------------------------------------------------
# Per-step validation
# ---------------------------------------------------------------------------


def validate_step_record(record: Mapping[str, Any], *, context: str,
                         strict: bool = False) -> dict[str, Any]:
    """Validate one schema-4 step record; raise ``RecordError`` on any gap.

    With ``strict`` the record must also be *convertible*: every pointer
    parameter has a validated label.  Without it, an honestly reported missing
    label (``provenance.premise.label_missing``) is accepted as a real gap: the
    record keeps the real candidate table and the real tactic parameter, and the
    downstream converter skips it.  Nothing is ever fabricated either way.

    Returns a small evidence dictionary used by ``--stats``.
    """

    if record.get("record") != "step":
        raise RecordError(f"{context}: not a step record")
    schema = record.get("schema")
    _require(schema in STEP_SCHEMA_VALUES, f"{context}: schema {schema!r} is not 3 or 4")
    _require(record.get("schema_version") == SCHEMA_VERSION, f"{context}: schema_version must be 4")
    theorem = _string(record.get("theorem"), f"{context}: theorem")
    goal_id = _string(record.get("goal_id"), f"{context}: goal_id")
    step_index = _integer(record.get("step"), f"{context}: step")
    tactic = _mapping(record.get("tactic"), f"{context}: tactic")
    kind = _string(tactic.get("kind"), f"{context}: tactic.kind")

    error = record.get("error")
    if error is not None:
        return _validate_error_record(record, context=context, theorem=theorem, goal_id=goal_id,
                                      step_index=step_index, kind=kind, error=error)

    graph = _mapping(record.get("goal_state_graph"), f"{context}: goal_state_graph")
    try:
        validate_graph(graph, context=f"{context}: goal_state_graph")
    except ValidationError as exc:
        raise RecordError(f"{context}: embedded graph is invalid: {exc}") from exc

    provenance = _mapping(record.get("provenance"), f"{context}: provenance")
    _require(provenance.get("ok") is True, f"{context}: provenance.ok must be true")
    _require(provenance.get("error") is None, f"{context}: provenance.error must be null")
    graph_provenance = _mapping(provenance.get("graph"), f"{context}: provenance.graph")
    _require(graph_provenance.get("built") is True, f"{context}: graph must be recorded as built")
    _require(
        graph_provenance.get("meta_state_discarded") is True,
        f"{context}: graph provenance must state that the MetaM state was discarded",
    )
    _require(
        graph_provenance.get("node_count") == len(graph.get("nodes") or []),
        f"{context}: provenance.graph.node_count disagrees with the graph",
    )
    _require(
        graph_provenance.get("edge_count") == len(graph.get("edges") or []),
        f"{context}: provenance.graph.edge_count disagrees with the graph",
    )
    _require(
        graph_provenance.get("constant_count") == len(graph.get("constants") or []),
        f"{context}: provenance.graph.constant_count disagrees with the graph",
    )
    _require(
        graph_provenance.get("locus_count") == len(graph.get("loci") or []),
        f"{context}: provenance.graph.locus_count disagrees with the graph",
    )

    goal_rows = _goal_rows(graph)
    goal_ids = [row["goal_id"] for row in goal_rows]
    _require(goal_id in goal_ids, f"{context}: current goal {goal_id!r} is not in the graph")

    # ---- goal_state ------------------------------------------------------
    goal_state = _mapping(record.get("goal_state"), f"{context}: goal_state")
    state_ids = _list(goal_state.get("goal_ids"), f"{context}: goal_state.goal_ids")
    _require(state_ids == goal_ids, f"{context}: goal_state.goal_ids must equal the graph goal ids")
    _require(
        goal_state.get("current_goal_id") == goal_id,
        f"{context}: goal_state.current_goal_id must equal step.goal_id",
    )
    _require(
        goal_state.get("goal_count") == len(goal_ids),
        f"{context}: goal_state.goal_count disagrees with the graph",
    )
    state_goals = _list(goal_state.get("goals"), f"{context}: goal_state.goals")
    _require(len(state_goals) == len(goal_rows), f"{context}: goal_state.goals length mismatch")
    for index, (state_goal, goal_row) in enumerate(zip(state_goals, goal_rows)):
        state_goal = _mapping(state_goal, f"{context}: goal_state.goals[{index}]")
        _require(state_goal.get("goal_id") == goal_row["goal_id"],
                 f"{context}: goal_state.goals[{index}] id mismatch")
        _require(state_goal.get("root") == goal_row["root"],
                 f"{context}: goal_state.goals[{index}] root mismatch")
        _require(state_goal.get("fvar_count") == goal_row["fvar_count"],
                 f"{context}: goal_state.goals[{index}] fvar_count mismatch")
    coupled = _mapping(goal_state.get("coupled"), f"{context}: goal_state.coupled")
    graph_coupled = _mapping(graph.get("coupled"), f"{context}: graph.coupled")
    _require(
        coupled.get("goal_edges") == graph_coupled.get("goal_edges"),
        f"{context}: goal_state.coupled.goal_edges differs from the graph",
    )
    _require(
        coupled.get("groups") == graph_coupled.get("groups"),
        f"{context}: goal_state.coupled.groups differs from the graph",
    )

    # ---- free variables --------------------------------------------------
    candidates = _mapping(record.get("candidates"), f"{context}: candidates")
    free_variables = _list(candidates.get("free_variables"), f"{context}: candidates.free_variables")
    fvar_rows = _fvar_rows(graph, goal_id)
    expected_names = [row.get("name") for row in fvar_rows]
    _require(
        free_variables == expected_names,
        f"{context}: candidates.free_variables {free_variables} != graph fvar table "
        f"for the current goal {expected_names}",
    )
    _require(
        candidates.get("free_variable_count") == len(expected_names),
        f"{context}: free_variable_count disagrees with the graph",
    )
    node_rows = _list(candidates.get("free_variable_nodes"),
                      f"{context}: candidates.free_variable_nodes")
    _require(len(node_rows) == len(fvar_rows), f"{context}: free_variable_nodes length mismatch")
    for index, (node_row, fvar_row) in enumerate(zip(node_rows, fvar_rows)):
        node_row = _mapping(node_row, f"{context}: free_variable_nodes[{index}]")
        _require(node_row.get("name") == fvar_row.get("name"),
                 f"{context}: free_variable_nodes[{index}].name mismatch")
        _require(node_row.get("graph_index") == fvar_row.get("index"),
                 f"{context}: free_variable_nodes[{index}].graph_index mismatch")
        _require(node_row.get("node") == fvar_row.get("node"),
                 f"{context}: free_variable_nodes[{index}].node mismatch")
        _require(node_row.get("type_node") == fvar_row.get("type_node"),
                 f"{context}: free_variable_nodes[{index}].type_node mismatch")

    labels = _mapping(record.get("labels", {}), f"{context}: labels")
    parameters = _mapping(tactic.get("parameters", {}), f"{context}: tactic.parameters")

    # ---- premise ---------------------------------------------------------
    premise_items = _list(record.get("premise_candidates"), f"{context}: premise_candidates")
    parsed_items: list[tuple[str, str, str]] = []
    for index, item in enumerate(premise_items):
        item = _mapping(item, f"{context}: premise_candidates[{index}]")
        name = _string(item.get("name"), f"{context}: premise_candidates[{index}].name")
        identifier = _string(item.get("id"), f"{context}: premise_candidates[{index}].id")
        _require(len(identifier) == 16 and set(identifier) <= FNV_HEX,
                 f"{context}: premise_candidates[{index}].id is not 16 lowercase hex digits")
        _require(identifier == fnv1a64_id(name),
                 f"{context}: premise_candidates[{index}].id is not FNV-1a-64 of {name!r}")
        origin = _string(item.get("origin"), f"{context}: premise_candidates[{index}].origin")
        _require(origin in ORIGINS, f"{context}: premise_candidates[{index}].origin {origin!r} invalid")
        parsed_items.append((name, identifier, origin))
    _require(len({name for name, _, _ in parsed_items}) == len(parsed_items),
             f"{context}: duplicate premise candidate")
    premise_provenance = _mapping(provenance.get("premise"), f"{context}: provenance.premise")
    mode = premise_provenance.get("mode")
    _require(mode in ("graph", "append"), f"{context}: unknown premise mode {mode!r}")
    _require(premise_provenance.get("table_size") == len(parsed_items),
             f"{context}: provenance.premise.table_size disagrees with the table")
    if mode == "graph":
        _require(all(origin == "graph" for _, _, origin in parsed_items),
                 f"{context}: the default graph mode must not append the observed label")
    label = labels.get("premise")
    convertible = True
    if label is None:
        _require(premise_provenance.get("label_in_table") is False,
                 f"{context}: provenance.premise.label_in_table must be false without a label")
        if "premise" in parameters:
            # Real gap: the observed premise is not in the graph's constant table.
            # It must be reported, never patched into the table.
            _require(premise_provenance.get("label_missing") is True,
                     f"{context}: a missing premise label must be recorded as label_missing")
            _require(premise_provenance.get("label") == parameters.get("premise"),
                     f"{context}: provenance.premise.label must name the unplaceable premise")
            convertible = False
            if strict:
                raise RecordError(
                    f"{context}: premise {parameters.get('premise')!r} is not in the graph's "
                    "constant candidate table (not convertible)"
                )
    else:
        label = _mapping(label, f"{context}: labels.premise")
        name = _string(label.get("name"), f"{context}: labels.premise.name")
        index = _integer(label.get("index"), f"{context}: labels.premise.index")
        _require(index < len(parsed_items), f"{context}: premise label index out of range")
        _require(parsed_items[index][0] == name,
                 f"{context}: premise label {name!r} is not at candidate index {index}")
        _require(label.get("id") == parsed_items[index][1],
                 f"{context}: premise label id disagrees with the candidate")
        _require(parameters.get("premise") == name,
                 f"{context}: parameters.premise disagrees with the label")
        _require(premise_provenance.get("label_in_table") is True,
                 f"{context}: provenance.premise.label_in_table must be true")
        _require(premise_provenance.get("label_index") == index,
                 f"{context}: provenance.premise.label_index disagrees with the label")
        _require(label.get("origin") == parsed_items[index][2],
                 f"{context}: premise label origin disagrees with the candidate")
        _require(not _is_target_derived(theorem, name),
                 f"{context}: premise label {name!r} is the target or derived from it")
        graph_names = _constant_names(graph)
        _require(
            premise_provenance.get("label_in_graph_constants") == (name in graph_names),
            f"{context}: provenance.premise.label_in_graph_constants is wrong",
        )

    premise_labelled = label is not None

    # ---- locus -----------------------------------------------------------
    locus_items = _list(candidates.get("locus_candidates"), f"{context}: locus_candidates")
    scope_name = candidates.get("locus_scope")
    _require(scope_name in LOCUS_SCOPES, f"{context}: candidates.locus_scope {scope_name!r} invalid")
    _require(candidates.get("locus_count") == len(locus_items),
             f"{context}: locus_count disagrees with the locus candidate list")
    graph_loci = _locus_map(graph)
    node_count = len(graph.get("nodes") or [])
    positions: list[str] = []
    raw_positions: list[str] = []
    parsed_loci: list[dict[str, Any]] = []
    for index, item in enumerate(locus_items):
        item = _mapping(item, f"{context}: locus_candidates[{index}]")
        raw_position = _string(item.get("position"), f"{context}: locus_candidates[{index}].position",
                               allow_empty=True)
        raw_positions.append(raw_position)
        position = normalize_position(raw_position)
        _require(item.get("index") == index,
                 f"{context}: locus_candidates[{index}].index must equal its list position")
        node = _integer(item.get("node"), f"{context}: locus_candidates[{index}].node")
        _require(node < node_count, f"{context}: locus_candidates[{index}].node outside the graph")
        scope = _string(item.get("scope"), f"{context}: locus_candidates[{index}].scope")
        _require(scope in LOCUS_SCOPES, f"{context}: locus_candidates[{index}].scope invalid")
        _require(scope == scope_name, f"{context}: locus candidate scope differs from locus_scope")
        _require(position not in positions, f"{context}: duplicate locus candidate {position!r}")
        positions.append(position)
        if scope == "goal":
            key = (goal_id, position)
            _require(key in graph_loci,
                     f"{context}: target locus {position!r} is not a graph locus of {goal_id}")
            _require(graph_loci[key] == node,
                     f"{context}: target locus {position!r} node disagrees with the graph")
        else:
            scope_fvar = _mapping(item.get("scope_fvar"), f"{context}: locus_candidates[{index}].scope_fvar")
            fvar_index = _integer(scope_fvar.get("index"), f"{context}: scope_fvar.index")
            fvar_name = _string(scope_fvar.get("name"), f"{context}: scope_fvar.name")
            declared = [row for row in graph.get("fvars") or []
                        if isinstance(row, Mapping) and row.get("index") == fvar_index]
            _require(len(declared) == 1, f"{context}: hypothesis scope fvar {fvar_index} is not in the graph")
            _require(declared[0].get("name") == fvar_name,
                     f"{context}: hypothesis scope fvar name disagrees with the graph")
        parsed_loci.append({"position": position, "raw_position": raw_position,
                            "node": node, "scope": scope})
    fingerprint = candidates.get("locus_fingerprint")
    _require(
        fingerprint == _fingerprint(raw_positions),
        f"{context}: locus_fingerprint does not match the locus positions",
    )
    locus_provenance = _mapping(provenance.get("locus"), f"{context}: provenance.locus")
    _require(locus_provenance.get("scope") == scope_name,
             f"{context}: provenance.locus.scope disagrees with candidates.locus_scope")
    _require(locus_provenance.get("count") == len(locus_items),
             f"{context}: provenance.locus.count disagrees with the candidate list")
    locus_label = labels.get("locus")
    if "locus" in parameters:
        _require(locus_label is not None, f"{context}: parameters.locus without a checked label")
    if locus_label is not None:
        locus_label = _mapping(locus_label, f"{context}: labels.locus")
        position = normalize_position(_string(locus_label.get("position"), f"{context}: labels.locus.position",
                                              allow_empty=True))
        index = _integer(locus_label.get("index"), f"{context}: labels.locus.index")
        _require(index < len(parsed_loci), f"{context}: locus label index out of range")
        _require(parsed_loci[index]["position"] == position,
                 f"{context}: locus label {position!r} is not at candidate index {index}")
        _require(locus_label.get("node") == parsed_loci[index]["node"],
                 f"{context}: locus label node disagrees with the candidate")
        _require(parameters.get("locus") == position,
                 f"{context}: parameters.locus disagrees with the label")
        _require(locus_label.get("scope") == scope_name,
                 f"{context}: locus label scope disagrees with the candidate list")
        _require(locus_provenance.get("index") == index,
                 f"{context}: provenance.locus.index disagrees with the label")

    # ---- parameters and labels ------------------------------------------
    missing_premise = (label is None and "premise" in parameters)
    for name in POINTER_PARAMETERS:
        if name in parameters:
            if name == "premise" and missing_premise:
                # Reported, not fabricated: the observed premise is a real constant
                # that the graph's constant table does not contain.
                continue
            _require(name in labels, f"{context}: pointer parameter {name!r} has no checked label")
        if name in labels:
            _require(name in parameters, f"{context}: label {name!r} without a parameter")
    for name, value in parameters.items():
        if name in POINTER_PARAMETERS or name in META_PARAMETERS:
            continue
        _require(name in CATEGORY_VALUES, f"{context}: unsupported parameter {name!r}")
        _require(value in CATEGORY_VALUES[name], f"{context}: parameter {name!r}={value!r} invalid")
        category_label = labels.get(name)
        if category_label is not None:
            category_label = _mapping(category_label, f"{context}: labels.{name}")
            _require(category_label.get("value", category_label.get("name")) == value,
                     f"{context}: label {name!r} disagrees with its parameter")
    for name in ("free_variable", "site_free_variable"):
        label = labels.get(name)
        if label is None:
            continue
        label = _mapping(label, f"{context}: labels.{name}")
        fvar_name = _string(label.get("name"), f"{context}: labels.{name}.name")
        index = _integer(label.get("index"), f"{context}: labels.{name}.index")
        _require(index < len(expected_names), f"{context}: labels.{name}.index out of range")
        _require(expected_names[index] == fvar_name,
                 f"{context}: labels.{name} {fvar_name!r} is not at candidate index {index}")
        _require(parameters.get(name) == fvar_name,
                 f"{context}: parameters.{name} disagrees with the label")

    children = _list(record.get("children", []), f"{context}: children")
    for child in children:
        _require(isinstance(child, str) and child, f"{context}: children entries must be goal ids")

    return {
        "ok": True,
        "kind": kind,
        "goals": len(goal_ids),
        "nodes": node_count,
        "premise_table": len(parsed_items),
        "premise_label_in_table": premise_labelled,
        "premise_label_missing_reported": bool(premise_provenance.get("label_missing")),
        "locus_scope": scope_name,
        "locus_count": len(locus_items),
        "locus_labelled": locus_label is not None,
        "coupled_groups": len(graph_coupled.get("groups") or []),
        "coupled_edges": len(graph_coupled.get("goal_edges") or []),
        "graph_bytes": len(json.dumps(graph, sort_keys=True, separators=(",", ":")).encode("utf-8")),
        "error": None,
        "convertible": convertible,
    }


def _validate_error_record(record: Mapping[str, Any], *, context: str, theorem: str,
                           goal_id: str, step_index: int, kind: str, error: Any) -> dict[str, Any]:
    error = _mapping(error, f"{context}: error")
    _string(error.get("code"), f"{context}: error.code")
    _string(error.get("message"), f"{context}: error.message")
    for forbidden in ("goal_state_graph", "premise_candidates", "goal_state"):
        _require(forbidden not in record,
                 f"{context}: an error record must not carry {forbidden}")
    candidates = record.get("candidates")
    if candidates is not None:
        candidates = _mapping(candidates, f"{context}: candidates")
        _require(not candidates.get("locus_candidates"),
                 f"{context}: an error record must not carry locus candidates")
    parameters = _mapping(record.get("tactic", {}).get("parameters", {}),
                          f"{context}: tactic.parameters")
    _require(not parameters, f"{context}: an error record must not carry tactic parameters")
    _require("labels" not in record or not record.get("labels"),
             f"{context}: an error record must not carry labels")
    provenance = _mapping(record.get("provenance"), f"{context}: provenance")
    _require(provenance.get("ok") is False, f"{context}: error record provenance.ok must be false")
    graph_provenance = _mapping(provenance.get("graph"), f"{context}: provenance.graph")
    _require(graph_provenance.get("built") is False,
             f"{context}: error record provenance.graph.built must be false")
    return {
        "ok": False,
        "kind": kind,
        "goals": 0,
        "nodes": 0,
        "premise_table": 0,
        "premise_label_in_table": False,
        "locus_scope": None,
        "locus_count": 0,
        "locus_labelled": False,
        "coupled_groups": 0,
        "coupled_edges": 0,
        "graph_bytes": 0,
        "error": dict(error),
        "convertible": False,
    }


def _fingerprint(parts: Sequence[str]) -> str:
    value = 0xCBF29CE484222325
    for part in parts:
        for byte in part.encode("utf-8"):
            value ^= byte
            value = (value * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return f"{value:016x}"


# ---------------------------------------------------------------------------
# File validation and statistics
# ---------------------------------------------------------------------------


def read_records(path: Path) -> Iterator[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                raise RecordError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(record, dict):
                raise RecordError(f"{path}:{line_no}: not a JSON object")
            record["__line__"] = line_no
            yield record


def validate_paths(paths: Sequence[Path], *, require_graph: bool,
                   strict_labels: bool = False) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    valid: list[dict[str, Any]] = []
    invalid: list[dict[str, Any]] = []
    for path in paths:
        theorem_records = 0
        for record in read_records(path):
            if record.get("record") == "theorem":
                theorem_records += 1
                continue
            if record.get("record") != "step":
                invalid.append({"file": str(path), "line": record.get("__line__"),
                                "error": f"unknown record kind {record.get('record')!r}"})
                continue
            context = f"{path.name}:{record.get('__line__')}:{record.get('theorem')}:step {record.get('step')}"
            try:
                evidence = validate_step_record(record, context=context, strict=strict_labels)
            except RecordError as exc:
                invalid.append({"file": str(path), "line": record.get("__line__"),
                                "error": str(exc)})
                continue
            if require_graph and record.get("error") is not None:
                invalid.append({"file": str(path), "line": record.get("__line__"),
                                "error": "strict mode: step has no graph"})
                continue
            evidence.update({
                "file": str(path),
                "line": record.get("__line__"),
                "theorem": record.get("theorem"),
                "step": record.get("step"),
                "goal_id": record.get("goal_id"),
                "envelope_schema": record.get("schema"),
                "schema_version": record.get("schema_version"),
                "premise_mode": (record.get("provenance") or {}).get("premise", {}).get("mode"),
                "source_bytes": len(json.dumps(record, sort_keys=True, separators=(",", ":")).encode("utf-8")),
            })
            valid.append(evidence)
    return valid, invalid


def summarise(evidence: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    total = len(evidence)
    ok_steps = [row for row in evidence if row["ok"]]
    error_steps = [row for row in evidence if not row["ok"]]
    kinds = Counter(row["kind"] for row in evidence)
    theorem_rows: dict[str, list[Mapping[str, Any]]] = defaultdict(list)
    for row in evidence:
        theorem_rows[str(row.get("theorem"))].append(row)
    premise_steps = [row for row in ok_steps if row["kind"] in ("apply", "motivatedApply", "exact",
                                                               "rewrite", "induction", "unfold")]
    locus_steps = [row for row in ok_steps if row["kind"] in ("rewrite", "generalizeAt")]
    return {
        "steps": total,
        "valid": len(ok_steps),
        "errors": len(error_steps),
        "convertible": sum(1 for row in ok_steps if row["convertible"]),
        "not_convertible": sum(1 for row in ok_steps if not row["convertible"]),
        "error_codes": dict(Counter(row["error"]["code"] for row in error_steps if row["error"])),
        "theorems": len(theorem_rows),
        "envelope_schemas": dict(Counter(row.get("envelope_schema") for row in evidence)),
        "schema_versions": dict(Counter(row.get("schema_version") for row in evidence)),
        "premise_modes": dict(Counter(row.get("premise_mode") for row in evidence)),
        "kinds": dict(kinds),
        "graph_present": len(ok_steps),
        "graph_missing": len(error_steps),
        "graph_bytes": sum(row["graph_bytes"] for row in evidence),
        "source_bytes": sum(row.get("source_bytes", 0) for row in evidence),
        "nodes": sum(row["nodes"] for row in ok_steps),
        "goals": sum(row["goals"] for row in ok_steps),
        "premise_steps": len(premise_steps),
        "premise_table_present": sum(1 for row in premise_steps if row["premise_table"] > 0),
        "premise_label_in_table": sum(1 for row in premise_steps if row["premise_label_in_table"]),
        "premise_label_missing": sum(1 for row in evidence
                                     if row.get("premise_label_missing_reported")),
        "premise_table_entries": sum(row["premise_table"] for row in evidence),
        "locus_steps": len(locus_steps),
        "locus_lists_present": sum(1 for row in locus_steps if row["locus_count"] > 0),
        "locus_labelled": sum(1 for row in locus_steps if row["locus_labelled"]),
        "locus_entries": sum(row["locus_count"] for row in evidence),
        "locus_scope_hypotheses": sum(1 for row in locus_steps if row["locus_scope"] == "hypotheses"),
        "coupled_steps": sum(1 for row in ok_steps if row["coupled_groups"] > 0),
        "coupled_groups": sum(row["coupled_groups"] for row in ok_steps),
        "coupled_edges": sum(row["coupled_edges"] for row in ok_steps),
        "mean_goals_per_state": round(sum(row["goals"] for row in ok_steps) / len(ok_steps), 3) if ok_steps else 0.0,
        "mean_premise_candidates": round(
            sum(row["premise_table"] for row in premise_steps) / len(premise_steps), 3
        ) if premise_steps else 0.0,
        "mean_locus_candidates": round(
            sum(row["locus_count"] for row in locus_steps) / len(locus_steps), 3
        ) if locus_steps else 0.0,
        "mean_bytes_per_step": round(
            sum(row.get("source_bytes", 0) for row in evidence) / total, 1
        ) if total else 0.0,
        "mean_bytes_per_theorem": round(
            sum(row.get("source_bytes", 0) for row in evidence) / len(theorem_rows), 1
        ) if theorem_rows else 0.0,
    }


def render_stats(stats: Mapping[str, Any]) -> str:
    keys = (
        "steps", "valid", "errors", "convertible", "not_convertible", "theorems",
        "graph_present", "graph_missing",
        "kinds", "envelope_schemas", "premise_modes", "premise_steps",
        "premise_table_present", "premise_label_in_table", "premise_label_missing",
        "premise_table_entries",
        "mean_premise_candidates", "locus_steps", "locus_lists_present",
        "locus_labelled", "locus_entries", "mean_locus_candidates",
        "locus_scope_hypotheses", "coupled_steps", "coupled_groups", "coupled_edges",
        "mean_goals_per_state", "mean_bytes_per_step", "mean_bytes_per_theorem",
        "graph_bytes", "source_bytes", "error_codes",
    )
    lines = [f"{key}: {stats.get(key)}" for key in keys]
    return "\n".join(lines)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("paths", nargs="+", type=Path, help="schema-4 steps.jsonl files")
    parser.add_argument("--stats", action="store_true", help="print aggregate statistics")
    parser.add_argument("--json", action="store_true", help="print the report as JSON")
    parser.add_argument("--require-graph", action="store_true",
                        help="strict: a step with an error record counts as invalid")
    parser.add_argument("--require-labels", action="store_true",
                        help="strict: every pointer parameter must have a validated label "
                             "(i.e. the record must be convertible)")
    parser.add_argument("--report", type=Path, default=None,
                        help="write the full report (valid counts + invalid list) as JSON")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    missing = [str(path) for path in args.paths if not path.exists()]
    if missing:
        print(f"missing input files: {missing}", file=sys.stderr)
        return 2
    try:
        valid, invalid = validate_paths(args.paths, require_graph=args.require_graph,
                                       strict_labels=args.require_labels)
    except (RecordError, OSError) as exc:
        print(f"validation aborted: {exc}", file=sys.stderr)
        return 2
    stats = summarise(valid)
    stats["invalid"] = len(invalid)
    report = {"stats": stats, "invalid": invalid}
    if args.report is not None:
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        if args.stats:
            print(render_stats(stats))
        print(f"valid steps: {stats['valid']} / {stats['valid'] + len(invalid)}  "
              f"(invalid {len(invalid)}, convertible {stats['convertible']})")
        for row in invalid[:20]:
            print(f"  INVALID {row['file']}:{row['line']}: {row['error']}")
    return 0 if not invalid else 1


if __name__ == "__main__":
    sys.exit(main())