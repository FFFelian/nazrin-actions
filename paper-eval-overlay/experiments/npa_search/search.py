"""Paper-aligned NPA proof search over the Nazrin string-tactic REPL.

The search never trusts model scores as proof evidence: a theorem is successful
only when the Lean REPL returns ``solved: true`` after a real tactic execution.
Model logits are used exclusively to order candidate tactics.

First-version scope and limitations are documented in ``README.md``:

* premise candidates default to the constants that occur in the current goal
  graph; ``premise_scope="global"`` instead exposes the whole checkpoint
  constant vocabulary, which is still not a definition-graph retrieval index;
* free-variable/locus pointers are decoded over graph-local candidates;
* the model's categorical parameters choose policies (for example an
  occurrence policy), not concrete binder names or arbitrary term syntax;
* tactics that cannot be rendered honestly from these parameters return
  ``None`` instead of a fabricated string.
"""

from __future__ import annotations

import heapq
import math
import re
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Mapping, Sequence

import torch
import torch.nn.functional as F

try:  # package execution and tests
    from experiments.npa_data.convert_trace import NODE_KIND_MAP
    from experiments.paper_aligned_npa import (
        CATEGORY_VALUES,
        CandidateSet,
        ExprGraph,
        NodeKind,
        PremiseCandidates,
        PointerCandidates,
        TACTIC_PARAMETERS,
        TacticKind,
        TacticPrefix,
        tactic_kind_from_name,
        tactic_kind_name,
    )
    from experiments.npa_training.train_npa import load_checkpoint
    from experiments.npa_search.repl_client import ReplClient, ReplError, ReplTimeout
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from experiments.npa_data.convert_trace import NODE_KIND_MAP  # type: ignore
    from experiments.paper_aligned_npa import (  # type: ignore
        CATEGORY_VALUES,
        CandidateSet,
        ExprGraph,
        NodeKind,
        PremiseCandidates,
        PointerCandidates,
        TACTIC_PARAMETERS,
        TacticKind,
        TacticPrefix,
        tactic_kind_from_name,
        tactic_kind_name,
    )
    from experiments.npa_training.train_npa import load_checkpoint  # type: ignore
    from experiments.npa_search.repl_client import (  # type: ignore
        ReplClient,
        ReplError,
        ReplTimeout,
    )


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------

#: Kinds this version can render from the parameter schema.  ``None`` is
#: returned for every other Kind; unsupported Kinds are never approximated by a
#: different tactic.
RENDERABLE_KINDS: frozenset[TacticKind] = frozenset(
    {
        TacticKind.INTRO,
        TacticKind.REVERT,
        TacticKind.APPLY,
        TacticKind.GENERALIZE,
        TacticKind.CASES,
        TacticKind.INDUCTION,
        TacticKind.REWRITE,
        TacticKind.GENERALIZE_AT,
        TacticKind.EXACT,
        TacticKind.CONTRADICTION,
        TacticKind.ASSUMPTION,
        TacticKind.DECIDE,
        TacticKind.RFL,
        TacticKind.INHABIT,
        TacticKind.UNFOLD,
        TacticKind.NORMALIZE,
        TacticKind.REDUCE_BETA,
    }
)


def _as_kind(kind: TacticKind | str) -> TacticKind | None:
    if isinstance(kind, TacticKind):
        return kind
    if isinstance(kind, str):
        try:
            return tactic_kind_from_name(kind)
        except ValueError:
            return None
    return None


def _param(params: Mapping[str, Any], name: str) -> Any | None:
    value = params.get(name)
    if value is None or value == "":
        return None
    return value


def _category(params: Mapping[str, Any], name: str, default: str) -> str:
    """Accept either a category name or its integer class index."""

    value = params.get(name)
    values = CATEGORY_VALUES.get(name, ())
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value < len(values):
        return values[value]
    if isinstance(value, str) and value:
        return value
    return default


# Lean identifiers accepted by the string-tactic parser.  GoalGraphCore uses
# display-only names such as `x#1` for duplicate binders and inaccessible names
# such as `n._@._hyg.4`; those cannot be referenced from a tactic string, so a
# candidate that needs them is skipped rather than rendered as invalid syntax.
_LEAN_IDENTIFIER = re.compile(r"^[A-Za-z_\u00C0-\uFFFF][A-Za-z0-9_'\u00C0-\uFFFF]*$", re.UNICODE)


def _usable_identifier(name: str | None) -> str | None:
    if not isinstance(name, str) or not name or "✝" in name:
        return None
    if not _LEAN_IDENTIFIER.match(name):
        return None
    return name


def _fresh_intro_name(graph: Mapping[str, Any] | None) -> str:
    existing = set()
    if isinstance(graph, Mapping):
        for entry in graph.get("fvars", []):
            if isinstance(entry, Mapping) and isinstance(entry.get("name"), str):
                existing.add(entry["name"])
    base = "h"
    if base not in existing:
        return base
    index = 1
    while f"{base}{index}" in existing:
        index += 1
    return f"{base}{index}"


def _fvar_name(value: Any, graph: Mapping[str, Any] | None) -> str | None:
    if isinstance(value, str):
        return _usable_identifier(value)
    if not isinstance(value, int) or graph is None:
        return None
    for entry in graph.get("fvars", []):
        if isinstance(entry, Mapping) and entry.get("node") == value:
            name = entry.get("name")
            return _usable_identifier(name if isinstance(name, str) else None)
    return None


def _premise_name(value: Any, graph: Mapping[str, Any] | None) -> str | None:
    if isinstance(value, str):
        return value
    if not isinstance(value, int) or graph is None:
        return None
    constants = graph.get("constants", [])
    if 0 <= value < len(constants):
        entry = constants[value]
        if isinstance(entry, Mapping) and isinstance(entry.get("name"), str):
            return entry["name"]
    for node in graph.get("nodes", []):
        if isinstance(node, Mapping) and node.get("id") == value:
            name = node.get("const")
            return name if isinstance(name, str) and name else None
    return None


def _generalize_term(params: Mapping[str, Any]) -> str | None:
    """A concrete term is not part of the NPA parameter schema.

    Callers that already know the pretty-printed subterm may pass ``term`` (or
    ``expr``); otherwise a faithful rendering is impossible and ``None`` is
    returned instead of inventing syntax.
    """

    for key in ("term", "expr"):
        value = params.get(key)
        if isinstance(value, str) and value.strip():
            return value
    return None


def render_tactic(
    kind: TacticKind | str,
    params: Mapping[str, Any] | None = None,
    graph: Mapping[str, Any] | None = None,
) -> str | None:
    """Render one decoded NPA tactic into a Lean string tactic.

    ``params`` values are the *canonical* parameter values:

    * ``premise``: a constant name (an integer graph-constant index is also
      accepted for convenience),
    * ``free_variable``: an fvar display name (or graph-local FVAR node index),
    * ``locus``: a ``SubExpr.Pos`` string (or graph-local node index),
    * categorical parameters: a class name from ``CATEGORY_VALUES``.

    Returns ``None`` when this version cannot produce an honest tactic string.
    """

    params = {} if params is None else params
    kind_enum = _as_kind(kind)
    if kind_enum is None or kind_enum not in RENDERABLE_KINDS:
        return None

    if kind_enum == TacticKind.INTRO:
        name_mode = _category(params, "name_mode", "auto")
        name = _param(params, "name")
        if name_mode == "anonymous":
            return "intro _"
        if name_mode == "explicit":
            # The NPA schema chooses the naming *policy*, not a concrete
            # binder name.  Generate a deterministic fresh name so later
            # pointer tactics can refer to the introduced fvar; otherwise
            # Lean creates inaccessible names (`n✝`) that cannot be rendered
            # into a follow-up tactic string.
            chosen = _usable_identifier(name if isinstance(name, str) else None)
            return f"intro {chosen or _fresh_intro_name(graph)}"
        # `auto` leaves freshness to Lean.
        return "intro"

    if kind_enum == TacticKind.REVERT:
        name = _fvar_name(_param(params, "free_variable"), graph)
        return f"revert {name}" if name else None

    if kind_enum == TacticKind.APPLY:
        name = _premise_name(_param(params, "premise"), graph)
        return f"apply {name}" if name else None

    if kind_enum == TacticKind.GENERALIZE:
        # Standard `generalize` needs a term to abstract.  The NPA schema has
        # name/locus but no term string; only an explicitly supplied term is
        # renderable.
        term = _generalize_term(params)
        if term is None:
            return None
        name = _param(params, "name")
        binder = name if isinstance(name, str) and name else "h"
        return f"generalize {binder} : {term} = _"

    if kind_enum == TacticKind.CASES:
        name = _fvar_name(_param(params, "free_variable"), graph)
        return f"cases {name}" if name else None

    if kind_enum == TacticKind.INDUCTION:
        name = _fvar_name(_param(params, "free_variable"), graph)
        if name is None:
            return None
        mode = _category(params, "induction_mode", "ordinary")
        if mode == "cases":
            return f"cases {name}"
        if mode == "using":
            # The NPA induction parameter head names the recursor in
            # `premise`; keep accepting the older `recursor`/`using` aliases for
            # callers that predate that schema.
            recursor_value = _param(params, "premise")
            if recursor_value is None:
                recursor_value = _param(params, "recursor")
            if recursor_value is None:
                recursor_value = _param(params, "using")
            recursor = _premise_name(recursor_value, graph)
            if not isinstance(recursor, str) or not recursor:
                return None
            return f"induction {name} using {recursor}"
        return f"induction {name}"

    if kind_enum == TacticKind.REWRITE:
        name = _premise_name(_param(params, "premise"), graph)
        if name is None:
            return None
        direction = _category(params, "direction", "forward")
        arrow = "← " if direction == "backward" else ""
        # Occurrence and locus policies are not representable in standard
        # `rw` syntax without `nth_rewrite`; the first version rewrites all
        # occurrences.  The parameter is still decoded and recorded.
        return f"rw [{arrow}{name}]"

    if kind_enum == TacticKind.GENERALIZE_AT:
        # `generalizeAt` in Nazrin is an atomic tactic over a concrete
        # position.  Standard Lean requires the pretty-printed subterm, which
        # is not part of the graph/parameter schema here.
        term = _generalize_term(params)
        if term is None:
            return None
        name = _param(params, "name")
        binder = name if isinstance(name, str) and name else "h"
        hypothesis = _fvar_name(_param(params, "free_variable"), graph)
        suffix = f" at {hypothesis}" if hypothesis else ""
        return f"generalize {binder} : {term} = _{suffix}"

    if kind_enum == TacticKind.EXACT:
        name = _premise_name(_param(params, "premise"), graph)
        return f"exact {name}" if name else None

    if kind_enum == TacticKind.CONTRADICTION:
        return "contradiction"
    if kind_enum == TacticKind.ASSUMPTION:
        return "assumption"
    if kind_enum == TacticKind.DECIDE:
        return "decide"
    if kind_enum == TacticKind.RFL:
        return "rfl"
    if kind_enum == TacticKind.INHABIT:
        # `inhabit` is a Mathlib tactic.  It is a real tactic in Mathlib
        # projects; under Init/Pantograph alone the REPL reports a parse
        # failure, which the search records as a failed candidate.
        return "inhabit"

    if kind_enum == TacticKind.UNFOLD:
        name = _premise_name(_param(params, "premise"), graph)
        if name is None:
            return None
        target_mode = _category(params, "target_mode", "goal")
        if target_mode in ("hypotheses", "all"):
            return f"unfold {name} at *"
        return f"unfold {name}"

    if kind_enum == TacticKind.NORMALIZE:
        target_mode = _category(params, "target_mode", "goal")
        if target_mode in ("hypotheses", "all"):
            return "simp at *"
        return "simp"

    if kind_enum == TacticKind.REDUCE_BETA:
        # Mathlib's `beta_reduce`; under Init it is unavailable and is
        # recorded as a failed candidate rather than silently replaced.
        target_mode = _category(params, "target_mode", "goal")
        if target_mode in ("hypotheses", "all"):
            return "beta_reduce at *"
        return "beta_reduce"

    return None


# ---------------------------------------------------------------------------
# REPL graph -> ExprGraph tensors
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class GraphView:
    """Tensor graph plus the candidate indices used for pointer decoding."""

    graph: ExprGraph
    constant_names: tuple[str, ...]
    fvar_names: Mapping[int, str]
    locus_positions: Mapping[int, str]
    warnings: tuple[str, ...] = ()

    @property
    def fvar_nodes(self) -> tuple[int, ...]:
        return tuple(self.fvar_names)

    @property
    def locus_nodes(self) -> tuple[int, ...]:
        return tuple(self.locus_positions)


def _node_features(
    nodes: Sequence[Mapping[str, Any]],
    edges: Sequence[Mapping[str, Any]],
    root: int,
    width: int,
) -> list[list[float]]:
    out_degree: dict[int, int] = {}
    for edge in edges:
        source = edge.get("src", edge.get("source"))
        if isinstance(source, int):
            out_degree[source] = out_degree.get(source, 0) + 1
    max_depth = max((int(node.get("depth", 0)) for node in nodes), default=0)
    max_children = max(out_degree.values(), default=0)
    rows: list[list[float]] = []
    for index, node in enumerate(nodes):
        depth = int(node.get("depth", 0))
        base = [
            depth / max_depth if max_depth > 0 else 0.0,
            1.0 if index == root else 0.0,
            out_degree.get(index, 0) / max_children if max_children > 0 else 0.0,
        ]
        if width <= len(base):
            row = base[:width]
        else:
            row = base + [0.0] * (width - len(base))
        rows.append(row)
    return rows


def graph_to_exprgraph(
    goal_graph: Mapping[str, Any],
    vocab: Any,
    device: str | torch.device = "cpu",
) -> GraphView:
    """Convert a REPL goal graph (schema v1) into an ``ExprGraph`` tensor.

    Unknown constants use the model's unseen-constant path (``constant_id=-1``)
    and unknown edge relations are dropped, because the checkpoint's relation
    vocabulary is a fixed index space.  Both events are reported in
    ``GraphView.warnings``.
    """

    if not isinstance(goal_graph, Mapping):
        raise ValueError("goal graph must be an object")
    if goal_graph.get("schema") != 1:
        raise ValueError(f"unsupported goal graph schema: {goal_graph.get('schema')!r}")
    nodes = goal_graph.get("nodes")
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("goal graph has no nodes")
    root = goal_graph.get("root")
    if not isinstance(root, int) or isinstance(root, bool) or not 0 <= root < len(nodes):
        raise ValueError(f"goal graph root {root!r} is outside the node range")

    constant_lookup = {name: index for index, name in enumerate(vocab.constants)}
    node_kinds: list[int] = []
    constant_ids: list[int] = []
    warnings: list[str] = []
    unknown_constants: list[str] = []
    for index, node in enumerate(nodes):
        if not isinstance(node, Mapping):
            raise ValueError(f"goal graph node {index} is not an object")
        raw_kind = str(node.get("kind", ""))
        mapped = NODE_KIND_MAP.get(raw_kind)
        if mapped is None:
            raise ValueError(f"goal graph node {index} has unknown kind {raw_kind!r}")
        kind = NodeKind[mapped]
        node_kinds.append(int(kind))
        if kind == NodeKind.CONST:
            name = node.get("const")
            if isinstance(name, str) and name in constant_lookup:
                constant_ids.append(constant_lookup[name])
            else:
                constant_ids.append(-1)
                if isinstance(name, str) and name and name not in unknown_constants:
                    unknown_constants.append(name)
        else:
            constant_ids.append(-1)

    edges_raw = goal_graph.get("edges", [])
    if not isinstance(edges_raw, list):
        raise ValueError("goal graph edges must be a list")
    sources: list[int] = []
    targets: list[int] = []
    edge_types: list[int] = []
    dropped_relations: list[str] = []
    relation_lookup = {name: index for index, name in enumerate(vocab.relations)}
    for edge_index, edge in enumerate(edges_raw):
        if not isinstance(edge, Mapping):
            raise ValueError(f"goal graph edge {edge_index} is not an object")
        source = edge.get("src", edge.get("source"))
        target = edge.get("dst", edge.get("target"))
        relation = edge.get("type")
        if not isinstance(source, int) or not isinstance(target, int):
            raise ValueError(f"goal graph edge {edge_index} has non-integer endpoints")
        if not 0 <= source < len(nodes) or not 0 <= target < len(nodes):
            raise ValueError(f"goal graph edge {edge_index} is outside the node range")
        if not isinstance(relation, str) or not relation:
            raise ValueError(f"goal graph edge {edge_index} has no relation name")
        relation_id = relation_lookup.get(relation)
        if relation_id is None:
            if relation not in dropped_relations:
                dropped_relations.append(relation)
            continue
        sources.append(source)
        targets.append(target)
        edge_types.append(relation_id)

    features = _node_features(nodes, edges_raw, root, vocab.node_feature_dim)
    resolved_device = torch.device(device)
    graph = ExprGraph(
        node_kinds=torch.tensor(node_kinds, dtype=torch.long, device=resolved_device),
        edge_index=torch.tensor([sources, targets], dtype=torch.long, device=resolved_device)
        if sources
        else torch.empty((2, 0), dtype=torch.long, device=resolved_device),
        edge_types=torch.tensor(edge_types, dtype=torch.long, device=resolved_device),
        constant_ids=torch.tensor(constant_ids, dtype=torch.long, device=resolved_device),
        node_features=torch.tensor(features, dtype=torch.float32, device=resolved_device).reshape(
            len(nodes), vocab.node_feature_dim
        ),
    )
    graph.validate(vocab.node_feature_dim)

    declared_constants: list[str] = []
    for entry in goal_graph.get("constants", []):
        name = entry.get("name") if isinstance(entry, Mapping) else entry
        if isinstance(name, str) and name:
            declared_constants.append(name)
    for node in nodes:
        if isinstance(node, Mapping) and isinstance(node.get("const"), str):
            declared_constants.append(node["const"])
    constant_names: list[str] = []
    for name in declared_constants:
        if name in constant_lookup and name not in constant_names:
            constant_names.append(name)

    fvar_names: dict[int, str] = {}
    for entry in goal_graph.get("fvars", []):
        if not isinstance(entry, Mapping):
            continue
        name = entry.get("name")
        node_index = entry.get("node")
        if isinstance(name, str) and name and isinstance(node_index, int):
            fvar_names[node_index] = name
    locus_positions: dict[int, str] = {}
    for entry in goal_graph.get("loci", []):
        if not isinstance(entry, Mapping):
            continue
        node_index = entry.get("node")
        position = entry.get("position")
        if isinstance(node_index, int) and isinstance(position, str):
            locus_positions.setdefault(node_index, "root" if position == "" else position)

    if unknown_constants:
        warnings.append(
            f"{len(unknown_constants)} constant(s) outside checkpoint vocabulary use the unseen-constant path: "
            + ", ".join(unknown_constants[:8])
        )
    if dropped_relations:
        warnings.append("dropped edge relations outside checkpoint vocabulary: " + ", ".join(dropped_relations))
    return GraphView(
        graph=graph,
        constant_names=tuple(constant_names),
        fvar_names=fvar_names,
        locus_positions=locus_positions,
        warnings=tuple(warnings),
    )


#: Supported ``premise_scope`` values.  ``graph`` keeps the first-version
#: behavior; ``global`` exposes every constant in the checkpoint vocabulary.
PREMISE_SCOPES: tuple[str, ...] = ("graph", "global")


def build_candidate_set(
    view: GraphView,
    vocab: Any,
    device: str | torch.device = "cpu",
    premise_scope: str = "graph",
) -> CandidateSet:
    """Build candidate sources for pointer decoding.

    * ``premise`` with ``premise_scope="graph"``: graph constants present in
      the checkpoint vocabulary (first-version behavior);
    * ``premise`` with ``premise_scope="global"``: every constant ID in the
      checkpoint vocabulary (``0..len(vocab.constants)-1``), all eligible.
      This approximates global premise retrieval but is *not* a definition-graph
      fixed-point encoding: constants outside the checkpoint vocabulary still
      cannot be proposed;
    * ``free_variable``: FVAR graph nodes (always graph-local);
    * ``locus``: graph locus nodes (always graph-local, deduplicated by node id).
    """

    if premise_scope not in PREMISE_SCOPES:
        raise ValueError(
            f"unknown premise_scope {premise_scope!r}; expected one of {', '.join(PREMISE_SCOPES)}"
        )

    resolved_device = torch.device(device)
    constant_lookup = {name: index for index, name in enumerate(vocab.constants)}
    if premise_scope == "graph":
        premise_ids = [constant_lookup[name] for name in view.constant_names if name in constant_lookup]
    else:
        constant_count = len(vocab.constants)
        if constant_count == 0:
            raise ValueError(
                "premise_scope='global' requires a non-empty checkpoint constant vocabulary"
            )
        premise_ids = list(range(constant_count))
    fvar_nodes = list(view.fvar_nodes)
    locus_nodes = list(view.locus_nodes)
    return CandidateSet(
        premise=PremiseCandidates(
            constant_ids=torch.tensor(premise_ids, dtype=torch.long, device=resolved_device),
            mask=torch.tensor([True] * len(premise_ids), dtype=torch.bool, device=resolved_device),
        ),
        free_variable=PointerCandidates(
            indices=torch.tensor(fvar_nodes, dtype=torch.long, device=resolved_device),
            mask=torch.tensor([True] * len(fvar_nodes), dtype=torch.bool, device=resolved_device),
        ),
        locus=PointerCandidates(
            indices=torch.tensor(locus_nodes, dtype=torch.long, device=resolved_device),
            mask=torch.tensor([True] * len(locus_nodes), dtype=torch.bool, device=resolved_device),
        ),
    )


# ---------------------------------------------------------------------------
# Policies
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class TacticProposal:
    tactic: str
    score: float
    kind: str | None = None
    parameters: Mapping[str, str] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        return {
            "tactic": self.tactic,
            "score": self.score,
            "kind": self.kind,
            "parameters": dict(self.parameters),
        }


def coerce_proposals(items: Any) -> list[TacticProposal]:
    """Accept proposals, ``(tactic, score)`` pairs, strings, or dicts.

    The abstract API returns :class:`TacticProposal`, but accepting the common
    lightweight forms keeps custom test policies and notebooks ergonomic.
    """

    if items is None:
        return []
    if isinstance(items, (TacticProposal, str, tuple, dict)):
        items = [items]
    proposals: list[TacticProposal] = []
    for item in items:
        if isinstance(item, TacticProposal):
            proposals.append(item)
        elif isinstance(item, str):
            if item.strip():
                proposals.append(TacticProposal(tactic=item, score=0.0))
        elif isinstance(item, dict):
            tactic = item.get("tactic")
            if isinstance(tactic, str) and tactic.strip():
                proposals.append(
                    TacticProposal(
                        tactic=tactic,
                        score=float(item.get("score", 0.0)),
                        kind=item.get("kind"),
                        parameters=item.get("parameters", {}) or {},
                    )
                )
        elif isinstance(item, (tuple, list)) and len(item) >= 2:
            tactic, score = item[0], item[1]
            if isinstance(tactic, str) and tactic.strip():
                proposals.append(TacticProposal(tactic=tactic, score=float(score)))
    return proposals


class TacticPolicy(ABC):
    """Interface for a tactic proposal source."""

    #: Short label used by evaluation summaries.
    name: str = "policy"

    @abstractmethod
    def propose(
        self,
        goal_graph: Mapping[str, Any] | None,
        goal_id: int | str,
        top_k: int = 5,
    ) -> list[TacticProposal]:
        """Return at most ``top_k`` tactic strings ordered by decreasing score."""


class MockPolicy(TacticPolicy):
    """Deterministic fixed-sequence policy for tests and CLI smoke runs."""

    name = "mock"

    def __init__(self, tactics: Sequence[str]) -> None:
        self.tactics = [tactic for tactic in tactics if isinstance(tactic, str) and tactic.strip()]
        self._index = 0

    def reset(self, theorem: str | None = None) -> None:
        self._index = 0

    def propose(
        self,
        goal_graph: Mapping[str, Any] | None,
        goal_id: int | str,
        top_k: int = 5,
    ) -> list[TacticProposal]:
        if self._index >= len(self.tactics):
            return []
        tactic = self.tactics[self._index]
        self._index += 1
        return [TacticProposal(tactic=tactic, score=1.0, kind="mock")]


def _eligible_kind(kind: TacticKind, candidates: CandidateSet) -> bool:
    """Whether every pointer head required by ``kind`` has candidates."""

    for parameter in TACTIC_PARAMETERS[kind]:
        if parameter == "premise":
            if candidates.premise.constant_ids.numel() == 0:
                return False
        elif parameter == "free_variable":
            if candidates.free_variable.indices.numel() == 0:
                return False
        elif parameter == "locus":
            if candidates.locus.indices.numel() == 0:
                return False
    return True


def _top_log_probs(logits: torch.Tensor, k: int) -> list[tuple[int, float]]:
    if logits.numel() == 0:
        return []
    values, indices = torch.topk(logits, k=min(k, logits.numel()))
    result: list[tuple[int, float]] = []
    for value, index in zip(values.tolist(), indices.tolist()):
        if math.isfinite(float(value)):
            result.append((int(index), float(value)))
    return result


class NPAPolicy(TacticPolicy):
    """Decode Kind + parameter prefixes from a trained NPA checkpoint.

    The policy is deliberately a proposal source, not a verifier.  Its scores
    are average log-probabilities and have no bearing on proof success.
    """

    name = "npa"

    def __init__(
        self,
        checkpoint: str | Path,
        device: str | torch.device = "cpu",
        *,
        kind_budget: int = 12,
        premise_scope: str = "graph",
    ) -> None:
        if premise_scope not in PREMISE_SCOPES:
            raise ValueError(
                f"unknown premise_scope {premise_scope!r}; expected one of {', '.join(PREMISE_SCOPES)}"
            )
        self.checkpoint = Path(checkpoint)
        self.model, self.vocab, self.payload = load_checkpoint(self.checkpoint, device)
        self.model.eval()
        self.device = next(self.model.parameters()).device
        self.kind_budget = max(1, int(kind_budget))
        self.premise_scope = premise_scope

    # -- inference ------------------------------------------------------
    def propose(
        self,
        goal_graph: Mapping[str, Any] | None,
        goal_id: int | str,
        top_k: int = 5,
    ) -> list[TacticProposal]:
        if not isinstance(goal_graph, Mapping):
            return []
        top_k = max(1, int(top_k))
        view = graph_to_exprgraph(goal_graph, self.vocab, self.device)
        candidates = build_candidate_set(
            view, self.vocab, self.device, premise_scope=self.premise_scope
        )
        graph = view.graph

        with torch.no_grad():
            kind_logits = self.model.forward(graph, candidates).kind_logits.detach().float().cpu()
            kind_log_probs = F.log_softmax(kind_logits, dim=-1)

        # Consider a wider kind set than top_k because some Kind heads may be
        # unrenderable or lack pointer candidates.  Never let a low Kind
        # probability turn into a fabricated tactic.
        ranked_kinds = sorted(range(kind_log_probs.numel()), key=lambda index: float(kind_log_probs[index]), reverse=True)
        per_kind: list[list[TacticProposal]] = []
        evaluated = 0
        for kind_index in ranked_kinds:
            try:
                kind = TacticKind(kind_index)
            except ValueError:
                continue
            if kind not in RENDERABLE_KINDS or kind in (TacticKind.OTHER, TacticKind.ABANDON):
                continue
            if not _eligible_kind(kind, candidates):
                continue
            if evaluated >= self.kind_budget:
                break
            evaluated += 1
            decoded = self._decode_kind(
                kind=kind,
                kind_log_prob=float(kind_log_probs[kind_index]),
                graph=graph,
                goal_graph=goal_graph,
                candidates=candidates,
                view=view,
                top_k=top_k,
            )
            decoded.sort(key=lambda proposal: proposal.score, reverse=True)
            if decoded:
                per_kind.append(decoded)

        # Round-robin across Kind families before taking a second (or later)
        # tactic from the same family.  A greedy global top-k would otherwise
        # return five `rw` variants while never trying `rfl` or `exact`.
        proposals: list[TacticProposal] = []
        seen_tactics: set[str] = set()
        rounds = max((len(items) for items in per_kind), default=0)
        for round_index in range(rounds):
            batch = [items[round_index] for items in per_kind if round_index < len(items)]
            batch.sort(key=lambda proposal: proposal.score, reverse=True)
            for proposal in batch:
                if proposal.tactic in seen_tactics:
                    continue
                seen_tactics.add(proposal.tactic)
                proposals.append(proposal)
                if len(proposals) >= top_k:
                    return proposals
        return proposals[:top_k]

    def _decode_kind(
        self,
        *,
        kind: TacticKind,
        kind_log_prob: float,
        graph: ExprGraph,
        goal_graph: Mapping[str, Any],
        candidates: CandidateSet,
        view: GraphView,
        top_k: int,
    ) -> list[TacticProposal]:
        sequence = TACTIC_PARAMETERS[kind]
        try:
            with torch.no_grad():
                output = self.model.forward_prefix(
                    graph,
                    candidates,
                    TacticPrefix(kind),
                    parameters=list(sequence),
                )
                parameter_log_probs = {
                    name: F.log_softmax(logits.detach().float().cpu(), dim=-1)
                    for name, logits in output.parameter_logits.items()
                }
        except (ValueError, RuntimeError):
            return []

        # Beam search over the independent parameter heads.  The model does
        # not condition later heads on earlier values, but a beam still gives
        # several complete different tactic strings.
        beam: list[tuple[dict[str, int], float]] = [({}, 0.0)]
        for parameter in sequence:
            log_probs = parameter_log_probs.get(parameter)
            if log_probs is None:
                return []
            choices = _top_log_probs(log_probs, max(top_k, 3))
            if not choices:
                return []
            expanded: list[tuple[dict[str, int], float]] = []
            for selected, score in beam:
                for index, value in choices:
                    next_selected = dict(selected)
                    next_selected[parameter] = index
                    expanded.append((next_selected, score + value))
            expanded.sort(key=lambda item: item[1], reverse=True)
            beam = expanded[: max(top_k, 3)]

        proposals: list[TacticProposal] = []
        seen: set[str] = set()
        for selected, parameter_score in beam:
            canonical: dict[str, Any] = {}
            for parameter, index in selected.items():
                value = self._canonical_value(parameter, index, candidates, view)
                if value is None:
                    canonical = {}
                    break
                canonical[parameter] = value
            if not canonical and sequence:
                continue
            # Canonical values are already strings (constant/fvar names and
            # locus positions), so rendering does not need the raw graph.
            tactic = render_tactic(kind, canonical, graph=goal_graph)
            if tactical_is_forbidden(tactic):
                continue
            if tactic is None or tactic in seen:
                continue
            seen.add(tactic)
            total = kind_log_prob + parameter_score
            score = total / (1 + len(sequence)) if sequence else kind_log_prob
            proposals.append(
                TacticProposal(
                    tactic=tactic,
                    score=score,
                    kind=tactic_kind_name(kind),
                    parameters={name: str(value) for name, value in canonical.items()},
                )
            )
        return proposals

    def _canonical_value(
        self,
        parameter: str,
        index: int,
        candidates: CandidateSet,
        view: GraphView,
    ) -> Any | None:
        if parameter == "premise":
            ids = candidates.premise.constant_ids
            if not 0 <= index < ids.numel():
                return None
            constant_id = int(ids[index])
            if 0 <= constant_id < len(self.vocab.constants):
                return self.vocab.constants[constant_id]
            return None
        if parameter == "free_variable":
            indices = candidates.free_variable.indices
            if not 0 <= index < indices.numel():
                return None
            node = int(indices[index])
            return view.fvar_names.get(node)
        if parameter == "locus":
            indices = candidates.locus.indices
            if not 0 <= index < indices.numel():
                return None
            node = int(indices[index])
            return view.locus_positions.get(node)
        values = CATEGORY_VALUES.get(parameter)
        if values is None or not 0 <= index < len(values):
            return None
        return values[index]


def tactical_is_forbidden(tactic: str | None) -> bool:
    """Reject proof shortcuts that are not real proofs for evaluation."""

    if not tactic:
        return True
    return re.search(r"\b(sorry|admit)\b", tactic) is not None


# ---------------------------------------------------------------------------
# Search
# ---------------------------------------------------------------------------


def _is_timeout_error(error: BaseException) -> bool:
    """Class-name fallback handles a directly-imported duplicate module."""

    return isinstance(error, ReplTimeout) or error.__class__.__name__ == "ReplTimeout"


@dataclass
class SearchResult:
    theorem: str
    status: str
    elapsed_ms: float
    steps: int
    tactic_path: list[str] = field(default_factory=list)
    error: str | None = None
    expansions: int = 0
    failures: list[dict[str, Any]] = field(default_factory=list)
    policy: str = "policy"

    def to_dict(self) -> dict[str, Any]:
        return {
            "theorem": self.theorem,
            "status": self.status,
            "elapsed_ms": self.elapsed_ms,
            "steps": self.steps,
            "tactic_path": list(self.tactic_path),
            "error": self.error,
            "expansions": self.expansions,
            "policy": self.policy,
            "failures": list(self.failures),
        }


@dataclass(order=True)
class _FrontierNode:
    priority: float
    order: int
    depth: int = field(compare=False)
    snapshot: str = field(compare=False)
    path: tuple[str, ...] = field(compare=False)
    cumulative_score: float = field(compare=False)


class SearchEngine:
    """Best-first / DFS proof search driven by a ``TacticPolicy``.

    Each theorem gets a wall-clock budget (default 15 s) and a hard cap on
    tactic attempts (default 100).  Branching uses the REPL's snapshot/restore
    commands.  A branch is successful only when the REPL says ``solved:true``.
    """

    def __init__(
        self,
        client: ReplClient,
        policy: TacticPolicy,
        *,
        time_limit: float = 15.0,
        max_steps: int = 100,
        top_k: int = 5,
        strategy: str = "best-first",
        max_failures: int = 200,
    ) -> None:
        if time_limit <= 0:
            raise ValueError("time_limit must be positive")
        if max_steps < 1:
            raise ValueError("max_steps must be positive")
        if top_k < 1:
            raise ValueError("top_k must be positive")
        if strategy not in ("best-first", "dfs"):
            raise ValueError("strategy must be 'best-first' or 'dfs'")
        self.client = client
        self.policy = policy
        self.time_limit = float(time_limit)
        self.max_steps = int(max_steps)
        self.top_k = int(top_k)
        self.strategy = strategy
        self.max_failures = int(max_failures)

    def prove(self, theorem: str) -> SearchResult:
        started = time.monotonic()
        deadline = started + self.time_limit
        failures: list[dict[str, Any]] = []
        steps = 0
        expansions = 0
        snapshot_counter = 0
        policy_name = getattr(self.policy, "name", self.policy.__class__.__name__)

        def result(status: str, path: Sequence[str], error: str | None = None) -> SearchResult:
            return SearchResult(
                theorem=theorem,
                status=status,
                elapsed_ms=(time.monotonic() - started) * 1000.0,
                steps=steps,
                tactic_path=list(path),
                error=error,
                expansions=expansions,
                failures=failures[-self.max_failures :],
                policy=policy_name,
            )

        reset = getattr(self.policy, "reset", None)
        if callable(reset):
            reset(theorem)

        try:
            start_response = self.client.start_theorem(theorem)
        except Exception as exc:  # transport/protocol failure
            if _is_timeout_error(exc):
                return result("timeout", [], "REPL timed out while starting the theorem")
            return result("error", [], f"could not start theorem: {exc}")
        if start_response.get("status") != "ok":
            return result(
                "error",
                [],
                f"start failed: {start_response.get('kind', 'error')}: "
                f"{start_response.get('message', start_response)}",
            )
        initial_goals = start_response.get("goals", [])
        if not initial_goals and start_response.get("solved"):
            return result("success", [])

        def new_snapshot() -> str:
            nonlocal snapshot_counter
            name = f"search{snapshot_counter}"
            snapshot_counter += 1
            response = self.client.snapshot(name)
            if response.get("status") != "ok":
                raise ReplError(f"snapshot failed: {response}")
            return name

        try:
            root_snapshot = new_snapshot()
        except (ReplError, Exception) as exc:
            return result("error", [], f"could not snapshot the initial state: {exc}")

        frontier: list[_FrontierNode] = []
        order = 0

        def push(snapshot: str, path: tuple[str, ...], depth: int, score: float) -> None:
            nonlocal order
            # `heapq` is a min-heap.  Best-first negates the average
            # log-probability so the best branch has the smallest key; DFS
            # negates depth so the deepest branch is expanded first.
            if self.strategy == "best-first":
                priority = -(score / max(1, depth))
            else:
                priority = -float(depth)
            heapq.heappush(frontier, _FrontierNode(priority, order, depth, snapshot, path, score))
            order += 1

        push(root_snapshot, (), 0, 0.0)

        while frontier:
            if time.monotonic() >= deadline:
                return result("timeout", frontier[0].path, f"time limit {self.time_limit:.1f}s exceeded")
            if steps >= self.max_steps:
                return result("failure", frontier[0].path, f"max steps ({self.max_steps}) reached")

            node = heapq.heappop(frontier)
            expansions += 1
            try:
                restored = self.client.restore(node.snapshot)
            except Exception as exc:
                if _is_timeout_error(exc):
                    return result("timeout", node.path, "REPL timed out while restoring a branch")
                return result("error", node.path, f"restore failed: {exc}")
            if restored.get("status") != "ok":
                return result("error", node.path, f"restore failed: {restored}")
            if restored.get("solved"):
                return result("success", node.path)
            goals = restored.get("goals", [])
            if not goals:
                failures.append(
                    {"step": steps, "tactic": None, "goal_id": None, "reason": "state has no goals but is not solved"}
                )
                continue
            goal = goals[0]
            goal_id = goal.get("id")
            try:
                proposals = coerce_proposals(self.policy.propose(goal.get("graph"), goal_id, self.top_k))
            except (ReplError, Exception) as exc:
                failures.append(
                    {
                        "step": steps,
                        "tactic": None,
                        "goal_id": goal_id,
                        "reason": f"policy error: {exc}",
                    }
                )
                continue
            if not proposals:
                failures.append(
                    {
                        "step": steps,
                        "tactic": None,
                        "goal_id": goal_id,
                        "reason": "policy returned no candidate tactics",
                    }
                )
                continue

            for proposal in proposals:
                if time.monotonic() >= deadline:
                    return result("timeout", node.path, f"time limit {self.time_limit:.1f}s exceeded")
                if steps >= self.max_steps:
                    return result("failure", node.path, f"max steps ({self.max_steps}) reached")
                tactic = proposal.tactic
                if tactical_is_forbidden(tactic):
                    failures.append(
                        {
                            "step": steps,
                            "tactic": tactic,
                            "goal_id": goal_id,
                            "reason": "forbidden tactic (sorry/admit)",
                        }
                    )
                    continue
                try:
                    restored = self.client.restore(node.snapshot)
                except Exception as exc:
                    if _is_timeout_error(exc):
                        return result("timeout", node.path, "REPL timed out while restoring a branch")
                    return result("error", node.path, f"restore failed: {exc}")
                if restored.get("status") != "ok":
                    return result("error", node.path, f"restore failed: {restored}")
                steps += 1
                try:
                    remaining = max(0.01, deadline - time.monotonic())
                    previous_timeout = getattr(self.client, "timeout", None)
                    if previous_timeout is not None:
                        self.client.timeout = min(float(previous_timeout), remaining)
                    try:
                        response = self.client.apply(goal_id, tactic)
                    finally:
                        if previous_timeout is not None:
                            self.client.timeout = previous_timeout
                except Exception as exc:
                    if _is_timeout_error(exc):
                        return result("timeout", node.path, f"tactic exceeded the {self.time_limit:.1f}s budget: {tactic}")
                    failures.append(
                        {"step": steps, "tactic": tactic, "goal_id": goal_id, "reason": f"REPL error: {exc}"}
                    )
                    return result("error", node.path, f"REPL error after {tactic!r}: {exc}")

                if response.get("status") != "ok":
                    failures.append(
                        {
                            "step": steps,
                            "tactic": tactic,
                            "goal_id": goal_id,
                            "kind": response.get("kind"),
                            "reason": response.get("message", "tactic failed"),
                        }
                    )
                    continue
                path = node.path + (tactic,)
                if response.get("solved"):
                    return result("success", path)
                if not response.get("goals"):
                    failures.append(
                        {
                            "step": steps,
                            "tactic": tactic,
                            "goal_id": goal_id,
                            "reason": "apply reported no goals but solved is false",
                        }
                    )
                    continue
                try:
                    child_snapshot = new_snapshot()
                except (ReplError, Exception) as exc:
                    return result("error", path, f"could not snapshot child state: {exc}")
                push(child_snapshot, path, node.depth + 1, node.cumulative_score + proposal.score)

        last_reason = failures[-1]["reason"] if failures else "search exhausted"
        return result("failure", [], f"no proof found; last failure: {last_reason}")
