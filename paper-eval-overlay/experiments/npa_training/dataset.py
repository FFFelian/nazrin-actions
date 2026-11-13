"""JSONL dataset loader and synthetic generator for the parameterized NPA.

The real ExprGraph exporter is a separate workstream.  This module therefore
defines the first-version JSONL contract used by the training/evaluation
scripts.  It is intentionally strict: every tensor index and every candidate
mask is validated before an example reaches the model, and tactics whose
parameters cannot be represented by the current pointer/categorical schema are
rejected or bucketed into ``TacticKind.OTHER`` (see README).

Only the Python standard library and PyTorch are used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

import torch

try:  # Support both ``python -m experiments.npa_training...`` and direct runs.
    from experiments.paper_aligned_npa import (
        CATEGORY_VALUES,
        CandidateSet,
        ExprGraph,
        NodeKind,
        POINTER_PARAMETERS,
        PremiseCandidates,
        PointerCandidates,
        TACTIC_PARAMETERS,
        TacticKind,
        tactic_kind_from_name,
        tactic_kind_name,
    )
except ModuleNotFoundError:  # pragma: no cover - exercised by direct CLI use
    import sys

    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from experiments.paper_aligned_npa import (
        CATEGORY_VALUES,
        CandidateSet,
        ExprGraph,
        NodeKind,
        POINTER_PARAMETERS,
        PremiseCandidates,
        PointerCandidates,
        TACTIC_PARAMETERS,
        TacticKind,
        tactic_kind_from_name,
        tactic_kind_name,
    )


GRAPH_SCHEMA_VERSION = 1
SPLIT_NAMES = ("train", "validation", "test")


class DatasetError(ValueError):
    """Raised when a JSONL record violates the dataset contract."""


@dataclass(frozen=True)
class DatasetVocab:
    """Global vocabularies and feature width shared by a dataset/checkpoint."""

    constants: tuple[str, ...]
    relations: tuple[str, ...]
    node_feature_dim: int

    def __post_init__(self) -> None:
        if self.node_feature_dim < 1:
            raise DatasetError("node_feature_dim must be positive")
        if len(set(self.constants)) != len(self.constants):
            raise DatasetError("constant vocabulary contains duplicates")
        if len(set(self.relations)) != len(self.relations):
            raise DatasetError("relation vocabulary contains duplicates")

    def constant_id(self, name: str) -> int:
        try:
            return self.constants.index(name)
        except ValueError as exc:
            raise DatasetError(f"constant {name!r} is outside the dataset vocabulary") from exc

    def relation_id(self, name: str) -> int:
        try:
            return self.relations.index(name)
        except ValueError as exc:
            raise DatasetError(f"relation {name!r} is outside the dataset vocabulary") from exc

    def to_json(self) -> dict[str, Any]:
        return {
            "constants": list(self.constants),
            "relations": list(self.relations),
            "node_feature_dim": self.node_feature_dim,
        }

    @classmethod
    def from_json(cls, payload: Mapping[str, Any]) -> "DatasetVocab":
        if not isinstance(payload, Mapping):
            raise DatasetError("vocabulary payload must be an object")
        try:
            constants = tuple(payload["constants"])
            relations = tuple(payload["relations"])
            node_feature_dim = _require_int(payload["node_feature_dim"], "node_feature_dim")
        except KeyError as exc:
            raise DatasetError(f"vocabulary payload missing {exc.args[0]!r}") from exc
        if any(not isinstance(name, str) or not name for name in constants):
            raise DatasetError("constant vocabulary entries must be non-empty strings")
        if any(not isinstance(name, str) or not name for name in relations):
            raise DatasetError("relation vocabulary entries must be non-empty strings")
        return cls(constants, relations, node_feature_dim)


@dataclass(frozen=True)
class ParameterLabel:
    """One supervised parameter target.

    ``value`` is canonical (constant ID, graph-local node index, or categorical
    class index).  ``target_index`` is the position in the corresponding
    candidate list or the categorical class index, i.e. what cross-entropy
    consumes directly.
    """

    name: str
    value: int
    target_index: int


@dataclass(frozen=True)
class NPAExample:
    theorem: str
    step: int
    goal_id: str
    split: str
    graph: ExprGraph
    kind: TacticKind
    source_kind: str
    parameters: Mapping[str, ParameterLabel]
    candidates: CandidateSet
    children: tuple[str, ...]

    @property
    def labeled_parameters(self) -> tuple[str, ...]:
        return tuple(self.parameters)


@dataclass(frozen=True)
class NPADataset:
    vocab: DatasetVocab
    examples: tuple[NPAExample, ...]
    source_path: str
    source_sha256: str

    def __len__(self) -> int:
        return len(self.examples)

    def split(self, name: str) -> tuple[NPAExample, ...]:
        if name not in SPLIT_NAMES:
            raise DatasetError(f"unknown split {name!r}; expected one of {SPLIT_NAMES}")
        return tuple(example for example in self.examples if example.split == name)

    @property
    def split_counts(self) -> dict[str, int]:
        return {name: len(self.split(name)) for name in SPLIT_NAMES}

    @property
    def kind_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for example in self.examples:
            name = tactic_kind_name(example.kind)
            counts[name] = counts.get(name, 0) + 1
        return dict(sorted(counts.items()))

    @property
    def source_kind_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for example in self.examples:
            counts[example.source_kind] = counts.get(example.source_kind, 0) + 1
        return dict(sorted(counts.items()))


def file_sha256(path: str | Path) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def split_for_theorem(theorem: str) -> str:
    """Deterministic theorem-level split used when a record has no split field.

    Matches the repository's existing trace-proxy convention:
    ``sha256(theorem)[:8] % 10`` -> 0-7 train, 8 validation, 9 test.
    """

    if not isinstance(theorem, str) or not theorem:
        raise DatasetError("theorem must be a non-empty string")
    value = int(hashlib.sha256(theorem.encode("utf-8")).hexdigest()[:8], 16) % 10
    if value < 8:
        return "train"
    if value == 8:
        return "validation"
    return "test"


def validate_no_theorem_leakage(records: Iterable[Mapping[str, Any]]) -> dict[str, str]:
    """Return theorem -> split and reject any theorem spanning multiple splits.

    A record may carry an explicit ``split`` field (one of train/validation/
    test); otherwise the deterministic hash rule is used.  Every record for a
    theorem must resolve to exactly the same split, so all proof states of a
    theorem stay together.
    """

    assignment: dict[str, str] = {}
    for index, record in enumerate(records):
        if not isinstance(record, Mapping):
            raise DatasetError(f"record {index} must be a JSON object")
        theorem = record.get("theorem")
        if not isinstance(theorem, str) or not theorem:
            raise DatasetError(f"record {index}: theorem must be a non-empty string")
        explicit = record.get("split")
        if explicit is None:
            resolved = split_for_theorem(theorem)
        else:
            if explicit not in SPLIT_NAMES:
                raise DatasetError(
                    f"record {index}: split must be one of {SPLIT_NAMES}, got {explicit!r}"
                )
            resolved = str(explicit)
        previous = assignment.get(theorem)
        if previous is not None and previous != resolved:
            raise DatasetError(
                f"theorem split leakage: {theorem!r} appears in {previous!r} and {resolved!r}"
            )
        assignment[theorem] = resolved
    return assignment


def read_jsonl(path: str | Path) -> list[dict[str, Any]]:
    path = Path(path)
    records: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as stream:
        for line_number, line in enumerate(stream, start=1):
            if not line.strip():
                continue
            try:
                payload = json.loads(line)
            except json.JSONDecodeError as exc:
                raise DatasetError(f"{path}:{line_number}: invalid JSON: {exc}") from exc
            if not isinstance(payload, dict):
                raise DatasetError(f"{path}:{line_number}: each line must be a JSON object")
            records.append(payload)
    if not records:
        raise DatasetError(f"{path}: dataset contains no records")
    return records


def _require_int(value: Any, field_name: str, *, minimum: int | None = None) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise DatasetError(f"{field_name} must be an integer, got {type(value).__name__}")
    if minimum is not None and value < minimum:
        raise DatasetError(f"{field_name} must be >= {minimum}, got {value}")
    return value


def _require_str(value: Any, field_name: str) -> str:
    if not isinstance(value, str) or not value:
        raise DatasetError(f"{field_name} must be a non-empty string")
    return value


def _normalized_name(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", name.lower())


_NODE_KIND_BY_NAME = {_normalized_name(kind.name): kind for kind in NodeKind}


def _parse_node_kind(value: Any, field_name: str) -> NodeKind:
    if isinstance(value, bool):
        raise DatasetError(f"{field_name} must be a NodeKind name")
    if isinstance(value, int):
        try:
            return NodeKind(value)
        except ValueError as exc:
            raise DatasetError(f"{field_name} has unknown NodeKind ID {value}") from exc
    if isinstance(value, str):
        key = _normalized_name(value)
        try:
            return _NODE_KIND_BY_NAME[key]
        except KeyError as exc:
            raise DatasetError(f"{field_name} has unknown NodeKind name {value!r}") from exc
    raise DatasetError(f"{field_name} must be a NodeKind name or integer ID")


def _constant_names(graph: Mapping[str, Any], record_index: int) -> list[str]:
    names: list[str] = []
    declared = graph.get("constants", [])
    if declared is None:
        declared = []
    if not isinstance(declared, list):
        raise DatasetError(f"record {record_index}: graph.constants must be a list")
    for entry in declared:
        if isinstance(entry, str):
            names.append(_require_str(entry, "graph.constants entry"))
        elif isinstance(entry, Mapping):
            names.append(_require_str(entry.get("name"), "graph.constants[].name"))
        else:
            raise DatasetError(
                f"record {record_index}: graph.constants entries must be strings or objects"
            )
    nodes = graph.get("nodes", [])
    if not isinstance(nodes, list):
        raise DatasetError(f"record {record_index}: graph.nodes must be a list")
    for node_index, node in enumerate(nodes):
        if not isinstance(node, Mapping):
            raise DatasetError(f"record {record_index}: node {node_index} must be an object")
        constant_name = node.get("constant")
        if constant_name is not None:
            names.append(_require_str(constant_name, "node.constant"))
    return names


def _edge_relation_name(edge: Mapping[str, Any], relations: Sequence[str], record_index: int) -> str:
    value = edge.get("type", edge.get("relation", 0))
    if isinstance(value, bool):
        raise DatasetError(f"record {record_index}: edge type must be a string or integer")
    if isinstance(value, int):
        if value < 0:
            raise DatasetError(f"record {record_index}: edge type must be nonnegative")
        if relations:
            if value >= len(relations):
                raise DatasetError(
                    f"record {record_index}: edge type index {value} outside graph.relations"
                )
            return _require_str(relations[value], "graph.relations entry")
        return f"rel_{value}"
    if isinstance(value, str) and value:
        return value
    raise DatasetError(f"record {record_index}: edge type must be a string or integer")


def _graph_relations(graph: Mapping[str, Any], record_index: int) -> list[str]:
    raw = graph.get("relations", [])
    if raw is None:
        raw = []
    if not isinstance(raw, list):
        raise DatasetError(f"record {record_index}: graph.relations must be a list")
    return [_require_str(name, "graph.relations entry") for name in raw]


def _referenced_premise_names(record: Mapping[str, Any], record_index: int) -> list[str]:
    """Collect constant names a record may name through its premise head.

    Premise candidates and labels are global constant-vocabulary entries, not
    graph-local nodes.  Apply/exact/rewrite steps routinely name lemmas (for
    example ``Eq.trans``) that never occur in the record's own expression
    graph, so the dataset vocabulary has to be seeded from the candidate list
    and the tactic label as well as from ``graph.constants``.

    Integer entries are vocabulary IDs in their own right and are validated
    later against the assembled vocabulary; only string entries contribute
    names here.
    """

    names: list[str] = []
    raw_candidates = record.get("candidates")
    if raw_candidates is not None:
        if not isinstance(raw_candidates, Mapping):
            raise DatasetError(f"record {record_index}: candidates must be an object")
        items, _ = _candidate_items(raw_candidates.get("premise"), "premise", record_index)
        for item in items:
            if isinstance(item, str):
                names.append(_require_str(item, "candidate premise name"))
    tactic = record.get("tactic")
    if isinstance(tactic, Mapping):
        raw_parameters = tactic.get("parameters")
        if isinstance(raw_parameters, Mapping):
            premise = raw_parameters.get("premise")
            if isinstance(premise, str):
                names.append(
                    _require_str(
                        premise, f"record {record_index}: tactic.parameters.premise"
                    )
                )
    return names


def build_dataset_vocab(
    records: Sequence[Mapping[str, Any]],
    *,
    constant_vocab: Sequence[str] | None = None,
    relation_vocab: Sequence[str] | None = None,
    node_feature_dim: int | None = None,
) -> DatasetVocab:
    """Collect global constant/relation vocabularies and validate feature widths.

    Constant names come from ``graph.constants``/CONST nodes and from every
    premise reference in the record (``candidates.premise`` entries and
    ``tactic.parameters.premise``), because premise lemmas need not occur in
    the expression graph itself.  Vocabularies are sorted by name unless
    explicitly supplied, which makes the IDs independent of record order.
    Evaluation must pass the checkpoint's vocabulary so model index spaces
    match.
    """

    constants: set[str] = set()
    relations: set[str] = set()
    inferred_dim: int | None = None
    for record_index, record in enumerate(records):
        graph = record.get("graph")
        if not isinstance(graph, Mapping):
            raise DatasetError(f"record {record_index}: graph must be an object")
        constants.update(_constant_names(graph, record_index))
        constants.update(_referenced_premise_names(record, record_index))
        relation_names = _graph_relations(graph, record_index)
        relations.update(relation_names)
        nodes = graph.get("nodes", [])
        for node_index, node in enumerate(nodes):
            if not isinstance(node, Mapping):
                raise DatasetError(f"record {record_index}: node {node_index} must be an object")
            if "features" not in node:
                continue
            features = node["features"]
            if not isinstance(features, list) or not features:
                raise DatasetError(
                    f"record {record_index}: node {node_index}.features must be a non-empty list"
                )
            if inferred_dim is None:
                inferred_dim = len(features)
            elif len(features) != inferred_dim:
                raise DatasetError(
                    f"record {record_index}: node feature width {len(features)} "
                    f"does not match {inferred_dim}"
                )
        edges = graph.get("edges", [])
        if not isinstance(edges, list):
            raise DatasetError(f"record {record_index}: graph.edges must be a list")
        for edge_index, edge in enumerate(edges):
            if isinstance(edge, (list, tuple)):
                if len(edge) != 3:
                    raise DatasetError(
                        f"record {record_index}: edge {edge_index} must have [source, target, type]"
                    )
                edge = {"source": edge[0], "target": edge[1], "type": edge[2]}
            if not isinstance(edge, Mapping):
                raise DatasetError(f"record {record_index}: edge {edge_index} must be an object")
            relations.add(_edge_relation_name(edge, relation_names, record_index))

    if node_feature_dim is not None:
        _require_int(node_feature_dim, "node_feature_dim", minimum=1)
        if inferred_dim is not None and inferred_dim != node_feature_dim:
            raise DatasetError(
                f"provided node_feature_dim={node_feature_dim} but data uses {inferred_dim}"
            )
    elif inferred_dim is None:
        # Datasets containing only empty graphs still need a valid projection
        # width; one zero feature is the least surprising default.
        inferred_dim = 1

    if constant_vocab is None:
        constant_tuple = tuple(sorted(constants))
    else:
        constant_tuple = tuple(constant_vocab)
        if any(not isinstance(name, str) or not name for name in constant_tuple):
            raise DatasetError("constant_vocab entries must be non-empty strings")
        missing = sorted(constants - set(constant_tuple))
        if missing:
            raise DatasetError(f"data contains constants outside constant_vocab: {missing[:5]}")
    if relation_vocab is None:
        relation_tuple = tuple(sorted(relations))
    else:
        relation_tuple = tuple(relation_vocab)
        if any(not isinstance(name, str) or not name for name in relation_tuple):
            raise DatasetError("relation_vocab entries must be non-empty strings")
        missing = sorted(relations - set(relation_tuple))
        if missing:
            raise DatasetError(f"data contains relations outside relation_vocab: {missing[:5]}")
    return DatasetVocab(constant_tuple, relation_tuple, int(inferred_dim))


def _convert_graph(
    raw_graph: Any,
    vocab: DatasetVocab,
    record_index: int,
) -> tuple[ExprGraph, dict[str, int], dict[str, int]]:
    if not isinstance(raw_graph, Mapping):
        raise DatasetError(f"record {record_index}: graph must be an object")
    schema = raw_graph.get("schema", GRAPH_SCHEMA_VERSION)
    if schema != GRAPH_SCHEMA_VERSION:
        raise DatasetError(
            f"record {record_index}: unsupported graph schema {schema!r}; "
            f"expected {GRAPH_SCHEMA_VERSION}"
        )
    nodes = raw_graph.get("nodes", [])
    if not isinstance(nodes, list):
        raise DatasetError(f"record {record_index}: graph.nodes must be a list")

    node_kinds: list[int] = []
    features: list[list[float]] = []
    constant_ids: list[int] = []
    for node_index, node in enumerate(nodes):
        if not isinstance(node, Mapping):
            raise DatasetError(f"record {record_index}: node {node_index} must be an object")
        kind = _parse_node_kind(node.get("kind"), f"record {record_index}: node {node_index}.kind")
        node_kinds.append(int(kind))
        raw_features = node.get("features")
        if raw_features is None:
            row = [0.0] * vocab.node_feature_dim
        else:
            if not isinstance(raw_features, list) or len(raw_features) != vocab.node_feature_dim:
                raise DatasetError(
                    f"record {record_index}: node {node_index}.features must have "
                    f"{vocab.node_feature_dim} numbers"
                )
            row = []
            for value in raw_features:
                if isinstance(value, bool) or not isinstance(value, (int, float)):
                    raise DatasetError(
                        f"record {record_index}: node {node_index}.features must be numeric"
                    )
                number = float(value)
                if not math.isfinite(number):
                    raise DatasetError(
                        f"record {record_index}: node {node_index}.features must be finite"
                    )
                row.append(number)
        features.append(row)

        constant_name = node.get("constant")
        constant_id = node.get("constant_id")
        if kind == NodeKind.CONST:
            if constant_name is not None:
                cid = vocab.constant_id(_require_str(constant_name, "node.constant"))
                if constant_id is not None and _require_int(constant_id, "node.constant_id", minimum=-1) != cid:
                    raise DatasetError(
                        f"record {record_index}: node {node_index} constant name/ID disagree"
                    )
                constant_ids.append(cid)
            elif constant_id is not None:
                cid = _require_int(constant_id, "node.constant_id", minimum=-1)
                if cid >= len(vocab.constants):
                    raise DatasetError(
                        f"record {record_index}: node {node_index} constant ID outside vocabulary"
                    )
                constant_ids.append(cid)
            else:
                constant_ids.append(-1)
        else:
            if constant_name is not None or constant_id not in (None, -1):
                raise DatasetError(
                    f"record {record_index}: only CONST nodes may carry a constant name/ID"
                )
            constant_ids.append(-1)

    relation_names = _graph_relations(raw_graph, record_index)
    edges_raw = raw_graph.get("edges", [])
    if not isinstance(edges_raw, list):
        raise DatasetError(f"record {record_index}: graph.edges must be a list")
    sources: list[int] = []
    targets: list[int] = []
    edge_types: list[int] = []
    for edge_index, edge in enumerate(edges_raw):
        if isinstance(edge, (list, tuple)):
            if len(edge) != 3:
                raise DatasetError(
                    f"record {record_index}: edge {edge_index} must have [source, target, type]"
                )
            edge = {"source": edge[0], "target": edge[1], "type": edge[2]}
        if not isinstance(edge, Mapping):
            raise DatasetError(f"record {record_index}: edge {edge_index} must be an object")
        source = _require_int(edge.get("source"), f"record {record_index}: edge source", minimum=0)
        target = _require_int(edge.get("target"), f"record {record_index}: edge target", minimum=0)
        if source >= len(nodes) or target >= len(nodes):
            raise DatasetError(f"record {record_index}: edge endpoint outside node range")
        sources.append(source)
        targets.append(target)
        relation_name = _edge_relation_name(edge, relation_names, record_index)
        edge_types.append(vocab.relation_id(relation_name))

    fvar_map: dict[str, int] = {}
    fvars_raw = raw_graph.get("fvars", [])
    if not isinstance(fvars_raw, list):
        raise DatasetError(f"record {record_index}: graph.fvars must be a list")
    for entry in fvars_raw:
        if not isinstance(entry, Mapping):
            raise DatasetError(f"record {record_index}: graph.fvars entries must be objects")
        name = _require_str(entry.get("name"), "graph.fvars[].name")
        node_index = _require_int(entry.get("node"), "graph.fvars[].node", minimum=0)
        if node_index >= len(nodes):
            raise DatasetError(f"record {record_index}: fvar {name!r} node outside range")
        if node_kinds[node_index] != int(NodeKind.FVAR):
            raise DatasetError(f"record {record_index}: fvar {name!r} must point to an FVAR node")
        if name in fvar_map:
            raise DatasetError(f"record {record_index}: duplicate fvar name {name!r}")
        fvar_map[name] = node_index

    locus_map: dict[str, int] = {}
    loci_raw = raw_graph.get("loci", [])
    if not isinstance(loci_raw, list):
        raise DatasetError(f"record {record_index}: graph.loci must be a list")
    for entry in loci_raw:
        if not isinstance(entry, Mapping):
            raise DatasetError(f"record {record_index}: graph.loci entries must be objects")
        position = entry.get("position")
        if isinstance(position, int) and not isinstance(position, bool):
            position = str(position)
        position = _require_str(position, "graph.loci[].position")
        node_index = _require_int(entry.get("node"), "graph.loci[].node", minimum=0)
        if node_index >= len(nodes):
            raise DatasetError(f"record {record_index}: locus {position!r} node outside range")
        if position in locus_map:
            raise DatasetError(f"record {record_index}: duplicate locus position {position!r}")
        locus_map[position] = node_index

    graph = ExprGraph(
        node_kinds=torch.tensor(node_kinds, dtype=torch.long),
        edge_index=torch.tensor([sources, targets], dtype=torch.long)
        if sources
        else torch.empty((2, 0), dtype=torch.long),
        edge_types=torch.tensor(edge_types, dtype=torch.long),
        constant_ids=torch.tensor(constant_ids, dtype=torch.long),
        node_features=torch.tensor(features, dtype=torch.float32).reshape(
            len(nodes), vocab.node_feature_dim
        ),
    )
    graph.validate(vocab.node_feature_dim)
    return graph, fvar_map, locus_map


def _candidate_items(raw: Any, parameter: str, record_index: int) -> tuple[list[Any], list[bool]]:
    if raw is None:
        return [], []
    if isinstance(raw, list):
        return list(raw), [True] * len(raw)
    if isinstance(raw, Mapping):
        items = raw.get("items", raw.get("indices", raw.get("values")))
        if items is None:
            raise DatasetError(
                f"record {record_index}: candidates.{parameter} object needs items/indices/values"
            )
        if not isinstance(items, list):
            raise DatasetError(f"record {record_index}: candidates.{parameter}.items must be a list")
        mask = raw.get("mask")
        if mask is None:
            mask = [True] * len(items)
        if not isinstance(mask, list) or len(mask) != len(items) or any(
            not isinstance(value, bool) for value in mask
        ):
            raise DatasetError(
                f"record {record_index}: candidates.{parameter}.mask must be bools matching items"
            )
        return list(items), list(mask)
    raise DatasetError(
        f"record {record_index}: candidates.{parameter} must be a list or object"
    )


def _convert_candidates(
    raw: Any,
    graph: ExprGraph,
    fvar_map: Mapping[str, int],
    locus_map: Mapping[str, int],
    vocab: DatasetVocab,
    record_index: int,
) -> CandidateSet:
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise DatasetError(f"record {record_index}: candidates must be an object")
    unknown = sorted(set(raw) - set(POINTER_PARAMETERS))
    if unknown:
        raise DatasetError(f"record {record_index}: unknown candidate sources {unknown}")
    node_count = int(graph.node_kinds.shape[0])

    premise_items, premise_mask = _candidate_items(raw.get("premise"), "premise", record_index)
    premise_ids: list[int] = []
    for item in premise_items:
        if isinstance(item, str):
            # Premise candidates are global vocabulary IDs, not graph nodes:
            # a lemma may be applicable without appearing anywhere in the
            # current expression graph, so no graph.constants membership check
            # belongs here.
            premise_ids.append(vocab.constant_id(item))
        else:
            value = _require_int(item, "candidate premise ID", minimum=0)
            if value >= len(vocab.constants):
                raise DatasetError(
                    f"record {record_index}: candidate premise ID {value} outside vocabulary"
                )
            premise_ids.append(value)
    if len(set(premise_ids)) != len(premise_ids):
        raise DatasetError(f"record {record_index}: duplicate premise candidates")

    def pointer_source(parameter: str, items: list[Any], mask: list[bool]) -> PointerCandidates:
        indices: list[int] = []
        for item in items:
            if parameter == "free_variable" and isinstance(item, str):
                if item not in fvar_map:
                    raise DatasetError(
                        f"record {record_index}: candidate fvar {item!r} not declared in graph.fvars"
                    )
                node_index = fvar_map[item]
            elif parameter == "locus" and isinstance(item, str):
                if item not in locus_map:
                    raise DatasetError(
                        f"record {record_index}: candidate locus {item!r} not in graph.loci"
                    )
                node_index = locus_map[item]
            else:
                node_index = _require_int(item, f"candidate {parameter} node", minimum=0)
            if node_index >= node_count:
                raise DatasetError(
                    f"record {record_index}: candidate {parameter} node {node_index} outside graph"
                )
            if parameter == "free_variable" and int(graph.node_kinds[node_index]) != int(NodeKind.FVAR):
                raise DatasetError(
                    f"record {record_index}: free_variable candidate {node_index} is not an FVAR node"
                )
            indices.append(node_index)
        if len(set(indices)) != len(indices):
            raise DatasetError(f"record {record_index}: duplicate {parameter} candidates")
        return PointerCandidates(
            indices=torch.tensor(indices, dtype=torch.long),
            mask=torch.tensor(mask, dtype=torch.bool),
        )

    return CandidateSet(
        premise=PremiseCandidates(
            constant_ids=torch.tensor(premise_ids, dtype=torch.long),
            mask=torch.tensor(premise_mask, dtype=torch.bool),
        ),
        free_variable=pointer_source(
            "free_variable", *_candidate_items(raw.get("free_variable"), "free_variable", record_index)
        ),
        locus=pointer_source("locus", *_candidate_items(raw.get("locus"), "locus", record_index)),
    )


def _convert_parameter_label(
    name: str,
    raw_value: Any,
    graph: ExprGraph,
    fvar_map: Mapping[str, int],
    locus_map: Mapping[str, int],
    candidates: CandidateSet,
    vocab: DatasetVocab,
    record_index: int,
) -> ParameterLabel:
    if name in POINTER_PARAMETERS:
        choices = candidates.for_parameter(name)
        if name == "premise":
            if isinstance(raw_value, str):
                value = vocab.constant_id(raw_value)
            else:
                value = _require_int(raw_value, "premise label", minimum=0)
                if value >= len(vocab.constants):
                    raise DatasetError(f"record {record_index}: premise label outside vocabulary")
            matches = torch.nonzero(
                (choices.constant_ids == value) & choices.mask, as_tuple=False
            ).flatten()
        else:
            if isinstance(raw_value, str):
                source_map = fvar_map if name == "free_variable" else locus_map
                if raw_value not in source_map:
                    raise DatasetError(
                        f"record {record_index}: {name} label {raw_value!r} is not in graph metadata"
                    )
                value = source_map[raw_value]
            else:
                value = _require_int(raw_value, f"{name} label", minimum=0)
            if value >= int(graph.node_kinds.shape[0]):
                raise DatasetError(f"record {record_index}: {name} label outside graph")
            if name == "free_variable" and int(graph.node_kinds[value]) != int(NodeKind.FVAR):
                raise DatasetError(f"record {record_index}: free_variable label is not an FVAR node")
            matches = torch.nonzero(
                (choices.indices == value) & choices.mask, as_tuple=False
            ).flatten()
        if matches.numel() != 1:
            raise DatasetError(
                f"record {record_index}: {name} label {value} is not exactly one eligible candidate"
            )
        return ParameterLabel(name=name, value=value, target_index=int(matches.item()))

    values = CATEGORY_VALUES[name]
    if isinstance(raw_value, str):
        try:
            value = values.index(raw_value)
        except ValueError as exc:
            raise DatasetError(
                f"record {record_index}: {name} label {raw_value!r} outside {values}"
            ) from exc
    else:
        value = _require_int(raw_value, f"{name} label", minimum=0)
        if value >= len(values):
            raise DatasetError(f"record {record_index}: {name} label {value} outside vocabulary")
    return ParameterLabel(name=name, value=value, target_index=value)


def _convert_record(
    record: Mapping[str, Any],
    vocab: DatasetVocab,
    split: str,
    record_index: int,
) -> NPAExample:
    theorem = _require_str(record.get("theorem"), f"record {record_index}: theorem")
    step = _require_int(record.get("step"), f"record {record_index}: step", minimum=0)
    goal_id = _require_str(record.get("goal_id"), f"record {record_index}: goal_id")
    tactic = record.get("tactic")
    if not isinstance(tactic, Mapping):
        raise DatasetError(f"record {record_index}: tactic must be an object")
    source_kind = _require_str(tactic.get("kind"), f"record {record_index}: tactic.kind")
    kind = tactic_kind_from_name(source_kind)

    graph, fvar_map, locus_map = _convert_graph(record.get("graph"), vocab, record_index)
    candidates = _convert_candidates(
        record.get("candidates"), graph, fvar_map, locus_map, vocab, record_index
    )

    raw_parameters = tactic.get("parameters", {})
    if raw_parameters is None:
        raw_parameters = {}
    if not isinstance(raw_parameters, Mapping):
        raise DatasetError(f"record {record_index}: tactic.parameters must be an object")

    parameters: dict[str, ParameterLabel] = {}
    if kind == TacticKind.OTHER:
        # Non-atomic/binder payloads (define/have/let/raw) are intentionally
        # not modeled in v1; the original source kind is retained for audits.
        parameters = {}
    else:
        sequence = TACTIC_PARAMETERS[kind]
        extra = sorted(set(raw_parameters) - set(sequence))
        if extra:
            raise DatasetError(
                f"record {record_index}: parameters {extra} are not valid for {source_kind}"
            )
        for name in sequence:
            raw_value = raw_parameters.get(name)
            if raw_value is None:
                continue
            parameters[name] = _convert_parameter_label(
                name,
                raw_value,
                graph,
                fvar_map,
                locus_map,
                candidates,
                vocab,
                record_index,
            )

    children = record.get("children", [])
    if not isinstance(children, list) or any(
        not isinstance(child, str) or not child for child in children
    ):
        raise DatasetError(f"record {record_index}: children must be a list of non-empty strings")

    return NPAExample(
        theorem=theorem,
        step=step,
        goal_id=goal_id,
        split=split,
        graph=graph,
        kind=kind,
        source_kind=source_kind,
        parameters=parameters,
        candidates=candidates,
        children=tuple(children),
    )


def load_dataset(
    path: str | Path,
    *,
    constant_vocab: Sequence[str] | None = None,
    relation_vocab: Sequence[str] | None = None,
    node_feature_dim: int | None = None,
) -> NPADataset:
    """Load and validate a JSONL NPA dataset.

    Pass the checkpoint's vocabularies when loading an evaluation file so the
    model index spaces are identical to training.  The theorem-level split is
    taken from an explicit ``split`` field when present, otherwise from
    :func:`split_for_theorem`; mixed assignments are rejected.
    """

    path = Path(path)
    records = read_jsonl(path)
    split_map = validate_no_theorem_leakage(records)
    vocab = build_dataset_vocab(
        records,
        constant_vocab=constant_vocab,
        relation_vocab=relation_vocab,
        node_feature_dim=node_feature_dim,
    )
    examples: list[NPAExample] = []
    seen_goals: set[tuple[str, str]] = set()
    for index, record in enumerate(records):
        example = _convert_record(record, vocab, split_map[record["theorem"]], index)
        key = (example.theorem, example.goal_id)
        if key in seen_goals:
            raise DatasetError(f"duplicate theorem/goal_id pair {key!r}")
        seen_goals.add(key)
        examples.append(example)
    return NPADataset(
        vocab=vocab,
        examples=tuple(examples),
        source_path=str(path),
        source_sha256=file_sha256(path),
    )


# ---------------------------------------------------------------------------
# Synthetic sample generator (schema/training smoke tests only)


# Twelve kinds cover every parameter head type (premise/free_variable/locus
# pointers and all six categorical vocabularies).  Keeping one kind per variant
# also guarantees that every parameter head receives a gradient in the
# synthetic overfit smoke test.
SYNTHETIC_KINDS: tuple[TacticKind, ...] = (
    TacticKind.INTRO,
    TacticKind.REVERT,
    TacticKind.APPLY,
    TacticKind.MOTIVATED_APPLY,
    TacticKind.GENERALIZE,
    TacticKind.PI,
    TacticKind.CASES,
    TacticKind.INDUCTION,
    TacticKind.REWRITE,
    TacticKind.GENERALIZE_AT,
    TacticKind.UNFOLD,
    TacticKind.NORMALIZE,
)
SYNTHETIC_FEATURE_DIM = 18
SYNTHETIC_VARIANTS = len(SYNTHETIC_KINDS)


def _theorem_name_for_split(split: str, group: int, seed: int) -> str:
    """Find a deterministic synthetic theorem name whose hash selects split."""

    for attempt in range(10000):
        candidate = f"synthetic.npa.{seed}.{split}.{group}.{attempt}"
        if split_for_theorem(candidate) == split:
            return candidate
    raise DatasetError(f"could not find a synthetic theorem name for split {split!r}")


def _synthetic_parameter_value(name: str, variant: int) -> str:
    if name == "premise":
        return f"syn.c{variant}"
    if name == "free_variable":
        return f"h{variant}" if variant % 2 == 0 else f"k{variant}"
    if name == "locus":
        return ("0", "1", "2")[variant % 3]
    if name == "direction":
        return CATEGORY_VALUES["direction"][variant % 2]
    if name == "occurrence":
        return CATEGORY_VALUES["occurrence"][variant % 4]
    if name == "cases_mode":
        return CATEGORY_VALUES["cases_mode"][variant % 3]
    if name == "induction_mode":
        return CATEGORY_VALUES["induction_mode"][variant % 3]
    if name == "name_mode":
        return CATEGORY_VALUES["name_mode"][variant % 3]
    if name == "target_mode":
        return CATEGORY_VALUES["target_mode"][variant % 3]
    raise DatasetError(f"no synthetic value rule for parameter {name!r}")


def synthetic_records(
    count: int = 64,
    *,
    seed: int = 0,
    states_per_theorem: int = 4,
) -> list[dict[str, Any]]:
    """Create a deterministic synthetic sample for smoke tests only.

    Labels are a deterministic function of a one-hot variant signal so a small
    model can overfit the sample.  This is not a benchmark and must never be
    reported as a real-data result.
    """

    count = int(count)
    states_per_theorem = int(states_per_theorem)
    if count < 1 or states_per_theorem < 1:
        raise DatasetError("count and states_per_theorem must be positive")
    theorem_groups = (count + states_per_theorem - 1) // states_per_theorem
    train_groups = max(1, int(round(theorem_groups * 0.75)))
    remaining_groups = theorem_groups - train_groups
    validation_groups = remaining_groups // 2 if remaining_groups else 0
    test_groups = remaining_groups - validation_groups
    records: list[dict[str, Any]] = []
    for group in range(theorem_groups):
        if group < train_groups:
            split = "train"
        elif group < train_groups + validation_groups:
            split = "validation"
        else:
            split = "test"
        theorem = _theorem_name_for_split(split, group, seed)
        # Reuse training variants for held-out theorems so held-out exact
        # tactic accuracy measures generalization to new theorem identities
        # rather than to labels the model never saw.
        variant = group % min(SYNTHETIC_VARIANTS, train_groups) if train_groups < SYNTHETIC_VARIANTS else group % SYNTHETIC_VARIANTS
        kind = SYNTHETIC_KINDS[variant]
        for step in range(states_per_theorem):
            if len(records) >= count:
                break
            goal_id = f"{theorem}:g{step}"
            features = [0.0] * SYNTHETIC_FEATURE_DIM
            features[variant] = 1.0
            features[16] = step / max(states_per_theorem - 1, 1)
            nodes = []
            node_kinds = ("CONST", "FVAR", "FVAR", "APP", "APP")
            for node_index, node_kind in enumerate(node_kinds):
                # A node-position signal breaks the h/k symmetry so pointer
                # heads can learn which fvar the label selects.
                features[17] = node_index / (len(node_kinds) - 1)
                node: dict[str, Any] = {
                    "kind": node_kind,
                    "features": list(features),
                }
                if node_kind == "CONST":
                    node["constant"] = f"syn.c{variant}"
                nodes.append(node)
            parameters = {
                name: _synthetic_parameter_value(name, variant)
                for name in TACTIC_PARAMETERS[kind]
            }
            records.append(
                {
                    "theorem": theorem,
                    "step": step,
                    "goal_id": goal_id,
                    "graph": {
                        "schema": 1,
                        "nodes": nodes,
                        "edges": [
                            {"source": 0, "target": 3, "type": "app_fn"},
                            {"source": 1, "target": 3, "type": "app_arg"},
                            {"source": 3, "target": 4, "type": "body"},
                            {"source": 2, "target": 4, "type": "app_arg"},
                        ],
                        "constants": [
                            f"syn.c{variant}",
                            f"syn.c{(variant + 1) % SYNTHETIC_VARIANTS}",
                            f"syn.c{(variant + 2) % SYNTHETIC_VARIANTS}",
                        ],
                        "fvars": [
                            {"name": f"h{variant}", "node": 1},
                            {"name": f"k{variant}", "node": 2},
                        ],
                        "loci": [
                            {"position": "0", "node": 3},
                            {"position": "1", "node": 4},
                            {"position": "2", "node": 1},
                        ],
                    },
                    "tactic": {
                        "kind": tactic_kind_name(kind),
                        "parameters": parameters,
                    },
                    "candidates": {
                        "premise": {
                            "items": [
                                f"syn.c{(variant + 1) % SYNTHETIC_VARIANTS}",
                                f"syn.c{variant}",
                                f"syn.c{(variant + 2) % SYNTHETIC_VARIANTS}",
                            ],
                            "mask": [True, True, variant % 2 == 0],
                        },
                        "free_variable": {
                            "items": [f"h{variant}", f"k{variant}"],
                            "mask": [True, True],
                        },
                        "locus": {
                            "items": ["0", "1", "2"],
                            "mask": [True, True, True],
                        },
                    },
                    "children": [f"{theorem}:g{step + 1}"] if step + 1 < states_per_theorem else [],
                }
            )
    return records


def write_synthetic_jsonl(
    path: str | Path,
    *,
    count: int = 64,
    seed: int = 0,
    states_per_theorem: int = 4,
) -> Path:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    records = synthetic_records(count, seed=seed, states_per_theorem=states_per_theorem)
    with path.open("w", encoding="utf-8") as stream:
        for record in records:
            stream.write(json.dumps(record, separators=(",", ":"), sort_keys=True) + "\n")
    return path


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-synthetic", type=Path, help="output JSONL path")
    parser.add_argument("--synthetic-states", type=int, default=64)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--states-per-theorem", type=int, default=4)
    args = parser.parse_args(argv)
    if args.write_synthetic is None:
        parser.error("--write-synthetic is required")
    path = write_synthetic_jsonl(
        args.write_synthetic,
        count=args.synthetic_states,
        seed=args.seed,
        states_per_theorem=args.states_per_theorem,
    )
    print(f"wrote synthetic sample to {path}")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
