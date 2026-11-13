"""Evaluate a trained parameterized NPA checkpoint.

Reports Kind accuracy, per-parameter accuracy, and exact full-tactic-prefix
accuracy on one or all theorem splits.  This version evaluates synthetic or
sample JSONL data only; it does not run Lean search.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

try:
    from experiments.npa_training.dataset import file_sha256, load_dataset
    from experiments.npa_training.train_npa import (
        count_parameters,
        evaluate_examples,
        load_checkpoint,
        resolve_device,
    )
except ModuleNotFoundError:  # pragma: no cover - direct CLI execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from experiments.npa_training.dataset import file_sha256, load_dataset
    from experiments.npa_training.train_npa import (
        count_parameters,
        evaluate_examples,
        load_checkpoint,
        resolve_device,
    )


def evaluate_checkpoint(
    checkpoint_path: str | Path,
    data_path: str | Path,
    *,
    split: str = "validation",
    device: str = "cpu",
    limit: int | None = None,
    data_kind: str = "sample",
) -> dict[str, Any]:
    resolved_device = resolve_device(device)
    model, vocab, payload = load_checkpoint(checkpoint_path, resolved_device)
    dataset = load_dataset(
        data_path,
        constant_vocab=vocab.constants,
        relation_vocab=vocab.relations,
        node_feature_dim=vocab.node_feature_dim,
    )
    split_names = ("train", "validation", "test") if split == "all" else (split,)
    results: dict[str, Any] = {}
    all_examples = []
    for name in split_names:
        examples = list(dataset.split(name))
        if limit is not None:
            examples = examples[:limit]
        all_examples.extend(examples)
        results[name] = evaluate_examples(model, examples, resolved_device)
    results["overall"] = evaluate_examples(model, all_examples, resolved_device)
    return {
        "experiment": "parameterized paper-aligned NPA evaluation (v1)",
        "paper_fidelity": False,
        "data_kind": data_kind,
        "data_warning": (
            "SYNTHETIC SAMPLE ONLY - not a real ExprGraph/Nazrin result"
            if data_kind == "synthetic"
            else "SAMPLE DATA - not a paper benchmark result"
        ),
        "checkpoint": {
            "path": str(checkpoint_path),
            "format": payload.get("format"),
            "sha256": file_sha256(checkpoint_path),
        },
        "data": {
            "path": str(data_path),
            "sha256": dataset.source_sha256,
            "examples": len(dataset),
            "split_counts": dataset.split_counts,
        },
        "model": {
            "parameter_count": count_parameters(model),
            "num_constants": model.num_constants,
            "num_relations": model.num_relations,
            "node_feature_dim": model.node_feature_dim,
        },
        "requested_split": split,
        "metrics": results,
    }


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--data", type=Path, default=None, help="JSONL; defaults to checkpoint's training data")
    parser.add_argument("--split", choices=("train", "validation", "test", "all"), default="validation")
    parser.add_argument("--device", default="cpu")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--data-kind", choices=("synthetic", "sample"), default=None)
    parser.add_argument("--output", type=Path, default=None)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_arg_parser().parse_args(argv)
    _, _, payload = load_checkpoint(args.checkpoint, "cpu")
    data_path = args.data
    if data_path is None:
        training = payload.get("training", {})
        candidate = training.get("data_path") if isinstance(training, dict) else None
        if not candidate:
            raise SystemExit("--data is required because the checkpoint has no training data path")
        data_path = Path(candidate)
        if not data_path.is_file():
            raise SystemExit(f"checkpoint training data no longer exists: {data_path}")
    data_kind = args.data_kind
    if data_kind is None:
        training = payload.get("training", {})
        stored_kind = training.get("data_kind") if isinstance(training, dict) else None
        data_kind = stored_kind if stored_kind in ("synthetic", "sample") else "sample"
    result = evaluate_checkpoint(
        args.checkpoint,
        data_path,
        split=args.split,
        device=args.device,
        limit=args.limit,
        data_kind=data_kind,
    )
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(f"wrote {args.output}")
    overall = result["metrics"]["overall"]

    def format_metric(value: Any) -> str:
        return "n/a" if value is None else f"{float(value):.4f}"

    print(
        f"examples={overall['examples']} kind_accuracy={format_metric(overall['kind_accuracy'])} "
        f"exact_tactic_accuracy={format_metric(overall['exact_tactic_accuracy'])} "
        f"loss={format_metric(overall['loss'])}"
    )
    for name, values in overall["parameter_accuracy"].items():
        print(
            f"  {name}: accuracy={format_metric(values['accuracy'])} "
            f"({values['correct']}/{values['total']})"
        )
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
