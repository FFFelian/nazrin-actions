"""Supervised training loop for the parameterized paper-aligned NPA.

This is a first-version trainer: variable-size ExprGraphs are processed one at
a time and gradients are accumulated over ``--batch-size`` examples before each
AdamW step.  It is deliberately small and reproducible; the synthetic sample
is a smoke test, not a benchmark.

Example:
    python -m experiments.npa_training.train_npa \
        --synthetic-states 64 --epochs 20 --batch-size 8 --lr 3e-3 \
        --device cuda --output-dir experiments/npa_training/runs/synthetic-overfit
"""

from __future__ import annotations

import argparse
import csv
import json
import platform
import random
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping, Sequence

import torch
from torch import Tensor, nn
from torch.nn import functional as F

try:
    from experiments.paper_aligned_npa import (
        CandidateSet,
        ExprGraph,
        PaperAlignedNPA,
        TacticPrefix,
    )
    from experiments.npa_training.dataset import (
        DatasetVocab,
        NPAExample,
        file_sha256,
        load_dataset,
        write_synthetic_jsonl,
    )
except ModuleNotFoundError:  # pragma: no cover - direct CLI execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from experiments.paper_aligned_npa import (
        CandidateSet,
        ExprGraph,
        PaperAlignedNPA,
        TacticPrefix,
    )
    from experiments.npa_training.dataset import (
        DatasetVocab,
        NPAExample,
        file_sha256,
        load_dataset,
        write_synthetic_jsonl,
    )


CHECKPOINT_FORMAT = "npa-training-checkpoint-v1"


def set_seed(seed: int) -> None:
    random.seed(seed)
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)


def resolve_device(specification: str | torch.device | None) -> torch.device:
    if isinstance(specification, torch.device):
        return specification
    value = "auto" if specification is None else str(specification).lower()
    if value == "auto":
        return torch.device("cuda" if torch.cuda.is_available() else "cpu")
    device = torch.device(value)
    if device.type == "cuda" and not torch.cuda.is_available():
        raise RuntimeError("CUDA requested but torch.cuda.is_available() is false")
    return device


def count_parameters(module: nn.Module) -> int:
    return sum(parameter.numel() for parameter in module.parameters() if parameter.requires_grad)


def model_config_from_vocab(vocab: DatasetVocab) -> dict[str, int]:
    if not vocab.constants:
        raise ValueError(
            "dataset has no constants; PaperAlignedNPA needs a non-empty constant vocabulary"
        )
    return {
        "num_constants": len(vocab.constants),
        # The model requires a positive relation count even for edge-free graphs.
        "num_relations": max(1, len(vocab.relations)),
        "node_feature_dim": vocab.node_feature_dim,
    }


def build_model(vocab: DatasetVocab) -> PaperAlignedNPA:
    return PaperAlignedNPA(**model_config_from_vocab(vocab))


def move_graph(graph: ExprGraph, device: torch.device) -> ExprGraph:
    return ExprGraph(
        node_kinds=graph.node_kinds.to(device),
        edge_index=graph.edge_index.to(device),
        edge_types=graph.edge_types.to(device),
        constant_ids=graph.constant_ids.to(device),
        node_features=graph.node_features.to(device),
    )


def move_candidates(candidates: CandidateSet, device: torch.device) -> CandidateSet:
    return CandidateSet(
        premise=type(candidates.premise)(
            candidates.premise.constant_ids.to(device),
            candidates.premise.mask.to(device),
        ),
        free_variable=type(candidates.free_variable)(
            candidates.free_variable.indices.to(device),
            candidates.free_variable.mask.to(device),
        ),
        locus=type(candidates.locus)(
            candidates.locus.indices.to(device),
            candidates.locus.mask.to(device),
        ),
    )


@dataclass(frozen=True)
class LossComponents:
    loss: Tensor
    kind_loss: Tensor
    parameter_loss: Tensor
    kind_correct: bool
    parameter_correct: Mapping[str, bool]
    exact: bool


def example_loss(
    model: PaperAlignedNPA,
    example: NPAExample,
    device: torch.device,
) -> LossComponents:
    """Cross-entropy on Kind plus every labeled parameter head.

    The parameter term is the mean over labeled heads of their individual
    cross-entropies, so a tactic with four arguments does not dominate one with
    a single argument purely by parameter count.  Candidate masks have already
    been applied as ``-inf`` logits by the model.
    """

    graph = move_graph(example.graph, device)
    candidates = move_candidates(example.candidates, device)
    output = model.forward_prefix(
        graph,
        candidates,
        TacticPrefix(example.kind),
        parameters=example.labeled_parameters,
    )
    kind_target = torch.tensor([int(example.kind)], dtype=torch.long, device=device)
    kind_loss = F.cross_entropy(output.kind_logits.unsqueeze(0), kind_target)
    kind_correct = int(output.kind_logits.argmax().item()) == int(example.kind)

    parameter_losses: list[Tensor] = []
    parameter_correct: dict[str, bool] = {}
    for name, label in example.parameters.items():
        logits = output.parameter_logits[name]
        target = torch.tensor([label.target_index], dtype=torch.long, device=device)
        parameter_losses.append(F.cross_entropy(logits.unsqueeze(0), target))
        parameter_correct[name] = int(logits.argmax().item()) == label.target_index
    if parameter_losses:
        parameter_loss = torch.stack(parameter_losses).mean()
        loss = kind_loss + parameter_loss
    else:
        parameter_loss = output.kind_logits.new_zeros(())
        loss = kind_loss
    exact = kind_correct and all(parameter_correct.values())
    return LossComponents(
        loss=loss,
        kind_loss=kind_loss,
        parameter_loss=parameter_loss,
        kind_correct=kind_correct,
        parameter_correct=parameter_correct,
        exact=exact,
    )


def _new_metric_state() -> dict[str, Any]:
    return {
        "loss_sum": 0.0,
        "kind_loss_sum": 0.0,
        "parameter_loss_sum": 0.0,
        "examples": 0,
        "kind_correct": 0,
        "parameter_correct": {},
        "parameter_total": {},
        "exact_correct": 0,
    }


def _accumulate_metrics(state: dict[str, Any], components: LossComponents) -> None:
    state["examples"] += 1
    state["loss_sum"] += float(components.loss.detach())
    state["kind_loss_sum"] += float(components.kind_loss.detach())
    state["parameter_loss_sum"] += float(components.parameter_loss.detach())
    state["kind_correct"] += int(components.kind_correct)
    state["exact_correct"] += int(components.exact)
    for name, correct in components.parameter_correct.items():
        state["parameter_correct"][name] = state["parameter_correct"].get(name, 0) + int(correct)
        state["parameter_total"][name] = state["parameter_total"].get(name, 0) + 1


def _finalize_metrics(state: dict[str, Any]) -> dict[str, Any]:
    total = state["examples"]
    if total == 0:
        return {
            "examples": 0,
            "loss": None,
            "kind_loss": None,
            "parameter_loss": None,
            "kind_accuracy": None,
            "parameter_accuracy": {},
            "exact_tactic_accuracy": None,
        }
    parameter_accuracy = {
        name: {
            "correct": state["parameter_correct"][name],
            "total": state["parameter_total"][name],
            "accuracy": state["parameter_correct"][name] / state["parameter_total"][name],
        }
        for name in sorted(state["parameter_total"])
    }
    return {
        "examples": total,
        "loss": state["loss_sum"] / total,
        "kind_loss": state["kind_loss_sum"] / total,
        "parameter_loss": state["parameter_loss_sum"] / total,
        "kind_accuracy": state["kind_correct"] / total,
        "parameter_accuracy": parameter_accuracy,
        "exact_tactic_accuracy": state["exact_correct"] / total,
    }


@torch.no_grad()
def evaluate_examples(
    model: PaperAlignedNPA,
    examples: Sequence[NPAExample],
    device: torch.device,
) -> dict[str, Any]:
    """Kind, per-parameter, and full tactic-prefix metrics."""

    was_training = model.training
    model.eval()
    state = _new_metric_state()
    try:
        for example in examples:
            _accumulate_metrics(state, example_loss(model, example, device))
    finally:
        model.train(was_training)
    return _finalize_metrics(state)


def _parameter_head_grad_max_abs(model: PaperAlignedNPA) -> dict[str, float]:
    values: dict[str, float] = {}
    for module_name in ("pointer_query", "pointer_key", "category_heads"):
        module = getattr(model, module_name)
        for name, parameter in module.named_parameters():
            key = f"{module_name}.{name}"
            if parameter.grad is None:
                values[key] = 0.0
            else:
                values[key] = float(parameter.grad.detach().abs().max())
    return values


def _merge_grad_stats(accumulated: dict[str, float], current: Mapping[str, float]) -> None:
    for name, value in current.items():
        accumulated[name] = max(accumulated.get(name, 0.0), value)


def save_checkpoint(
    path: str | Path,
    model: PaperAlignedNPA,
    vocab: DatasetVocab,
    training_metadata: Mapping[str, Any] | None = None,
) -> str:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "format": CHECKPOINT_FORMAT,
        "model_state": {
            name: tensor.detach().cpu() for name, tensor in model.state_dict().items()
        },
        "model_config": {
            "num_constants": model.num_constants,
            "num_relations": model.num_relations,
            "node_feature_dim": model.node_feature_dim,
        },
        "vocab": vocab.to_json(),
        "training": dict(training_metadata or {}),
        "saved_at": datetime.now(timezone.utc).isoformat(),
    }
    torch.save(payload, path)
    return file_sha256(path)


def load_checkpoint(
    path: str | Path,
    device: str | torch.device = "cpu",
) -> tuple[PaperAlignedNPA, DatasetVocab, dict[str, Any]]:
    path = Path(path)
    payload = torch.load(path, map_location="cpu", weights_only=False)
    if not isinstance(payload, Mapping) or payload.get("format") != CHECKPOINT_FORMAT:
        raise ValueError(f"{path}: not an {CHECKPOINT_FORMAT} checkpoint")
    config = payload.get("model_config")
    vocab_payload = payload.get("vocab")
    if not isinstance(config, Mapping) or not isinstance(vocab_payload, Mapping):
        raise ValueError(f"{path}: checkpoint is missing model_config/vocab")
    vocab = DatasetVocab.from_json(vocab_payload)
    expected = model_config_from_vocab(vocab)
    if dict(config) != expected:
        raise ValueError(f"{path}: model_config is inconsistent with the stored vocabulary")
    model = PaperAlignedNPA(**expected)
    model.load_state_dict(payload["model_state"], strict=True)
    model.to(resolve_device(device))
    model.eval()
    return model, vocab, dict(payload)


def _device_metadata(device: torch.device) -> dict[str, Any]:
    metadata: dict[str, Any] = {
        "device": str(device),
        "torch": torch.__version__,
        "python": platform.python_version(),
    }
    if device.type == "cuda":
        metadata["cuda_device_name"] = torch.cuda.get_device_name(device)
        metadata["cuda_capability"] = list(torch.cuda.get_device_capability(device))
    return metadata


def train_model(
    *,
    output_dir: str | Path,
    data_path: str | Path | None = None,
    data_kind: str | None = None,
    epochs: int = 20,
    batch_size: int = 8,
    lr: float = 3e-3,
    weight_decay: float = 1e-2,
    seed: int = 0,
    device: str | torch.device = "auto",
    limit: int | None = None,
    synthetic_states: int = 64,
    synthetic_seed: int = 0,
    states_per_theorem: int = 4,
    quiet: bool = False,
) -> dict[str, Any]:
    """Train one model and write checkpoint.pt + training-summary.json."""

    started = time.perf_counter()
    if epochs < 1 or batch_size < 1:
        raise ValueError("epochs and batch_size must be positive")
    if lr <= 0 or weight_decay < 0:
        raise ValueError("lr must be positive and weight_decay nonnegative")
    if limit is not None and limit < 1:
        raise ValueError("limit must be positive when provided")
    if data_kind is None:
        data_kind = "synthetic" if data_path is None else "sample"
    if data_kind not in ("synthetic", "sample"):
        raise ValueError("data_kind must be 'synthetic' or 'sample'")

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    if data_path is None:
        data_path = output_dir / "synthetic-sample.jsonl"
        write_synthetic_jsonl(
            data_path,
            count=synthetic_states,
            seed=synthetic_seed,
            states_per_theorem=states_per_theorem,
        )
    dataset = load_dataset(data_path)

    train_examples = list(dataset.split("train"))
    validation_examples = list(dataset.split("validation"))
    test_examples = list(dataset.split("test"))
    if not train_examples:
        raise ValueError("dataset has no training examples")
    if limit is not None:
        train_examples = train_examples[:limit]
    if validation_examples:
        held_out_examples = validation_examples
        held_out_split = "validation"
    elif test_examples:
        held_out_examples = test_examples
        held_out_split = "test"
    else:
        held_out_examples = []
        held_out_split = None

    resolved_device = resolve_device(device)
    set_seed(seed)
    vocab = dataset.vocab
    model = build_model(vocab).to(resolved_device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr, weight_decay=weight_decay)
    parameter_count = count_parameters(model)

    history: list[dict[str, Any]] = []
    gradient_max: dict[str, float] = {}
    rng = random.Random(seed)
    for epoch in range(1, epochs + 1):
        model.train()
        order = list(range(len(train_examples)))
        rng.shuffle(order)
        for start in range(0, len(order), batch_size):
            batch_indices = order[start : start + batch_size]
            optimizer.zero_grad(set_to_none=True)
            for index in batch_indices:
                components = example_loss(model, train_examples[index], resolved_device)
                (components.loss / len(batch_indices)).backward()
            _merge_grad_stats(gradient_max, _parameter_head_grad_max_abs(model))
            optimizer.step()

        train_metrics = evaluate_examples(model, train_examples, resolved_device)
        held_out_metrics = (
            evaluate_examples(model, held_out_examples, resolved_device)
            if held_out_examples
            else None
        )
        record: dict[str, Any] = {
            "epoch": epoch,
            "train_loss": train_metrics["loss"],
            "train_kind_accuracy": train_metrics["kind_accuracy"],
            "train_parameter_accuracy": {
                name: values["accuracy"]
                for name, values in train_metrics["parameter_accuracy"].items()
            },
            "train_exact_tactic_accuracy": train_metrics["exact_tactic_accuracy"],
            "held_out_split": held_out_split,
            "held_out_loss": held_out_metrics["loss"] if held_out_metrics else None,
            "held_out_kind_accuracy": (
                held_out_metrics["kind_accuracy"] if held_out_metrics else None
            ),
            "held_out_parameter_accuracy": (
                {
                    name: values["accuracy"]
                    for name, values in held_out_metrics["parameter_accuracy"].items()
                }
                if held_out_metrics
                else {}
            ),
            "held_out_exact_tactic_accuracy": (
                held_out_metrics["exact_tactic_accuracy"] if held_out_metrics else None
            ),
        }
        history.append(record)
        if not quiet:
            held_out_text = (
                f" held_out_exact={record['held_out_exact_tactic_accuracy']:.4f}"
                if record["held_out_exact_tactic_accuracy"] is not None
                else " held_out=n/a"
            )
            print(
                f"epoch {epoch:3d}/{epochs} train_loss={record['train_loss']:.4f} "
                f"train_kind={record['train_kind_accuracy']:.4f} "
                f"train_exact={record['train_exact_tactic_accuracy']:.4f}"
                f"{held_out_text}"
            )

    final_train = evaluate_examples(model, train_examples, resolved_device)
    final_validation = (
        evaluate_examples(model, validation_examples, resolved_device)
        if validation_examples
        else None
    )
    final_test = (
        evaluate_examples(model, test_examples, resolved_device) if test_examples else None
    )
    final_held_out = final_validation if final_validation is not None else final_test

    checkpoint_path = output_dir / "checkpoint.pt"
    summary_path = output_dir / "training-summary.json"
    training_metadata = {
        "data_kind": data_kind,
        "data_path": str(data_path),
        "data_sha256": dataset.source_sha256,
        "epochs": epochs,
        "batch_size": batch_size,
        "lr": lr,
        "weight_decay": weight_decay,
        "seed": seed,
        "limit": limit,
        "parameter_count": parameter_count,
        "history": history,
    }
    checkpoint_sha = save_checkpoint(checkpoint_path, model, vocab, training_metadata)

    curve_path = output_dir / "loss-curve.csv"
    with curve_path.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(
            [
                "epoch",
                "train_loss",
                "train_kind_accuracy",
                "train_exact_tactic_accuracy",
                "held_out_loss",
                "held_out_kind_accuracy",
                "held_out_exact_tactic_accuracy",
            ]
        )
        for record in history:
            writer.writerow(
                [
                    record["epoch"],
                    record["train_loss"],
                    record["train_kind_accuracy"],
                    record["train_exact_tactic_accuracy"],
                    record["held_out_loss"],
                    record["held_out_kind_accuracy"],
                    record["held_out_exact_tactic_accuracy"],
                ]
            )

    summary: dict[str, Any] = {
        "experiment": "parameterized paper-aligned NPA supervised training (v1)",
        "paper_fidelity": False,
        "data_kind": data_kind,
        "data_warning": (
            "SYNTHETIC SAMPLE ONLY - not a real ExprGraph/Nazrin result"
            if data_kind == "synthetic"
            else "SAMPLE DATA - not a paper benchmark result"
        ),
        "data": {
            "path": str(data_path),
            "sha256": dataset.source_sha256,
            "examples": len(dataset),
            "split_counts": dataset.split_counts,
            "kind_counts": dataset.kind_counts,
            "source_kind_counts": dataset.source_kind_counts,
            "train_examples_used": len(train_examples),
            "held_out_split": held_out_split,
            "held_out_examples": len(held_out_examples),
        },
        "model": {
            "class": type(model).__name__,
            "hidden_dim": 32,
            "layers": 5,
            "heads": 4,
            "activation": "GELU",
            "parameter_count": parameter_count,
            "num_constants": model.num_constants,
            "num_relations": model.num_relations,
            "node_feature_dim": model.node_feature_dim,
        },
        "training": {
            "optimizer": "AdamW",
            "loss": "cross_entropy(kind) + mean(cross_entropy(parameter))",
            "epochs": epochs,
            "batch_size": batch_size,
            "lr": lr,
            "weight_decay": weight_decay,
            "seed": seed,
            "batching": "one graph at a time, gradients accumulated per batch",
        },
        "history": history,
        "final": {
            "train": final_train,
            "validation": final_validation,
            "test": final_test,
            "held_out_split": held_out_split,
            "held_out_exact_tactic_accuracy": (
                final_held_out["exact_tactic_accuracy"] if final_held_out else None
            ),
        },
        "parameter_head_grad_max_abs": dict(sorted(gradient_max.items())),
        "parameter_heads_with_nonzero_grad": sum(
            1 for value in gradient_max.values() if value > 0.0
        ),
        "parameter_heads_total": len(gradient_max),
        "checkpoint": {
            "path": str(checkpoint_path),
            "sha256": checkpoint_sha,
            "format": CHECKPOINT_FORMAT,
        },
        "runtime": {
            **_device_metadata(resolved_device),
            "elapsed_seconds": time.perf_counter() - started,
        },
        "notes": [
            "Synthetic/sample smoke test; do not report these numbers as paper or real-data metrics.",
            "Real ExprGraph/Nazrin JSONL data is not connected in this version.",
            "Graphs are processed individually with gradient accumulation; no cross-graph padding yet.",
            "define/have/let/raw source tactics map to TacticKind.OTHER and their payloads are not scored.",
        ],
    }
    summary["artefacts"] = {
        "checkpoint": str(checkpoint_path),
        "summary": str(summary_path),
        "loss_curve": str(curve_path),
    }
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    return summary


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=None, help="JSONL dataset; omit to use synthetic sample")
    parser.add_argument("--data-kind", choices=("synthetic", "sample"), default=None)
    parser.add_argument("--output-dir", type=Path, default=Path("experiments/npa_training/runs/latest"))
    parser.add_argument("--epochs", type=int, default=20)
    parser.add_argument("--batch-size", type=int, default=8)
    parser.add_argument("--lr", type=float, default=3e-3)
    parser.add_argument("--weight-decay", type=float, default=1e-2)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--device", default="auto")
    parser.add_argument("--limit", type=int, default=None, help="cap training examples used per epoch")
    parser.add_argument("--synthetic-states", type=int, default=64)
    parser.add_argument("--synthetic-seed", type=int, default=0)
    parser.add_argument("--states-per-theorem", type=int, default=4)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_arg_parser().parse_args(argv)
    summary = train_model(
        output_dir=args.output_dir,
        data_path=args.data,
        data_kind=args.data_kind,
        epochs=args.epochs,
        batch_size=args.batch_size,
        lr=args.lr,
        weight_decay=args.weight_decay,
        seed=args.seed,
        device=args.device,
        limit=args.limit,
        synthetic_states=args.synthetic_states,
        synthetic_seed=args.synthetic_seed,
        states_per_theorem=args.states_per_theorem,
    )
    print(
        f"wrote {summary['checkpoint']['path']} and "
        f"{summary['artefacts']['summary']} "
        f"({summary['runtime']['elapsed_seconds']:.2f}s)"
    )
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
