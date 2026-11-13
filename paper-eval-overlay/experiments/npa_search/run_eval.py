#!/usr/bin/env python3
"""Run the first-version NPA proof-search evaluation.

Examples
--------
Mock run (no model needed)::

    python experiments/npa_search/run_eval.py \
        --mock-policy --module Init \
        --theorems experiments/npa_search/theorems.tsv \
        --output-dir experiments/npa_search/runs/mock

Real checkpoint run::

    python experiments/npa_search/run_eval.py \
        --checkpoint experiments/npa_training/runs/init-prelude-sample/checkpoint.pt \
        --module Init --theorems theorems.tsv --output-dir runs/npa --device cpu

Success is decided only by the Lean REPL's ``solved: true``.  Model scores are
never used as proof evidence.
"""

from __future__ import annotations

import argparse
import csv
import json
import platform
import subprocess
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Sequence

try:
    from experiments.npa_training.dataset import file_sha256
    from experiments.npa_search.repl_client import ReplClient, find_lake
    from experiments.npa_search.search import (
        MockPolicy,
        NPAPolicy,
        SearchEngine,
        SearchResult,
        TacticPolicy,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from experiments.npa_training.dataset import file_sha256  # type: ignore
    from experiments.npa_search.repl_client import ReplClient, find_lake  # type: ignore
    from experiments.npa_search.search import (  # type: ignore
        MockPolicy,
        NPAPolicy,
        SearchEngine,
        SearchResult,
        TacticPolicy,
    )


REPO_ROOT = Path(__file__).resolve().parents[2]

#: `--mock-policy` with no explicit sequence uses these real Lean proofs.  The
#: evaluation summary always marks the policy as mock.
MOCK_SCRIPTS: dict[str, list[str]] = {
    "Nat.add_zero": ["intro h; rfl"],
    "Nat.le_of_succ_le": ["intro h h1 h2; exact Nat.le_trans (Nat.le_succ h) h2"],
    "And.comm": ["intro a b; constructor <;> intro h <;> exact ⟨h.right, h.left⟩"],
}


def load_theorems(path: str | Path) -> list[str]:
    """Read theorem names from a TSV with a ``theorem`` column.

    A header is optional; when no recognized header is present, the first
    column of every row is used.  Blank lines and ``#`` comments are skipped.
    """

    path = Path(path)
    with path.open(encoding="utf-8", newline="") as handle:
        rows = [row for row in csv.reader(handle, delimiter="\t") if any(cell.strip() for cell in row)]
    if not rows:
        return []
    header = [cell.strip().lower() for cell in rows[0]]
    column = 0
    if "theorem" in header:
        column = header.index("theorem")
        rows = rows[1:]
    elif "theorem_name" in header:
        column = header.index("theorem_name")
        rows = rows[1:]
    elif "name" in header:
        column = header.index("name")
        rows = rows[1:]
    names: list[str] = []
    for row in rows:
        if column >= len(row):
            continue
        name = row[column].strip()
        if not name or name.startswith("#"):
            continue
        names.append(name)
    return names


def parse_mock_sequence(specification: str | None, theorem: str) -> list[str]:
    """Turn ``--mock-policy`` into a fixed list of tactic strings."""

    if specification is None or specification == "auto":
        return list(MOCK_SCRIPTS.get(theorem, []))
    return [part.strip() for part in specification.split("||") if part.strip()]


def lean_toolchain_metadata() -> dict[str, Any]:
    metadata: dict[str, Any] = {
        "python": platform.python_version(),
        "platform": platform.platform(),
    }
    toolchain_file = REPO_ROOT / "lean-toolchain"
    if toolchain_file.is_file():
        metadata["lean_toolchain"] = toolchain_file.read_text(encoding="utf-8").strip()
    try:
        import torch

        metadata["torch"] = torch.__version__
    except Exception:  # pragma: no cover - torch is required for NPA runs
        metadata["torch"] = None
    try:
        lake = find_lake()
        metadata["lake"] = lake
        completed = subprocess.run(
            [lake, "env", "lean", "--version"],
            cwd=str(REPO_ROOT),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
        )
        metadata["lean_version"] = (completed.stdout or completed.stderr).strip() or None
    except Exception as exc:  # pragma: no cover - diagnostic only
        metadata["lean_version"] = None
        metadata["lean_version_error"] = str(exc)
    return metadata


def evaluate_one(
    *,
    theorem: str,
    module: str,
    policy_factory: Any,
    policy_label: str,
    time_limit: float,
    max_steps: int,
    top_k: int,
    heartbeat_limit: int = 200_000,
) -> SearchResult:
    """Run one theorem in a fresh REPL process.

    A fresh process isolates Lean state and makes a killed/timed-out tactic
    from one theorem unable to poison the next theorem.  Process startup is
    outside the per-theorem search budget; the budget starts when the theorem
    is submitted to the REPL.
    """

    client = ReplClient(
        module=module,
        max_heartbeats=heartbeat_limit,
        timeout=max(30.0, time_limit + 15.0),
    )
    try:
        try:
            client.start()
        except Exception as exc:
            return SearchResult(
                theorem=theorem,
                status="error",
                elapsed_ms=0.0,
                steps=0,
                error=f"could not start REPL: {exc}",
                policy=policy_label,
            )
        try:
            policy = policy_factory(theorem)
        except Exception as exc:
            return SearchResult(
                theorem=theorem,
                status="error",
                elapsed_ms=0.0,
                steps=0,
                error=f"could not create policy: {exc}",
                policy=policy_label,
            )
        engine = SearchEngine(
            client,
            policy,
            time_limit=time_limit,
            max_steps=max_steps,
            top_k=top_k,
        )
        return engine.prove(theorem)
    finally:
        try:
            client.close(timeout=5.0)
        except Exception:
            pass


def _json_result(result: SearchResult) -> dict[str, Any]:
    payload = result.to_dict()
    payload["elapsed_ms"] = round(float(payload["elapsed_ms"]), 3)
    return payload


def run_evaluation(args: argparse.Namespace) -> dict[str, Any]:
    started = time.perf_counter()
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    theorems = load_theorems(args.theorems)
    if args.limit is not None:
        if args.limit < 1:
            raise SystemExit("--limit must be positive")
        theorems = theorems[: args.limit]
    if not theorems:
        raise SystemExit(f"no theorem names found in {args.theorems}")

    checkpoint = Path(args.checkpoint) if args.checkpoint is not None else None
    mock = args.mock_policy is not None
    if not mock and (checkpoint is None or not checkpoint.is_file()):
        raise SystemExit("--checkpoint is required and must exist unless --mock-policy is used")
    checkpoint_sha = file_sha256(checkpoint) if checkpoint is not None and checkpoint.is_file() else None

    shared_policy: TacticPolicy | None = None
    if not mock:
        assert checkpoint is not None
        shared_policy = NPAPolicy(
            checkpoint, device=args.device, premise_scope=args.premise_scope
        )

    def policy_factory(theorem: str) -> TacticPolicy:
        if mock:
            return MockPolicy(parse_mock_sequence(args.mock_policy, theorem))
        assert shared_policy is not None
        return shared_policy

    results: list[dict[str, Any]] = []
    results_path = output_dir / "results.jsonl"
    with results_path.open("w", encoding="utf-8") as handle:
        for index, theorem in enumerate(theorems, start=1):
            print(f"[{index}/{len(theorems)}] {theorem}", file=sys.stderr, flush=True)
            result = evaluate_one(
                theorem=theorem,
                module=args.module,
                policy_factory=policy_factory,
                policy_label="mock" if mock else "npa",
                time_limit=args.time_limit,
                max_steps=args.max_steps,
                top_k=args.top_k,
            )
            payload = _json_result(result)
            results.append(payload)
            handle.write(json.dumps(payload, ensure_ascii=False) + "\n")
            handle.flush()

    counts = {"success": 0, "failure": 0, "timeout": 0, "error": 0}
    reason_counts: Counter[str] = Counter()
    for payload in results:
        status = payload["status"]
        counts[status] = counts.get(status, 0) + 1
        for failure in payload.get("failures", []):
            reason = str(failure.get("reason", "")).strip().splitlines()
            if reason:
                reason_counts[reason[0][:160]] += 1
    total = len(results)
    summary = {
        "experiment": "NPA proof search evaluation (v1)",
        "paper_fidelity": False,
        "policy": "mock" if mock else "npa",
        "premise_scope": args.premise_scope,
        "mock": mock,
        "mock_sequence": args.mock_policy if mock else None,
        "checkpoint": {
            "path": str(checkpoint) if checkpoint is not None else None,
            "sha256": checkpoint_sha,
            "exists": bool(checkpoint is not None and checkpoint.is_file()),
        },
        "checkpoint_sha256": checkpoint_sha,
        "module": args.module,
        "theorems_file": str(args.theorems),
        "total": total,
        "success": counts.get("success", 0),
        "failure": counts.get("failure", 0),
        "timeout": counts.get("timeout", 0),
        "error": counts.get("error", 0),
        "success_rate": (counts.get("success", 0) / total) if total else 0.0,
        "failure_reason_counts": dict(reason_counts.most_common(10)),
        "time_limit_seconds": args.time_limit,
        "time_limit": args.time_limit,
        "max_steps": args.max_steps,
        "top_k": args.top_k,
        "device": args.device,
        "results_path": str(results_path),
        "elapsed_seconds": round(time.perf_counter() - started, 3),
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "toolchain": lean_toolchain_metadata(),
        "notes": [
            "success means the Lean REPL returned solved:true; model scores are never proof evidence",
            (
                "premise_scope=graph: premise candidates are graph constants only; "
                "--premise-scope global instead uses the whole checkpoint constant vocabulary"
                if args.premise_scope == "graph"
                else "premise candidates are all constants in the checkpoint vocabulary; this approximates "
                "global premise retrieval but is not a definition-graph fixed-point encoding and cannot "
                "propose constants outside the checkpoint vocabulary"
            ),
            "mock runs are marked policy=mock and must not be reported as model results",
        ],
    }
    summary_path = output_dir / "summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return summary


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", type=Path, default=None, help="NPA checkpoint.pt")
    parser.add_argument("--module", default="Init", help="Lean module imported by the REPL")
    parser.add_argument("--theorems", type=Path, required=True, help="TSV containing a theorem column")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--time-limit", type=float, default=15.0, help="wall-clock seconds per theorem")
    parser.add_argument("--max-steps", type=int, default=100, help="maximum tactic attempts per theorem")
    parser.add_argument("--top-k", type=int, default=5, help="candidate tactics decoded per state")
    parser.add_argument("--limit", type=int, default=None, help="evaluate only the first N theorems")
    parser.add_argument("--device", default="cpu", help="torch device for the checkpoint (cpu/cuda/auto)")
    parser.add_argument(
        "--premise-scope",
        choices=("graph", "global"),
        default="graph",
        help=(
            "premise candidates: 'graph' uses goal-graph constants only; "
            "'global' uses the whole checkpoint constant vocabulary"
        ),
    )
    parser.add_argument(
        "--mock-policy",
        nargs="?",
        const="auto",
        default=None,
        help="use a fixed tactic sequence (omit value for built-in scripts; separate steps with '||')",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)
    if args.time_limit <= 0:
        parser.error("--time-limit must be positive")
    if args.max_steps < 1:
        parser.error("--max-steps must be positive")
    if args.top_k < 1:
        parser.error("--top-k must be positive")
    summary = run_evaluation(args)
    print(
        f"policy={summary['policy']} success={summary['success']}/{summary['total']} "
        f"failure={summary['failure']} timeout={summary['timeout']} error={summary['error']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
