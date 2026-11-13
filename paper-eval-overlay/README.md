# Paper-aligned NPA proof evaluation overlay

This directory is a byte-for-byte snapshot of the local paper-aligned NPA
proof-search sources plus the 15-second evaluation manifest. The
`paper-proof-eval.yml` workflow copies the files into a disposable, pinned
Nazrin checkout, appends `lakefile.append`, builds `NPARepl`, and runs
`experiments.npa_search.run_eval` on deterministic shards. It never writes to
the upstream checkout in place and never uploads a checkpoint to an artifact.

## Provenance and version

| Item | Value |
| --- | --- |
| Local source tree | `/home/felian/lab/Nazrin/nazrin-repo` |
| Snapshot date | 2026-11-14 |
| Upstream base | `e34a0535fc767479f7939a98f5699b1a6513a919` (`https://codeberg.org/aniva/Nazrin.git`) |
| Lean toolchain | `leanprover/lean4:v4.29.1` |
| Mathlib commit | `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| Evaluation manifest | `paper-slices/slice-01.tsv`, **20,603 data rows + 1 header** |
| Checkpoint requirement | HTTPS URL plus a required 64-hex SHA256 digest |

The local files were untracked working-tree files, so this overlay is identified
by the content digests in `SHA256SUMS`, not by a Git commit. The workflow runs
`sha256sum -c SHA256SUMS` before installing any file.

```text
$ (cd paper-eval-overlay && sha256sum -c SHA256SUMS)
```

The manifest header is `index\ttheorem\tmodule\tslice\ttopo_rank`; the first data
row starts at index 167. The full header is preserved by
`scripts/plan_paper_shards.py`, which creates contiguous, non-overlapping shard
TSVs without sampling or truncation.

## Contents

| Path | Purpose |
| --- | --- |
| `Standalone/NPARepl.lean` | JSON-line Lean REPL over Pantograph's string-tactic API |
| `Standalone/GoalGraphCore.lean` | Goal graph builder used by the REPL and `ExprGraph` export |
| `Standalone/ExprGraphExport.lean` | Offline goal-graph exporter kept for reprocessing trace data |
| `Standalone/AtomizerCore.lean` | Fallback copy; `setup_runtime.sh` normally assembles this target first |
| `experiments/npa_search/` | Search engine, REPL client, and `run_eval.py` |
| `experiments/npa_training/` | Checkpoint model, dataset loader, and training/evaluation helpers |
| `experiments/paper_aligned_npa.py` | Paper-aligned model and tactic-parameter schema |
| `experiments/npa_data/convert_trace.py` | Trace converter imported by `search.py` |
| `paper-slices/slice-01.tsv` | 20,603-theorem evaluation manifest |
| `lakefile.append` | `GoalGraphCore` library and `NPARepl` executable declarations |

## Lake targets

The pinned upstream lakefile has neither `GoalGraphCore` nor `NPARepl`.
`lakefile.append` therefore declares both:

```lean
lean_lib GoalGraphCore {
  roots := #[`Standalone.GoalGraphCore]
}

lean_exe NPARepl {
  root := `Standalone.NPARepl
  supportInterpreter := true
}
```

`scripts/setup_runtime.sh` already assembles `Standalone/AtomizerCore.lean` and
its Lake target. The overlay's `AtomizerCore` copy is a fallback only and is not
allowed to overwrite the runtime-generated file.

## Workflow dispatch

The workflow is manual only. Example:

```bash
gh workflow run paper-proof-eval.yml \
  --ref main \
  -f checkpoint_url=https://github.com/OWNER/REPO/releases/download/TAG/checkpoint.pt \
  -f checkpoint_sha256=0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef \
  -f shard_count=10 \
  -f max_parallel=10 \
  -f time_limit=15 \
  -f max_steps=100 \
  -f top_k=5
```

Optional overrides are `theorems` (default
`paper-eval-overlay/paper-slices/slice-01.tsv`), `source_ref`, `mathlib_commit`,
and `runner_label`. The defaults pin the official base
`e34a0535fc767479f7939a98f5699b1a6513a919` and Mathlib
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`.

The prepare job downloads and verifies the checkpoint, records its digest and
size in `plan/checkpoint.json`, and uploads only that metadata with the shard
plan. Each shard independently downloads the checkpoint from the same HTTPS URL
and verifies the same SHA256 before evaluating anything.

## Evaluation command

`import Mathlib` resolves through Mathlib's Lake search path, which contains
the Mathlib build directory **and** every transitive dependency (`Batteries`,
`Qq`, `Aesop`, `ProofWidgets`, `importGraph`, and so on). Pointing `LEAN_PATH`
only at
`$MATHLIB_PROJECT_DIR/.lake/packages/mathlib/.lake/build/lib/lean` is not
sufficient; the REPL fails with
`failed to import Mathlib: unknown module prefix 'Batteries'`.

Run the evaluation from `$MATHLIB_PROJECT_DIR` and derive the complete
`LEAN_PATH` from that project's Lake environment, keeping the Nazrin and
Pantograph build directories first:

```bash
cd "$MATHLIB_PROJECT_DIR"
export PYTHONPATH="$NAZRIN_DIR${PYTHONPATH:+:$PYTHONPATH}"
MATHLIB_LEAN_PATH=$(cd "$MATHLIB_PROJECT_DIR" && lake env printenv LEAN_PATH)
export LEAN_PATH="$NAZRIN_DIR/.lake/build/lib/lean:$NAZRIN_DIR/.lake/packages/pantograph/.lake/build/lib/lean:$MATHLIB_LEAN_PATH"

python3 -m experiments.npa_search.run_eval \
  --checkpoint "$RUNNER_TEMP/checkpoint/checkpoint.pt" \
  --module Mathlib \
  --theorems "$GITHUB_WORKSPACE/plan/shard-00.tsv" \
  --output-dir "$GITHUB_WORKSPACE/outputs/shard-0" \
  --time-limit 15 \
  --max-steps 100 \
  --top-k 5 \
  --device cpu
```

Every workflow shard uses exactly this environment: the shard step runs from
`$MATHLIB_PROJECT_DIR`, preserves `PYTHONPATH=$NAZRIN_DIR`, and exports
`LEAN_PATH` with `MATHLIB_LEAN_PATH` appended. `MATHLIB_PROJECT_DIR` is
exported by `scripts/setup_runtime.sh`; manual runs must `cd` into it before
invoking `run_eval` so Lake resolves the Mathlib manifest rather than the
Nazrin one.

The REPL launcher is pinned to the Mathlib project through a small `LAKE`
wrapper that changes directory to `$MATHLIB_PROJECT_DIR` before invoking
`lake env lean --run "$NAZRIN_DIR/Standalone/NPARepl.lean" Mathlib`. This keeps
the Python package rooted at `$NAZRIN_DIR` while ensuring the imported Lean
workspace is the Mathlib project.

## Outputs

Each shard uploads `results.jsonl`, `summary.json`, `shard.tsv`, and
`checkpoint.json`. The package job merges results only from shards whose TSV
digest, theorem list, result statuses, per-status counts, summary counts,
checkpoint digest, and run parameters all validate. It writes:

- `results.jsonl` — merged records in plan order.
- `evaluation-summary.json` — total/success/failure/timeout/error counts,
  success rate, checkpoint digest, and evaluation parameters.
- `evaluation-report.json` — completeness, issues, missing/invalid shards, and
  per-shard validation details.

The package job uploads its artifact before failing an incomplete run, so
diagnostics remain available.

## Deliberate limitations

- **No shared build cache:** every shard performs its own `setup_runtime.sh`,
  Mathlib cache download, and `lake build NPARepl`; there is no cross-shard
  Mathlib build cache.
- **CPU only:** the workflow installs `torch==2.6.0` from the PyTorch CPU index.
  No CUDA device is requested or used.
- **Checkpoint URL must be reachable:** the URL is user-supplied and must be an
  HTTPS GitHub release asset, artifact URL, or equivalent; authentication is
  the caller's responsibility. The checkpoint is not stored in this repository
  and is not uploaded as an Actions artifact.
- **15-second budget scope:** `--time-limit 15` applies to proof search after
  the theorem is submitted to an already-imported REPL. Lean process startup
  and Mathlib module import are outside that per-theorem budget, matching
  `run_eval.py`.
- **No resumability:** a new dispatch creates a fresh plan and fresh shards;
  partial shard results are reported but are not combined across runs.
- **Shard bounds:** 1–20 shards. With 20,603 theorems and a separate Mathlib
  REPL per theorem, a full run is expected to take many hours per shard even
  before process-startup overhead.
- **Mock policy is not used:** the workflow always requires and verifies a real
  checkpoint, and rejects summaries whose `policy` is not `npa` or whose
  `mock` flag is true.
