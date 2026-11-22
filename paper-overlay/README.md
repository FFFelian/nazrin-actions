# Paper trace overlay

This directory is a byte-for-byte snapshot of the local paper-trace exporter
sources plus the `slice-00` theorem list. The workflow copies these files into
the disposable, pinned Nazrin checkout, appends `lakefile.append`, and builds
`PaperTraceExport` there. It never writes to the upstream checkout in place.

## Provenance and version

| Item | Value |
| --- | --- |
| Local source tree | `/home/felian/lab/Nazrin/nazrin-repo` |
| Snapshot date | 2026-11-14 |
| Upstream base | `e34a0535fc767479f7939a98f5699b1a6513a919` (`https://codeberg.org/aniva/Nazrin.git`) |
| Lean toolchain | `leanprover/lean4:v4.29.1` |
| Mathlib commit | `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| Slice input | `paper-slices/slice-00.tsv`, 20,602 data rows + 1 header |

The local files were untracked working-tree files, so their overlay version is
the content digest below, not a Git commit. `SHA256SUMS` is verified by the
workflow before any file is installed:

```text
7dbb38faaa18f6511ba312322646b4b275c2327e311eac220ef36e5a95f7815f  Standalone/GoalGraphCore.lean
04f319093093c3d05ac2f246cb0ee62a9e4a7bd96089aa662f5b2b03ffea5947  Standalone/ExprGraphExport.lean
4940c1fdc8efc3ff1411572aea96fcbf605c1a40f9e52b321e1f29a4247c5401  Standalone/PaperTraceExport.lean
39c862ce2b0d0d1de479d6198936025afbd67a49eeea021b1c3b42ee9a55eabb  Standalone/AtomizerCore.lean
d96edffb5ecfdc5c0b6ff6d066c52b56f5ac7960e05ac6f7ad25eb9c1e0a3fab  experiments/npa_data/convert_trace.py
0ab3c6cf58267d9cfa738dd40345994cc32511db0c6f56ec2f3312a345c6a2b1  paper-slices/slice-00.tsv
```

`Standalone/AtomizerCore.lean` is included because the pinned upstream base
does not provide it, and `PaperTraceExport` imports it. The base also lacks
`GoalGraphCore`, `PaperTraceExport`, and `ExprGraphExport`.

## Lake targets

`scripts/setup_runtime.sh` already assembles `Standalone/AtomizerCore.lean`
and its `lean_lib AtomizerCore` target. `lakefile.append` therefore declares
only the missing `GoalGraphCore` library and the `ExprGraphExport` and
`PaperTraceExport` executables. The workflow appends the file exactly once to
a fresh checkout and verifies both executable declarations. The overlay's
`AtomizerCore` copy is a fallback only: the workflow does not overwrite the
runtime-generated file when it is already present.

## Schema-4 structured trace additions

[`schema4-trace-export.yml`](../.github/workflows/schema4-trace-export.yml)
exports the schema-4 atomization trace (`Standalone/StructuredTraceV4.lean`)
with up to 20 parallel shards. It reuses `scripts/setup_runtime.sh` and
`scripts/plan_paper_shards.py`, then runs one isolated Lean process per
theorem through `scripts/run_schema4_shard.py`.

The schema-4 exporter needs five overlay files that were not part of the old
trace snapshot:

| File | Why it is installed |
| --- | --- |
| `Standalone/StructuredTraceV4.lean` | per-theorem schema-4 JSONL exporter (`schema_version` 4) |
| `Standalone/ExprGraphV3.lean` | schema-3 ExprGraph of the full pre-step goal state (§V-A pp.6-7) |
| `Standalone/ExprGraphV2.lean` | direct import of `ExprGraphV3`; not in the pinned base |
| `experiments/exprgraph/v3/validate_exprgraph_v3.py` | graph validator used by the schema-4 checker |
| `experiments/npa_data/validate_structured_v4.py` | independent schema-4 record checker (merge job, report only) |

`Standalone/GoalGraphCore.lean` and `Standalone/AtomizerCore.lean` are already
overlay/runtime files (`AtomizerCore` is assembled from the upstream atomizer
by `verify_source.py`). A second append file,
[`lakefile.schema4.append`](lakefile.schema4.append), declares the
`ExprGraphV2`/`ExprGraphV3` libraries and the `StructuredTraceV4` executable.
It is kept separate from `lakefile.append` so the old exporter workflow never
sees a Lake target whose root file it does not install.

`scripts/setup_runtime.sh` and the runtime assembly are unchanged: the new
modules are copied after assembly into the same disposable checkout. Every
file is listed in `SHA256SUMS` and verified before installation; the local
source bytes are the origin of the copy, as with the old snapshot.

## Deliberate exclusions

- `.lake/`, build products, caches, and checkpoints.
- `mathlib-atomization/` and other generated/scan data.
- `experiments/paper-slices/dependency-edges.tsv`, other slices, and `.work/`.
- The NPA support modules imported by `convert_trace.py`. That converter is
  carried for the follow-on proof-eval/NPA work but is not executed by this
  workflow; it needs `experiments/paper_aligned_npa.py` and
  `experiments/npa_training/dataset.py` from the local research tree.

## Reuse

The slice TSV keeps all five columns (`index`, `theorem`, `module`, `slice`,
`topo_rank`). `scripts/plan_paper_shards.py` preserves the full header and rows,
so another theorem-list TSV with a `theorem` column can be sharded without
changing the Lean side. For proof-eval, substitute the input path and keep the
same overlay/build/package contract.
