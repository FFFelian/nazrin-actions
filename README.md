# Nazrin Actions orchestration bundle

This repository contains a manual-only GitHub Actions orchestration bundle. It fetches a compatible Nazrin source revision directly from Codeberg at an immutable commit, builds a full pinned Mathlib inventory, assigns deterministic theorem shards, runs one worker per job, and packages verified results. It does not mirror or upload the Nazrin source. The only workflow is [mathlib-atomization.yml](.github/workflows/mathlib-atomization.yml).

## Source compatibility

The current upstream revision is not claimed to satisfy the scanner contract. A source commit without the required files and `.nazrin-actions-compatible.json` fails verification before Lean installation, worker build, or inventory generation. Do not bypass that check or point the workflow at an unverified local checkout.

A compatible immutable revision must provide:

- `.nazrin-actions-compatible.json` with schema `1`, the exact worker/core/inventory/supervisor paths, and a `lean_toolchain` matching `lean-toolchain`.
- `Standalone/AtomizerWorker.lean`, `Standalone/AtomizerCore.lean`, `Standalone/Inventory.lean`, `script/atomize_mathlib_bounded.py`, and a `lakefile.lean` defining `lean_exe AtomizerWorker`.
- A committed `mathlib-project` Lake workspace whose toolchain matches the source and whose manifest pins exactly one official `leanprover-community/mathlib4` Git dependency to the requested full SHA.
- An inventory entry point accepting `OUTPUT_TSV MODULE`, exporting the complete `Mathlib` theorem universe with header `index\ttheorem\tmodule`.
- A bounded supervisor compatible with [run_shard.py](scripts/run_shard.py). It must resume from the immutable complete input and durable ledger, enforce a per-theorem deadline, write validated terminal artifacts, stop after import failure, and continue after theorem timeout/crash.

[verify_source.py](scripts/verify_source.py) checks the declared contract, source Git HEAD, both toolchains, worker target, and Mathlib project manifest. This check establishes identity and an explicit integration contract; it does not replace testing the worker itself.

## Dispatch inputs

Run **Mathlib atomization** from **Actions → Mathlib atomization → Run workflow**. Inputs are:

- `source_repository`: fixed to `https://codeberg.org/aniva/Nazrin.git`. Other repositories and Git forge URLs are rejected.
- `source_ref`: required full 40-character compatible source commit SHA.
- `mathlib_commit`: full 40-character Mathlib commit SHA; default `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. It must match the source workspace manifest.
- `shard_count`: 1–128, default 10.
- `max_parallel`: 1–10, default 10. Use fewer concurrent jobs when runner quota or resources require it.
- `scan_minutes`: 1–300 per shard, default 300. The workflow may lower the effective runtime to leave time for setup, shutdown, and upload.
- `runner_label`: default `ubuntu-24.04`. A configured self-hosted Linux x64 runner label may be used if it has sufficient disk, memory, and matching dependencies.

There is no theorem sample or limit. At the known pinned Mathlib revision, the expected candidate universe is **324004 theorems** (261651 Mathlib-owned and 62353 dependency-owned). The inventory is generated from the selected compatible source and Mathlib SHA, so the plan's actual row count and digest are authoritative. Shard assignment is stable: the first 64 bits of `SHA256(module + NUL + theorem)` modulo shard count. The full canonical TSV and every shard TSV are retained in the plan artifact.

## Runtime model

The prepare job runs orchestration tests, bootstraps the pinned source and Mathlib cache, builds the worker, exports the complete inventory, and plans shards. Each shard job separately fetches and builds the same pinned runtime because GitHub jobs do not share local filesystems. Shard setup sets `GENERATE_INVENTORY=false`; the complete inventory is not regenerated in every worker job. Setup writes `NAZRIN_DIR`, `MATHLIB_PROJECT_DIR`, `ELAN_HOME`, `LEAN_PATH`, `FULL_INVENTORY`, and both commit identities to `GITHUB_ENV`, and adds the elan binary directory through `GITHUB_PATH`. The shard runner then derives the Lake workspace `LEAN_PATH` and prepends the built Nazrin and package libraries.

Each shard runs exactly one `AtomizerWorker` process at a time with two Lean internal task workers. The fixed theorem timeout is **30 seconds**. Worker startup/import has a separate 180-second allowance. The default virtual address-space limit is 10 GiB (`RLIMIT_AS`), not reserved physical RAM. Prior local measurements were roughly 6–7 GiB RSS and can vary; choose runners with enough additional memory. Setup requires 10 GiB free disk initially and at least 2 GiB after build/cache work, which are minimum guards rather than a guarantee the complete run fits.

Shard jobs have a 350-minute wall-clock cap and reserve 15 minutes for shutdown and artifact upload. The requested `scan_minutes` is an upper bound; a runtime calculation immediately before scanning further reduces it according to elapsed setup time. The setup step itself is capped at 75 minutes. Prepare setup has a 300-minute cap and its job remains within GitHub's six-hour maximum. Timeouts, theorem failures, crashes, and invalid symbols are terminal attempted outcomes, not successful proofs. Import failures, missing/invalid artifacts, and unattempted candidates remain pending.

Ten shards are not expected to finish 324004 candidates in one batch. If every theorem used all 30 seconds, ten evenly sized shards would each need about 270 hours of scan time before import/recycle overhead. A budget cutoff keeps the original full shard input, ledger, summary, and exact pending inventory for that run. A new Actions dispatch creates a fresh plan; it does not resume/download a previous run. Any cross-run continuation must explicitly preserve and validate the matching source binary, project manifest, limits, inventory, and state.

The default hosted runner is CPU-only. Lean proof search here does not use an RTX 2070, so assigning a GPU runner alone does not accelerate the workflow. A self-hosted label is useful only if the compatible worker has an actual GPU-backed workload; no CUDA dependency or GPU code is added by this bundle.

## Results and integrity

Plan and shard artifacts use stable run-ID/source/Mathlib-qualified names; shard artifacts also include the shard ID. Package artifacts add the workflow attempt so each package remains available. Uploads include hidden files (`include-hidden-files: true`) so `.bounded-*` supervisor state is preserved. A rerun downloads the prior plan and shard directory before setup/resumption, allowing skipped successful jobs to be reused and failed shards to continue from their ledger. `overwrite: true` lets rerun jobs replace the same plan/shard artifact after restoring its contents. On attempts after the first, a restore failure blocks scanning and replacement uploads to preserve prior results; if no earlier artifact exists, start a fresh dispatch. Budget cutoffs return success after saving state, so use **Re-run all jobs** to resume those shards; **Re-run failed jobs** alone may rerun only packaging. The package job runs with `always()`, downloads available shards without merging their directories, recomputes coverage from the immutable input, ledger, and artifacts, and checks the exact canonical partition. Invalid shard identity cannot subtract rows from the pending inventory; missing, duplicate, unexpected, and mismatched artifacts make the package incomplete.

A failed or interrupted shard retains coverage for independently validated committed terminal outcomes while keeping the package incomplete. Missing artifacts and identity/summary mismatches do not count toward coverage. Package construction omits symlinks and includes rejection notes.

The final artifact contains:

- `nazrin-atomization-results.tar.gz`, with the plan/canonical/shard inventories and shard results under separate namespaces.
- `package-report.json`, with source identity, coverage, shard status, and validation issues.
- `pending-inventory.tsv`, listing every planned row without a validated terminal outcome.

If setup/planning fails before a plan exists, the workflow still packages an explicit incomplete diagnostic report and a header-only pending TSV. A header-only file means the candidate universe was unavailable, not that zero candidates are pending. The package is uploaded before incomplete coverage makes the workflow fail.

## Local checks

```bash
python3 -B -m unittest discover -s tests -v
bash -n scripts/setup_runtime.sh
```

The helper tests use temporary fixtures; they do not start Lean or affect the existing local scan. No Actions run was started, no source was mirrored, and no existing scan inventory or output was changed while preparing this bundle. A real Actions run still requires a compatible Codeberg source revision and a cold-runner bootstrap check.
