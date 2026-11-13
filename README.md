# Nazrin Actions orchestration

This repository contains independent runner extensions and one manual GitHub Actions workflow, [mathlib-atomization.yml](.github/workflows/mathlib-atomization.yml). At runtime it fetches the official Nazrin base directly from Codeberg, assembles the extensions in a disposable checkout, builds the worker, exports the full pinned Mathlib inventory, assigns deterministic theorem shards, and packages verified results. Upstream source is neither mirrored here nor included in uploaded result artifacts.

## Reproducible runtime assembly

[runtime/manifest.json](runtime/manifest.json) pins the supported upstream base, Lean toolchain, Mathlib commit, upstream build-file digests, and every independent extension digest:

- Official source: `https://codeberg.org/aniva/Nazrin.git` at `e34a0535fc767479f7939a98f5699b1a6513a919`.
- Lean: `leanprover/lean4:v4.29.1`.
- Mathlib: `5e932f97dd25535344f80f9dd8da3aab83df0fe6`, with all transitive Git dependencies locked in the supplied Lake manifest.

[verify_source.py](scripts/verify_source.py) requires a clean checkout at the supported source SHA, verifies the upstream and extension file digests, installs the new worker/inventory/supervisor/project files, and appends only the two required Lake build targets. It extracts `integratedAtomize` and its imports directly from the verified upstream atomizer at runtime. The upstream algorithm is unchanged, and its source is not copied into this repository. The original upstream files remain intact except for the appended Lake targets.

The assembly records both identities in `.nazrin-actions-runtime.json`; its source SHA describes the base, while its runtime manifest digest and assembled-file digests describe the installed extensions. This replaces the previous, unsatisfiable requirement that upstream provide our local extensions and a `.nazrin-actions-compatible.json` marker. The verifier runs again after build, and setup confirms the installed Mathlib Git HEAD matches the requested SHA.

Before the full inventory is generated, [smoke_runtime.py](scripts/smoke_runtime.py) exercises the real built worker and durable supervisor with two small theorem fixtures importing `Mathlib`. Every fixture must produce a validated successful trace. Failure blocks the full shard matrix. Runtime provenance, the integration report, and logs are preserved under the plan artifact for diagnosis. This fixture is an integration check; the subsequent full scan has no theorem sampling or limit.

## Dispatch inputs

Run **Mathlib atomization** from **Actions → Mathlib atomization → Run workflow**. Inputs are:

- `source_repository`: fixed to `https://codeberg.org/aniva/Nazrin.git`; other repositories and forge URLs are rejected.
- `source_ref`: full supported upstream commit SHA, default `e34a0535fc767479f7939a98f5699b1a6513a919`. Supporting another base requires reviewing and updating the runtime manifest.
- `mathlib_commit`: full Mathlib commit SHA, default `5e932f97dd25535344f80f9dd8da3aab83df0fe6`; it must match the runtime manifest.
- `shard_count`: 1–128, default 10.
- `max_parallel`: 1–10, default 10. Reduce this when runner quota or resources require it.
- `scan_minutes`: 1–300 per shard, default 300. Effective scan time reserves time for setup, shutdown, and upload.
- `runner_label`: default `ubuntu-24.04`; a configured self-hosted Linux x64 runner label may be used with sufficient disk and memory.

At the pinned Mathlib revision the known candidate universe is **324004 theorems** (261651 Mathlib-owned and 62353 dependency-owned). The generated canonical TSV and its digest are authoritative. Shard assignment uses the first 64 bits of `SHA256(module + NUL + theorem)` modulo shard count. The full canonical inventory and every shard TSV are retained.

## Runtime model

Prepare runs the orchestration tests, assembles the pinned runtime, downloads the Mathlib cache, builds the worker, verifies actual worker execution, exports the complete inventory, and plans shards. Each shard separately assembles and builds the identical pinned runtime because jobs do not share filesystems. Shard setup sets `GENERATE_INVENTORY=false`; it does not regenerate the full inventory or run the prepare integration fixture. Setup exports `NAZRIN_DIR`, `MATHLIB_PROJECT_DIR`, `ELAN_HOME`, `LEAN_PATH`, `FULL_INVENTORY`, and both base commit identities through `GITHUB_ENV`, and the elan binary directory through `GITHUB_PATH`. The shard runner derives the Lake workspace `LEAN_PATH` and prepends the built Nazrin/Pantograph libraries.

Each shard runs one theorem worker at a time with two Lean internal task workers. The theorem deadline is fixed at **30 seconds**; worker startup/import has a separate 180-second allowance. The 10 GiB `RLIMIT_AS` limit bounds virtual address space, not reserved physical RAM. Prior local measurements were roughly 6–7 GiB RSS and can vary. Setup requires at least 10 GiB free disk initially and 2 GiB after build/cache work; these are minimum guards rather than a complete capacity estimate.

Shard jobs have a 350-minute wall-clock cap and reserve 15 minutes for shutdown/upload. Requested `scan_minutes` is an upper bound reduced by elapsed setup time. Shard setup is capped at 75 minutes; prepare setup at 300 minutes, within a six-hour job cap. Timeouts, theorem failures, crashes, and invalid symbols count as attempted terminal outcomes rather than successful proofs. Import failures, malformed or missing artifacts, and unattempted candidates remain pending.

Ten shards are not expected to finish 324004 candidates in one batch. At 30 seconds for every theorem, each of ten balanced shards would need about 270 hours before import/recycle overhead. A budget cutoff retains the full shard input, ledger, summary, and exact pending inventory. A new Actions dispatch creates a fresh plan; it does not resume a previous run. Cross-run continuation requires explicit validation and preservation of matching runtime provenance, binary, manifests, limits, inventory, and state.

The default hosted runner is CPU-only. This Lean atomization workload does not use an RTX 2070; assigning a GPU alone does not accelerate it. No CUDA workload is added.

## Results and recovery

Plan and shard artifact names are stable across attempts of the same run and include run/source/Mathlib identities. Package names additionally include the attempt. Uploads include hidden supervisor state. A rerun restores the prior plan and shard directory; `overwrite: true` replaces them only after successful restoration on later attempts. Restore failure blocks scanning and replacement uploads to preserve earlier results. If no original artifact exists, use a new dispatch.

Budget cutoffs return success after saving state, so use **Re-run all jobs** to resume these shards; **Re-run failed jobs** may rerun only packaging. Package runs with `always()`, recomputes coverage from immutable inputs, ledger, and actual artifacts, validates the exact canonical partition, and retains incomplete diagnostics before returning failure. Failed/interrupted shards retain independently validated committed terminal outcomes. Missing artifacts and identity/summary mismatches contribute no coverage. Symlinks are omitted and replaced with rejection notes.

The package includes `nazrin-atomization-results.tar.gz`, `package-report.json`, and `pending-inventory.tsv`, preserving available plan and shard inventories/results under separate namespaces. If planning fails, it includes an explicit incomplete report and a header-only pending TSV. A header-only pending TSV means the candidate universe was unavailable, not that nothing remains.

## Local checks

```bash
python3 -B -m unittest discover -s tests -v
bash -n scripts/setup_runtime.sh
```

Tests use temporary fixtures and do not run Lean or alter an existing scan. A clean cloud bootstrap and the real worker integration check establish whether the selected runtime can proceed to the full scan.
