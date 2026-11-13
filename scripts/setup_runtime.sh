#!/usr/bin/env bash
set -Eeuo pipefail

: "${NAZRIN_SOURCE_REF:?Set the full Codeberg base commit SHA supported by runtime/manifest.json}"
: "${MATHLIB_COMMIT:?Set the pinned Mathlib commit SHA}"
: "${RUNNER_TEMP:?RUNNER_TEMP must be set by GitHub Actions}"
: "${GITHUB_WORKSPACE:?GITHUB_WORKSPACE must be set by GitHub Actions}"
: "${GITHUB_ENV:?GITHUB_ENV must be set by GitHub Actions}"

if [[ ! "$NAZRIN_SOURCE_REF" =~ ^[0-9a-fA-F]{40}$ ]]; then
  printf 'NAZRIN_SOURCE_REF must be a full 40-character commit SHA\n' >&2
  exit 2
fi
if [[ ! "$MATHLIB_COMMIT" =~ ^[0-9a-fA-F]{40}$ ]]; then
  printf 'MATHLIB_COMMIT must be a full 40-character commit SHA\n' >&2
  exit 2
fi

NAZRIN_DIR="$RUNNER_TEMP/nazrin"
MATHLIB_PROJECT_DIR="$NAZRIN_DIR/mathlib-project"
ELAN_HOME="$RUNNER_TEMP/elan"
FULL_INVENTORY="$GITHUB_WORKSPACE/input/theorems.tsv"
GENERATE_INVENTORY="${GENERATE_INVENTORY:-true}"
if [[ "$GENERATE_INVENTORY" != true && "$GENERATE_INVENTORY" != false ]]; then
  printf 'GENERATE_INVENTORY must be true or false\n' >&2
  exit 2
fi
mkdir -p "$RUNNER_TEMP"
if [[ "$GENERATE_INVENTORY" == true ]]; then
  mkdir -p "$(dirname "$FULL_INVENTORY")"
fi

free_kib=$(df -Pk "$RUNNER_TEMP" | awk 'NR == 2 {print $4}')
if [[ ! "$free_kib" =~ ^[0-9]+$ ]] || (( free_kib < 10 * 1024 * 1024 )); then
  printf 'Need at least 10 GiB free on runner disk before Lean/Mathlib setup; found %s KiB\n' "${free_kib:-unknown}" >&2
  exit 3
fi

clone_commit() {
  local url=$1 commit=$2 destination=$3
  if [[ -e "$destination" ]]; then
    printf 'Refusing to overwrite existing checkout: %s\n' "$destination" >&2
    return 1
  fi
  git init -q "$destination"
  git -C "$destination" remote add origin "$url"
  git -C "$destination" fetch --quiet --depth=1 origin "$commit"
  git -C "$destination" checkout --quiet --detach FETCH_HEAD
  local actual
  actual=$(git -C "$destination" rev-parse HEAD)
  if [[ "${actual,,}" != "${commit,,}" ]]; then
    printf 'Fetched commit mismatch for %s: expected %s got %s\n' "$url" "$commit" "$actual" >&2
    return 1
  fi
}

NAZRIN_SOURCE_URL="${NAZRIN_SOURCE_URL:-https://codeberg.org/aniva/Nazrin.git}"
python3 - "$NAZRIN_SOURCE_URL" <<'PY'
import sys
from urllib.parse import urlsplit
url = urlsplit(sys.argv[1])
if (url.scheme != "https" or url.netloc != "codeberg.org" or url.query or url.fragment
        or url.path != "/aniva/Nazrin.git"):
    raise SystemExit("NAZRIN_SOURCE_URL must be https://codeberg.org/aniva/Nazrin.git")
PY
clone_commit "$NAZRIN_SOURCE_URL" "$NAZRIN_SOURCE_REF" "$NAZRIN_DIR"
python3 "$GITHUB_WORKSPACE/scripts/verify_source.py" \
  --source "$NAZRIN_DIR" \
  --expected-commit "$NAZRIN_SOURCE_REF" \
  --expected-mathlib-commit "$MATHLIB_COMMIT" --assemble

TOOLCHAIN=$(<"$NAZRIN_DIR/lean-toolchain")
mkdir -p "$ELAN_HOME"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl --retry 3 --retry-delay 2 --connect-timeout 20 --max-time 180 \
    -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | ELAN_HOME="$ELAN_HOME" sh -s -- -y --default-toolchain "$TOOLCHAIN" --no-modify-path
fi
export ELAN_HOME
export PATH="$ELAN_HOME/bin:$PATH"
printf '%s\n' "$ELAN_HOME/bin" >> "${GITHUB_PATH:?GITHUB_PATH must be set by GitHub Actions}"

if [[ "$(<"$MATHLIB_PROJECT_DIR/lean-toolchain")" != "$TOOLCHAIN" ]]; then
  printf 'Mathlib project toolchain does not match Nazrin toolchain\n' >&2
  exit 4
fi

export LEAN_TASK_MANAGER_WORKERS=2
(
  cd "$MATHLIB_PROJECT_DIR"
  lake exe cache get
)
(
  cd "$NAZRIN_DIR"
  lake build AtomizerWorker
)

python3 "$GITHUB_WORKSPACE/scripts/verify_source.py" \
  --source "$NAZRIN_DIR" --expected-commit "$NAZRIN_SOURCE_REF" \
  --expected-mathlib-commit "$MATHLIB_COMMIT"
actual_mathlib_commit=$(git -C "$MATHLIB_PROJECT_DIR/.lake/packages/mathlib" rev-parse HEAD)
if [[ "${actual_mathlib_commit,,}" != "${MATHLIB_COMMIT,,}" ]]; then
  printf 'Installed Mathlib checkout does not match requested commit\n' >&2
  exit 4
fi

# Keep the supervisor's Lake environment and the worker's Mathlib dependency on
# the same manifest, then add Nazrin/Pantograph modules built at the same commit.
MATHLIB_LEAN_PATH=$(cd "$MATHLIB_PROJECT_DIR" && lake env printenv LEAN_PATH)
NAZRIN_LEAN_PATH="$NAZRIN_DIR/.lake/build/lib/lean"
while IFS= read -r package_dir; do
  package_lib="$package_dir/.lake/build/lib/lean"
  if [[ -d "$package_lib" ]]; then
    NAZRIN_LEAN_PATH="$NAZRIN_LEAN_PATH:$package_lib"
  fi
done < <(find "$NAZRIN_DIR/.lake/packages" -mindepth 1 -maxdepth 1 -type d -print 2>/dev/null | sort)
export LEAN_PATH="$NAZRIN_LEAN_PATH:$MATHLIB_LEAN_PATH"

# Exercise the real worker/Mathlib import and durable supervisor protocol before
# generating the full inventory or launching a long-running shard.
if [[ "$GENERATE_INVENTORY" == true ]]; then
  mkdir -p "$GITHUB_WORKSPACE/plan"
  cp "$NAZRIN_DIR/.nazrin-actions-runtime.json" "$GITHUB_WORKSPACE/plan/runtime-provenance.json"
  python3 "$GITHUB_WORKSPACE/scripts/smoke_runtime.py" \
    --source "$NAZRIN_DIR" --project "$MATHLIB_PROJECT_DIR" \
    --output "$GITHUB_WORKSPACE/plan/integration-attempt-${GITHUB_RUN_ATTEMPT:-1}"
  (
    cd "$MATHLIB_PROJECT_DIR"
    lake env lean --run "$NAZRIN_DIR/Standalone/Inventory.lean" "$FULL_INVENTORY" Mathlib
  )
fi

free_kib=$(df -Pk "$RUNNER_TEMP" | awk 'NR == 2 {print $4}')
printf 'Runner free space after setup: %s KiB\n' "$free_kib"
if [[ ! "$free_kib" =~ ^[0-9]+$ ]] || (( free_kib < 2 * 1024 * 1024 )); then
  printf 'Less than 2 GiB free after setup; stopping before theorem workers start\n' >&2
  exit 3
fi

{
  printf 'ELAN_HOME=%s\n' "$ELAN_HOME"
  printf 'NAZRIN_DIR=%s\n' "$NAZRIN_DIR"
  printf 'MATHLIB_PROJECT_DIR=%s\n' "$MATHLIB_PROJECT_DIR"
  printf 'NAZRIN_COMMIT=%s\n' "$NAZRIN_SOURCE_REF"
  printf 'MATHLIB_COMMIT=%s\n' "$MATHLIB_COMMIT"
  printf 'LEAN_TOOLCHAIN=%s\n' "$TOOLCHAIN"
  printf 'LEAN_TASK_MANAGER_WORKERS=2\n'
  printf 'LEAN_PATH=%s\n' "$LEAN_PATH"
  printf 'FULL_INVENTORY=%s\n' "$FULL_INVENTORY"
} >> "$GITHUB_ENV"
printf 'Pinned Codeberg base plus verified independent Actions runtime setup completed.\n'
