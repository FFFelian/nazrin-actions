#!/usr/bin/env python3
"""Fail fast unless a Codeberg revision exposes the required CI worker contract."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

REQUIRED_FILES = (
    "Standalone/AtomizerWorker.lean",
    "Standalone/AtomizerCore.lean",
    "Standalone/Inventory.lean",
    "script/atomize_mathlib_bounded.py",
    "lakefile.lean",
    "lake-manifest.json",
    "lean-toolchain",
    "mathlib-project/lakefile.toml",
    "mathlib-project/lake-manifest.json",
    "mathlib-project/lean-toolchain",
)
CONTRACT_FILE = ".nazrin-actions-compatible.json"


def verify(source: Path, expected_commit: str, expected_mathlib_commit: str | None = None) -> dict:
    source = source.resolve()
    for label, commit in (("source commit", expected_commit), ("Mathlib commit", expected_mathlib_commit)):
        if commit is not None and not re.fullmatch(r"[0-9a-fA-F]{40}", commit):
            raise ValueError(f"{label} must be a full 40-character Git SHA")
    missing = [name for name in REQUIRED_FILES if not (source / name).is_file()]
    if missing:
        raise ValueError("incompatible source revision; missing: " + ", ".join(missing))

    marker_path = source / CONTRACT_FILE
    if not marker_path.is_file():
        raise ValueError(
            f"incompatible source revision; missing {CONTRACT_FILE}. "
            "The ref must explicitly declare this independent Actions runner contract."
        )
    try:
        marker = json.loads(marker_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read {CONTRACT_FILE}: {exc}") from exc
    if not isinstance(marker, dict) or marker.get("schema") != 1:
        raise ValueError("source compatibility marker must have schema=1")
    expected_paths = {
        "worker": "Standalone/AtomizerWorker.lean",
        "core": "Standalone/AtomizerCore.lean",
        "inventory": "Standalone/Inventory.lean",
        "supervisor": "script/atomize_mathlib_bounded.py",
    }
    for key, value in expected_paths.items():
        if marker.get(key) != value:
            raise ValueError(f"{CONTRACT_FILE}: {key} must be {value!r}")

    lakefile = (source / "lakefile.lean").read_text(encoding="utf-8")
    if "lean_exe AtomizerWorker" not in lakefile:
        raise ValueError("source lakefile.lean must define the AtomizerWorker target")
    toolchain = (source / "lean-toolchain").read_text(encoding="utf-8").strip()
    if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(?:[-.][A-Za-z0-9]+)*", toolchain):
        raise ValueError("lean-toolchain must pin an explicit Lean release")
    if marker.get("lean_toolchain") != toolchain:
        raise ValueError("compatibility marker lean_toolchain does not match lean-toolchain")
    project = source / "mathlib-project"
    if (project / "lean-toolchain").read_text(encoding="utf-8").strip() != toolchain:
        raise ValueError("Mathlib project toolchain does not match source toolchain")
    try:
        manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ValueError("Mathlib project manifest is invalid JSON") from exc
    packages = manifest.get("packages", []) if isinstance(manifest, dict) else []
    if not isinstance(packages, list):
        raise ValueError("Mathlib project manifest packages must be a list")
    mathlib_entries = [entry for entry in packages if isinstance(entry, dict) and entry.get("name") == "mathlib"]
    if len(mathlib_entries) != 1:
        raise ValueError("Mathlib project manifest must contain exactly one mathlib dependency")
    mathlib = mathlib_entries[0]
    mathlib_commit = mathlib.get("rev", "")
    if not isinstance(mathlib_commit, str) or not re.fullmatch(r"[0-9a-fA-F]{40}", mathlib_commit):
        raise ValueError("Mathlib manifest revision must be a full 40-character Git SHA")
    if mathlib.get("type") != "git" or str(mathlib.get("url", "")).removesuffix(".git").rstrip("/") != "https://github.com/leanprover-community/mathlib4":
        raise ValueError("Mathlib dependency must use the official GitHub repository")
    if expected_mathlib_commit is not None and mathlib_commit.lower() != expected_mathlib_commit.lower():
        raise ValueError("Mathlib manifest commit does not match requested mathlib_commit")
    try:
        actual_commit = subprocess.check_output(
            ["git", "-C", str(source), "rev-parse", "--verify", "HEAD"],
            text=True, stderr=subprocess.PIPE, timeout=15,
        ).strip().lower()
        git_root = subprocess.check_output(
            ["git", "-C", str(source), "rev-parse", "--show-toplevel"],
            text=True, stderr=subprocess.PIPE, timeout=15,
        ).strip()
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise ValueError("source must be a checked-out Git revision") from exc
    if Path(git_root).resolve() != source or actual_commit != expected_commit.lower():
        raise ValueError("checked-out Codeberg commit does not match requested source_ref")
    return {"schema": 1, "source_commit": actual_commit, "mathlib_commit": mathlib_commit.lower(),
            "toolchain": toolchain, "marker": marker}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--expected-mathlib-commit", required=True)
    args = parser.parse_args()
    try:
        result = verify(args.source, args.expected_commit, args.expected_mathlib_commit)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
