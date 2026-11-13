#!/usr/bin/env python3
"""Assemble and verify a pinned upstream checkout plus independent CI extensions."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

RUNTIME = Path(__file__).resolve().parents[1] / "runtime"
REPORT = ".nazrin-actions-runtime.json"
UPSTREAM_FILES = ("lean-toolchain", "lakefile.lean", "lake-manifest.json", "Standalone/Atomizer.lean")
TARGETS = """

-- Independent Actions runtime targets; the upstream algorithm is unchanged.
lean_lib AtomizerCore {
  roots := #[`Standalone.AtomizerCore]
}
lean_exe AtomizerWorker {
  root := `Standalone.AtomizerWorker
  supportInterpreter := true
}
"""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(source: Path, *arguments: str) -> bytes:
    try:
        return subprocess.check_output(["git", "-C", str(source), *arguments], stderr=subprocess.PIPE, timeout=30)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise ValueError("cannot verify upstream Git checkout") from exc


def regular(path: Path) -> bytes:
    if path.is_symlink() or not path.is_file() or any(parent.is_symlink() for parent in path.parents):
        raise ValueError(f"expected a regular file without symlink parents: {path}")
    return path.read_bytes()


def safe_path(root: Path, name: str) -> Path:
    relative = PurePosixPath(name)
    if not name or relative.is_absolute() or any(part in {"..", ".git", ".lake"} for part in relative.parts):
        raise ValueError(f"invalid runtime path: {name!r}")
    path = root / name
    if any(parent.is_symlink() for parent in [path, *path.parents]):
        raise ValueError(f"runtime path contains a symlink: {name!r}")
    return path


def load_manifest(runtime: Path, expected_commit: str, expected_mathlib_commit: str | None) -> tuple[dict, bytes]:
    for label, value in (("source_ref", expected_commit), ("mathlib_commit", expected_mathlib_commit)):
        if value is not None and not re.fullmatch(r"[0-9a-fA-F]{40}", value):
            raise ValueError(f"{label} must be a full 40-character Git SHA")
    raw = regular(runtime / "manifest.json")
    manifest = json.loads(raw)
    if not isinstance(manifest, dict) or manifest.get("schema") != 1:
        raise ValueError("runtime manifest must have schema=1")
    if manifest.get("source_commit") != expected_commit.lower():
        raise ValueError("runtime does not support requested source_ref")
    if expected_mathlib_commit is not None and manifest.get("mathlib_commit") != expected_mathlib_commit.lower():
        raise ValueError("runtime does not match requested mathlib_commit")
    if set(manifest.get("upstream_sha256", {})) != set(UPSTREAM_FILES):
        raise ValueError("runtime must pin the upstream build and atomizer files")
    files = manifest.get("files")
    required = {"Standalone/AtomizerWorker.lean", "Standalone/Inventory.lean", "script/atomize_mathlib_bounded.py",
                "mathlib-project/lakefile.toml", "mathlib-project/lake-manifest.json", "mathlib-project/lean-toolchain"}
    if not isinstance(files, list) or {entry.get("destination") for entry in files} != required or len(files) != len(required):
        raise ValueError("runtime file destinations do not match the integration contract")
    for entry in files:
        data = regular(safe_path(runtime, entry["path"]))
        if sha256(data) != entry["sha256"]:
            raise ValueError(f"runtime extension digest mismatch: {entry['path']}")
    return manifest, raw


def core_from_upstream(atomizer: bytes) -> bytes:
    text = atomizer.decode("utf-8")
    prefix = "def envKeyParallelism"
    start = "open Pantograph Atomization in\ndef integratedAtomize"
    end = "\ndef atomizeTask"
    if any(text.count(boundary) != 1 for boundary in (prefix, start, end)):
        raise ValueError("upstream atomizer extraction boundaries changed")
    return (text[:text.index(prefix)] + text[text.index(start):text.index(end)]).encode("utf-8")


def expected_files(source: Path, runtime: Path, manifest: dict, *, assembled: bool) -> dict[str, bytes]:
    actual_root = Path(git(source, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    actual_commit = git(source, "rev-parse", "--verify", "HEAD").decode().strip().lower()
    if source != actual_root or actual_commit != manifest["source_commit"]:
        raise ValueError("checked-out Codeberg commit does not match requested source_ref")
    changed = set(git(source, "diff", "HEAD", "--name-only").decode().splitlines())
    if changed - ({"lakefile.lean"} if assembled else set()):
        raise ValueError("upstream tracked source was modified outside runtime assembly")
    upstream = {}
    for name, digest in manifest["upstream_sha256"].items():
        committed = git(source, "show", f"HEAD:{name}")
        if sha256(committed) != digest:
            raise ValueError(f"upstream committed file digest mismatch: {name}")
        expected = committed + TARGETS.encode() if assembled and name == "lakefile.lean" else committed
        if regular(safe_path(source, name)) != expected:
            raise ValueError(f"upstream worktree file digest mismatch: {name}")
        upstream[name] = committed
    if upstream["lean-toolchain"].decode().strip() != manifest["lean_toolchain"]:
        raise ValueError("upstream Lean toolchain does not match runtime")
    output = {entry["destination"]: regular(safe_path(runtime, entry["path"])) for entry in manifest["files"]}
    output["Standalone/AtomizerCore.lean"] = core_from_upstream(upstream["Standalone/Atomizer.lean"])
    output["lakefile.lean"] = upstream["lakefile.lean"] + TARGETS.encode()
    if output["mathlib-project/lean-toolchain"].decode().strip() != manifest["lean_toolchain"]:
        raise ValueError("Mathlib project toolchain does not match runtime")
    lake_manifest = json.loads(output["mathlib-project/lake-manifest.json"])
    entries = [entry for entry in lake_manifest["packages"] if entry.get("name") == "mathlib"]
    if len(entries) != 1 or entries[0].get("rev") != manifest["mathlib_commit"] or entries[0].get("type") != "git" or entries[0].get("url", "").removesuffix(".git") != "https://github.com/leanprover-community/mathlib4":
        raise ValueError("Mathlib manifest does not pin the requested official commit")
    if any(entry.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", entry.get("rev", "")) for entry in lake_manifest["packages"]):
        raise ValueError("all Mathlib workspace dependencies must pin full Git SHAs")
    return output


def provenance(manifest: dict, raw: bytes, files: dict[str, bytes]) -> dict:
    return {"schema": 1, "source_commit": manifest["source_commit"], "mathlib_commit": manifest["mathlib_commit"],
            "toolchain": manifest["lean_toolchain"], "runtime_manifest_sha256": sha256(raw),
            "assembled_files_sha256": {name: sha256(data) for name, data in sorted(files.items())}}


def assemble(source: Path, expected_commit: str, expected_mathlib_commit: str, runtime: Path = RUNTIME) -> dict:
    source, runtime = source.resolve(), runtime.resolve()
    manifest, raw = load_manifest(runtime, expected_commit, expected_mathlib_commit)
    if git(source, "status", "--porcelain", "--untracked-files=all").strip():
        raise ValueError("assembly requires a clean upstream checkout")
    files = expected_files(source, runtime, manifest, assembled=False)
    # Validate every destination before mutating this disposable checkout.
    for name in [*files, REPORT]:
        path = safe_path(source, name)
        if name != "lakefile.lean" and path.exists():
            raise ValueError(f"refusing to overwrite an existing extension: {name}")
    for name, data in files.items():
        path = safe_path(source, name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    result = provenance(manifest, raw, files)
    (source / REPORT).write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return verify(source, expected_commit, expected_mathlib_commit, runtime)


def verify(source: Path, expected_commit: str, expected_mathlib_commit: str | None = None, runtime: Path = RUNTIME) -> dict:
    source, runtime = source.resolve(), runtime.resolve()
    manifest, raw = load_manifest(runtime, expected_commit, expected_mathlib_commit)
    files = expected_files(source, runtime, manifest, assembled=True)
    for name, data in files.items():
        if regular(safe_path(source, name)) != data:
            raise ValueError(f"assembled runtime digest mismatch: {name}")
    result = provenance(manifest, raw, files)
    if json.loads(regular(source / REPORT)) != result:
        raise ValueError("assembled runtime provenance mismatch")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--expected-mathlib-commit", required=True)
    parser.add_argument("--runtime", type=Path, default=RUNTIME)
    parser.add_argument("--assemble", action="store_true")
    args = parser.parse_args()
    try:
        operation = assemble if args.assemble else verify
        result = operation(args.source, args.expected_commit, args.expected_mathlib_commit, args.runtime)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
