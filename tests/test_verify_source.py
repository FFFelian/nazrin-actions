from __future__ import annotations

import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "verify_source.py"
SPEC = importlib.util.spec_from_file_location("verify_source", SCRIPT)
assert SPEC and SPEC.loader
verify_source = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verify_source)
MATHLIB_COMMIT = "b" * 40


class VerifySourceTests(unittest.TestCase):
    def make_source(self, root: Path, *, marker: bool = True) -> str:
        for relative in verify_source.REQUIRED_FILES:
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("lean_exe AtomizerWorker\n", encoding="utf-8")
        for directory in (root, root / "mathlib-project"):
            (directory / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n", encoding="utf-8")
        manifest = {"packages": [{"name": "mathlib", "type": "git", "rev": MATHLIB_COMMIT,
                                  "url": "https://github.com/leanprover-community/mathlib4.git"}]}
        (root / "mathlib-project/lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        if marker:
            value = {
                "schema": 1,
                "worker": "Standalone/AtomizerWorker.lean",
                "core": "Standalone/AtomizerCore.lean",
                "inventory": "Standalone/Inventory.lean",
                "supervisor": "script/atomize_mathlib_bounded.py",
                "lean_toolchain": "leanprover/lean4:v4.29.1",
            }
            (root / ".nazrin-actions-compatible.json").write_text(json.dumps(value), encoding="utf-8")
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        subprocess.run(["git", "-C", str(root), "add", "."], check=True)
        subprocess.run(["git", "-C", str(root), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "-c", "commit.gpgsign=false", "commit", "-qm", "Fixture"], check=True)
        return subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()

    def test_compatible_pinned_checkout_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp)
            commit = self.make_source(source)
            result = verify_source.verify(source, commit, MATHLIB_COMMIT)
            self.assertEqual(result["source_commit"], commit)
            self.assertEqual(result["mathlib_commit"], MATHLIB_COMMIT)
            self.assertEqual(result["toolchain"], "leanprover/lean4:v4.29.1")

    def test_missing_contract_marker_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp)
            commit = self.make_source(source, marker=False)
            with self.assertRaisesRegex(ValueError, "missing .nazrin-actions-compatible.json"):
                verify_source.verify(source, commit, MATHLIB_COMMIT)

    def test_commit_mismatch_is_rejected_even_with_forged_commit_file(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp)
            self.make_source(source)
            (source / ".git/NAZRIN_ACTIONS_SOURCE_COMMIT").write_text("a" * 40)
            with self.assertRaisesRegex(ValueError, "does not match requested source_ref"):
                verify_source.verify(source, "a" * 40, MATHLIB_COMMIT)

    def test_mathlib_pin_mismatch_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp)
            commit = self.make_source(source)
            with self.assertRaisesRegex(ValueError, "does not match requested mathlib_commit"):
                verify_source.verify(source, commit, "c" * 40)

    def test_non_object_marker_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp)
            commit = self.make_source(source)
            (source / ".nazrin-actions-compatible.json").write_text("[]")
            with self.assertRaisesRegex(ValueError, "schema=1"):
                verify_source.verify(source, commit, MATHLIB_COMMIT)

    def test_toolchains_must_match(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source = Path(temp)
            commit = self.make_source(source)
            (source / "mathlib-project/lean-toolchain").write_text("leanprover/lean4:v4.28.0\n")
            with self.assertRaisesRegex(ValueError, "Mathlib project toolchain"):
                verify_source.verify(source, commit, MATHLIB_COMMIT)


if __name__ == "__main__":
    unittest.main()
