from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "verify_source.py"
SPEC = importlib.util.spec_from_file_location("verify_source", SCRIPT)
assert SPEC and SPEC.loader
verify_source = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verify_source)
MATHLIB_COMMIT = "b" * 40
TOOLCHAIN = "leanprover/lean4:v4.29.1\n"


class VerifySourceTests(unittest.TestCase):
    def make_fixture(self, root: Path) -> tuple[Path, Path, str]:
        source, runtime = root / "source", root / "runtime"
        (source / "Standalone").mkdir(parents=True)
        runtime.mkdir()
        atomizer = ("import Nazrin.Atomization\nimport Pantograph\n\nopen Lean Nazrin\n\n"
                    "def envKeyParallelism := \"TEST\"\n\n"
                    "open Pantograph Atomization in\ndef integratedAtomize := upstreamAlgorithm\n\n"
                    "def atomizeTask := upstreamRunner\n")
        base = {"lean-toolchain": TOOLCHAIN, "lakefile.lean": "import Lake\nopen Lake DSL\npackage nazrin\n",
                "lake-manifest.json": '{"packages": []}\n', "Standalone/Atomizer.lean": atomizer}
        for name, text in base.items():
            (source / name).write_text(text)
        subprocess.run(["git", "init", "-q", str(source)], check=True)
        subprocess.run(["git", "-C", str(source), "add", "."], check=True)
        subprocess.run(["git", "-C", str(source), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "-c", "commit.gpgsign=false", "commit", "-qm", "Fixture"], check=True)
        commit = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
        files = {"Standalone/AtomizerWorker.lean": "import Standalone.AtomizerCore\n",
                 "Standalone/Inventory.lean": "-- independent inventory\n",
                 "script/atomize_mathlib_bounded.py": "# independent supervisor\n",
                 "mathlib-project/lean-toolchain": TOOLCHAIN,
                 "mathlib-project/lakefile.toml": 'name = "fixture"\n',
                 "mathlib-project/lake-manifest.json": json.dumps({"packages": [
                     {"name": "mathlib", "rev": MATHLIB_COMMIT, "type": "git",
                      "url": "https://github.com/leanprover-community/mathlib4"}]})}
        entries = []
        for name, text in files.items():
            path = runtime / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            entries.append({"path": name, "destination": name, "sha256": verify_source.sha256(path.read_bytes())})
        manifest = {"schema": 1, "source_commit": commit, "mathlib_commit": MATHLIB_COMMIT,
                    "lean_toolchain": TOOLCHAIN.strip(), "files": entries,
                    "upstream_sha256": {name: verify_source.sha256(text.encode()) for name, text in base.items()}}
        (runtime / "manifest.json").write_text(json.dumps(manifest))
        return source, runtime, commit

    def test_assembly_preserves_upstream_algorithm_and_records_separate_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source, runtime, commit = self.make_fixture(Path(temp))
            original = (source / "Standalone/Atomizer.lean").read_bytes()
            result = verify_source.assemble(source, commit, MATHLIB_COMMIT, runtime)
            self.assertEqual(result["source_commit"], commit)
            self.assertEqual(result["mathlib_commit"], MATHLIB_COMMIT)
            self.assertEqual(result["toolchain"], TOOLCHAIN.strip())
            self.assertEqual(result["runtime_manifest_sha256"], hashlib.sha256((runtime / "manifest.json").read_bytes()).hexdigest())
            self.assertEqual((source / "Standalone/Atomizer.lean").read_bytes(), original)
            core = (source / "Standalone/AtomizerCore.lean").read_text()
            self.assertIn("integratedAtomize := upstreamAlgorithm", core)
            self.assertNotIn("envKeyParallelism", core)
            self.assertNotIn("atomizeTask", core)
            self.assertEqual(verify_source.verify(source, commit, MATHLIB_COMMIT, runtime), result)
            self.assertFalse((source / ".nazrin-actions-compatible.json").exists())

    def test_unsupported_source_and_mathlib_fail_before_assembly(self) -> None:
        for source_pin, mathlib_pin, error in (("a" * 40, MATHLIB_COMMIT, "source_ref"),
                                               (None, "c" * 40, "mathlib_commit")):
            with self.subTest(error=error), tempfile.TemporaryDirectory() as temp:
                source, runtime, commit = self.make_fixture(Path(temp))
                with self.assertRaisesRegex(ValueError, error):
                    verify_source.assemble(source, source_pin or commit, mathlib_pin, runtime)
                self.assertFalse((source / "Standalone/AtomizerWorker.lean").exists())

    def test_runtime_payload_digest_is_checked_before_installing(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source, runtime, commit = self.make_fixture(Path(temp))
            (runtime / "Standalone/AtomizerWorker.lean").write_text("tampered")
            with self.assertRaisesRegex(ValueError, "extension digest mismatch"):
                verify_source.assemble(source, commit, MATHLIB_COMMIT, runtime)
            self.assertFalse((source / "Standalone/AtomizerCore.lean").exists())

    def test_dirty_checkout_is_not_overwritten(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source, runtime, commit = self.make_fixture(Path(temp))
            (source / "local-output").write_text("keep")
            with self.assertRaisesRegex(ValueError, "clean upstream checkout"):
                verify_source.assemble(source, commit, MATHLIB_COMMIT, runtime)
            self.assertEqual((source / "local-output").read_text(), "keep")

    def test_installed_extension_and_upstream_edits_are_rejected(self) -> None:
        for name, error in (("Standalone/AtomizerWorker.lean", "assembled runtime digest"),
                            ("Standalone/Atomizer.lean", "tracked source was modified"),
                            ("lakefile.lean", "worktree file digest")):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temp:
                source, runtime, commit = self.make_fixture(Path(temp))
                verify_source.assemble(source, commit, MATHLIB_COMMIT, runtime)
                with (source / name).open("a") as handle:
                    handle.write("-- changed\n")
                with self.assertRaisesRegex(ValueError, error):
                    verify_source.verify(source, commit, MATHLIB_COMMIT, runtime)

    def test_symlinked_payload_and_escape_destinations_are_rejected(self) -> None:
        for malicious in ("../outside", ".git/config", "/tmp/absolute"):
            with self.subTest(path=malicious), tempfile.TemporaryDirectory() as temp:
                source, runtime, commit = self.make_fixture(Path(temp))
                manifest_path = runtime / "manifest.json"
                manifest = json.loads(manifest_path.read_text())
                manifest["files"][0]["path"] = malicious
                manifest_path.write_text(json.dumps(manifest))
                with self.assertRaisesRegex(ValueError, "invalid runtime path"):
                    verify_source.assemble(source, commit, MATHLIB_COMMIT, runtime)

    def test_provenance_cannot_be_forged_without_matching_files(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source, runtime, commit = self.make_fixture(Path(temp))
            verify_source.assemble(source, commit, MATHLIB_COMMIT, runtime)
            (source / verify_source.REPORT).write_text('{}')
            with self.assertRaisesRegex(ValueError, "provenance mismatch"):
                verify_source.verify(source, commit, MATHLIB_COMMIT, runtime)

    def test_different_git_head_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            source, runtime, commit = self.make_fixture(Path(temp))
            subprocess.run(["git", "-C", str(source), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                            "-c", "commit.gpgsign=false", "commit", "--allow-empty", "-qm", "Changed HEAD"], check=True)
            with self.assertRaisesRegex(ValueError, "Codeberg commit does not match"):
                verify_source.assemble(source, commit, MATHLIB_COMMIT, runtime)


if __name__ == "__main__":
    unittest.main()
