from __future__ import annotations

import argparse
from contextlib import redirect_stderr, redirect_stdout
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]


def load_script(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


smoke = load_script("smoke_runtime", ROOT / "scripts/smoke_runtime.py")
bounded = load_script("bounded_smoke", ROOT / "runtime/atomize_mathlib_bounded.py")


class SmokeRuntimeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.source = root / "source with spaces"
        self.project = self.source / "mathlib-project"
        self.output = root / "smoke-output"
        worker = self.source / ".lake/build/bin/AtomizerWorker"
        worker.parent.mkdir(parents=True)
        worker.write_bytes(b"mock worker; never execute\n")
        supervisor = self.source / "script/atomize_mathlib_bounded.py"
        supervisor.parent.mkdir(parents=True)
        supervisor.write_text("# mocked supervisor; never execute\n", encoding="utf-8")
        (self.source / ".nazrin-actions-runtime.json").write_text(json.dumps({
            "source_commit": "a" * 40, "mathlib_commit": "b" * 40,
            "runtime_manifest_sha256": "c" * 64,
        }), encoding="utf-8")
        self.project.mkdir()
        for directory in (self.source, self.project):
            (directory / "lean-toolchain").write_text("leanprover/lean4:v4.29.1\n", encoding="utf-8")
        (self.project / "lake-manifest.json").write_text('{"packages": []}\n', encoding="utf-8")
        self.environment = {"PATH": "/mock/bin", "LEAN_PATH": "/mock/nazrin:/mock/mathlib"}

    def completed_fixture(self, command, **kwargs):
        # This is the external supervisor contract: no Lean subprocess is used.
        self.assertEqual(Path(command[1]), self.source / "script/atomize_mathlib_bounded.py")
        self.assertEqual(Path(command[2]), self.output / "fixture-inventory.tsv")
        self.assertEqual(Path(command[3]), self.output)
        options = dict(zip(command[4::2], command[5::2]))
        self.assertEqual(options, {
            "--project": str(self.project),
            "--worker": str(self.source / ".lake/build/bin/AtomizerWorker"),
            "--timeout-seconds": "30",
            "--startup-timeout-seconds": "180",
            "--max-heartbeats": "200000",
            "--memory-gib": "10",
            "--lean-workers": "2",
            "--import-module": "Mathlib",
        })
        self.assertEqual(kwargs["cwd"], self.project)
        self.assertEqual(kwargs["env"]["LEAN_PATH"], self.environment["LEAN_PATH"])
        self.assertEqual(kwargs["env"]["LEAN_TASK_MANAGER_WORKERS"], "2")
        self.assertEqual(kwargs["stderr"], subprocess.STDOUT)
        kwargs["stdout"].write(b"mock supervisor diagnostic\n")
        self.write_outputs()
        return subprocess.CompletedProcess(command, 0)

    def write_outputs(self) -> None:
        manifest = smoke.expected_manifest(self.source, self.project, self.output / "fixture-inventory.tsv")
        (self.output / ".bounded-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        records = []
        for index, theorem, module in smoke.FIXTURE_ROWS:
            filename = hashlib.sha256(theorem.encode()).hexdigest() + ".txt"
            (self.output / filename).write_text("⊢ example\texact proof\t\n", encoding="utf-8")
            records.append({
                "index": index, "theorem": theorem, "module": module,
                "status": "success", "filename": filename, "elapsed_seconds": 0.01,
            })
        self.write_ledger(records)
        (self.output / ".bounded-state.json").write_text(json.dumps({
            "status": "finished", "pid": 12345,
            "attempted_this_run": 2, "queued_this_run": 2,
        }), encoding="utf-8")

    def write_ledger(self, records: list[dict]) -> None:
        (self.output / ".bounded-results.jsonl").write_text(
            "".join(json.dumps(row) + "\n" for row in records), encoding="utf-8"
        )

    def ledger(self) -> list[dict]:
        return [json.loads(line) for line in (self.output / ".bounded-results.jsonl").read_text().splitlines()]

    def invoke(self, supervisor=None, environment=None) -> tuple[int, dict]:
        with mock.patch.dict(os.environ, self.environment if environment is None else environment, clear=True), \
                mock.patch.object(smoke.shutil, "which", return_value="/mock/bin/lake"), \
                mock.patch.object(smoke.subprocess, "run", side_effect=supervisor or self.completed_fixture), \
                redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            code = smoke.run(self.source, self.project, self.output)
        return code, json.loads((self.output / "integration-report.json").read_text())

    def test_fixed_fixture_runs_direct_supervisor_and_retains_diagnostics(self) -> None:
        code, report = self.invoke()
        self.assertEqual(code, 0)
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["success_rows"], 2)
        self.assertEqual((self.output / "fixture-inventory.tsv").read_bytes(), (
            b"index\ttheorem\tmodule\n"
            b"0\tNat.le_refl\tMathlib\n"
            b"1\tNat.succ_pos\tMathlib\n"
        ))
        self.assertEqual((self.output / "supervisor.log").read_text(), "mock supervisor diagnostic\n")
        self.assertEqual([trace["theorem"] for trace in report["traces"]], ["Nat.le_refl", "Nat.succ_pos"])
        for trace in report["traces"]:
            self.assertGreater(trace["bytes"], 0)
            self.assertEqual(trace["sha256"], smoke.sha256(self.output / trace["filename"]))
        # A second run must not claim a worker test from reusable successes.
        before = (self.output / "integration-report.json").read_bytes()
        with self.assertRaisesRegex(ValueError, "must be empty"):
            smoke.run(self.source, self.project, self.output)
        self.assertEqual((self.output / "integration-report.json").read_bytes(), before)

    def test_cli_requires_source_project_output(self) -> None:
        with mock.patch("sys.argv", ["smoke_runtime.py", "--source", str(self.source),
                                    "--project", str(self.project), "--output", str(self.output)]), \
                mock.patch.object(smoke, "run", return_value=0) as run:
            self.assertEqual(smoke.main(), 0)
        run.assert_called_once_with(self.source, self.project, self.output)

    def test_nonzero_supervisor_exit_keeps_log_and_failure_report(self) -> None:
        def fail(command, **kwargs):
            kwargs["stdout"].write(b"import failed\n")
            return subprocess.CompletedProcess(command, 4)
        code, report = self.invoke(fail)
        self.assertEqual(code, 1)
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["supervisor_exit_code"], 4)
        self.assertIn("code 4", report["error"])
        self.assertEqual((self.output / "supervisor.log").read_text(), "import failed\n")
        self.assertEqual((self.output / "fixture-inventory.tsv").read_bytes(), smoke.FIXTURE)

    def test_setup_preconditions_fail_before_supervisor(self) -> None:
        for missing in ("LEAN_PATH", "lake", "runtime"):
            with self.subTest(missing=missing):
                output = Path(self.temp.name) / f"missing-{missing}"
                environment = dict(self.environment)
                if missing == "LEAN_PATH":
                    environment.pop("LEAN_PATH")
                elif missing == "runtime":
                    (self.source / ".nazrin-actions-runtime.json").unlink()
                with mock.patch.dict(os.environ, environment, clear=True), \
                        mock.patch.object(smoke.shutil, "which", return_value=None if missing == "lake" else "/mock/lake"), \
                        mock.patch.object(smoke.subprocess, "run") as run, \
                        redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                    self.assertEqual(smoke.run(self.source, self.project, output), 1)
                run.assert_not_called()
                report = json.loads((output / "integration-report.json").read_text())
                self.assertIn("runtime" if missing == "runtime" else missing, report["error"])

    def test_corruption_and_failed_rows_cannot_pass_smoke(self) -> None:
        cases = (
            "partial-ledger", "invalid-json", "non-object", "missing-row", "duplicate-row",
            "wrong-theorem", "wrong-module", "wrong-index", "boolean-index", "float-index", "failure", "timeout",
            "crash", "import_failure", "invalid_symbol", "unsafe-filename", "missing-trace",
            "empty-trace", "whitespace-trace", "symlink-trace", "invalid-trace-encoding",
            "bad-elapsed", "nan-elapsed", "wrong-manifest", "missing-manifest", "symlink-ledger",
            "unfinished-state", "wrong-count", "changed-fixture", "pending-artifact", "changed-worker",
        )
        for case in cases:
            with self.subTest(case=case):
                self.output = Path(self.temp.name) / case

                def corrupt(command, **kwargs):
                    result = self.completed_fixture(command, **kwargs)
                    records = self.ledger()
                    trace = self.output / records[0]["filename"]
                    ledger = self.output / ".bounded-results.jsonl"
                    if case == "partial-ledger":
                        ledger.write_bytes(ledger.read_bytes().rstrip(b"\n"))
                    elif case == "invalid-json":
                        ledger.write_text("{broken}\n" + ledger.read_text(), encoding="utf-8")
                    elif case == "non-object":
                        ledger.write_text("[]\n" + json.dumps(records[1]) + "\n", encoding="utf-8")
                    elif case == "missing-row":
                        self.write_ledger(records[:1])
                    elif case == "duplicate-row":
                        self.write_ledger([records[0], records[0]])
                    elif case in {"wrong-theorem", "wrong-module", "wrong-index", "boolean-index", "float-index"}:
                        field, value = {
                            "wrong-theorem": ("theorem", "Nat.bad"),
                            "wrong-module": ("module", "Other"),
                            "wrong-index": ("index", 99),
                            "boolean-index": ("index", False),
                            "float-index": ("index", 1.0),
                        }[case]
                        records[0][field] = value
                        self.write_ledger(records)
                    elif case in {"failure", "timeout", "crash", "import_failure", "invalid_symbol"}:
                        records[0]["status"] = case
                        self.write_ledger(records)
                    elif case == "unsafe-filename":
                        records[0]["filename"] = "../outside.txt"
                        self.write_ledger(records)
                    elif case == "missing-trace":
                        trace.rename(self.output / "held-trace")
                    elif case == "empty-trace":
                        trace.write_bytes(b"")
                    elif case == "whitespace-trace":
                        trace.write_text(" \n\t\n")
                    elif case == "symlink-trace":
                        saved = self.output / "held-trace"
                        trace.rename(saved)
                        trace.symlink_to(saved)
                    elif case == "invalid-trace-encoding":
                        trace.write_bytes(b"\xff\xfe")
                    elif case in {"bad-elapsed", "nan-elapsed"}:
                        records[0]["elapsed_seconds"] = -1 if case == "bad-elapsed" else float("nan")
                        self.write_ledger(records)
                    elif case == "wrong-manifest":
                        (self.output / ".bounded-manifest.json").write_text('{}')
                    elif case == "missing-manifest":
                        (self.output / ".bounded-manifest.json").rename(self.output / "held-manifest")
                    elif case == "symlink-ledger":
                        saved = self.output / "held-ledger"
                        ledger.rename(saved)
                        ledger.symlink_to(saved)
                    elif case == "unfinished-state":
                        (self.output / ".bounded-state.json").write_text('{"status":"running"}')
                    elif case == "wrong-count":
                        (self.output / ".bounded-state.json").write_text(json.dumps({
                            "status": "finished", "attempted_this_run": 1, "queued_this_run": 2,
                        }))
                    elif case == "changed-fixture":
                        (self.output / "fixture-inventory.tsv").write_text("other inventory\n")
                    elif case == "pending-artifact":
                        (self.output / ".pending-test").write_text("uncommitted")
                    elif case == "changed-worker":
                        (self.source / ".lake/build/bin/AtomizerWorker").write_bytes(b"changed")
                    return result

                code, report = self.invoke(corrupt)
                self.assertEqual(code, 1)
                self.assertEqual(report["status"], "failed")
                self.assertEqual(report["success_rows"], 0)
                self.assertTrue(report["error"])
                self.assertTrue((self.output / "supervisor.log").is_file())


class WorkerProtocolTests(unittest.TestCase):
    def test_resume_uses_exact_inventory_keys_and_typed_indices(self) -> None:
        keys = {(1, "Test.valid", "Mathlib.Test")}
        cases = (
            ({"index": 1, "theorem": "Test.valid", "module": "Mathlib.Test", "status": "success"}, True),
            ({"index": 99, "theorem": "Test.valid", "module": "Mathlib.Test", "status": "success"}, False),
            ({"index": True, "theorem": "Test.valid", "module": "Mathlib.Test", "status": "success"}, False),
            ({"index": 1.0, "theorem": "Test.valid", "module": "Mathlib.Test", "status": "success"}, False),
        )
        with tempfile.TemporaryDirectory() as temp:
            ledger = Path(temp) / ".bounded-results.jsonl"
            for record, accepted in cases:
                with self.subTest(record=record):
                    ledger.write_text(json.dumps(record) + "\n", encoding="utf-8")
                    result = bounded.load_latest(ledger, keys)
                    self.assertEqual((1, "Test.valid", "Mathlib.Test") in result, accepted)

    def test_stale_ledger_rows_are_quarantined_and_unknown_retries(self) -> None:
        key = (1, "Test.valid", "Mathlib.Test")
        valid = {"index": 1, "theorem": key[1], "module": key[2], "status": "success"}
        stale = {**valid, "index": 99}
        unknown = {**valid, "status": "unknown"}
        with tempfile.TemporaryDirectory() as temp:
            ledger = Path(temp) / ".bounded-results.jsonl"
            ledger.write_text("".join(json.dumps(row) + "\n" for row in (valid, stale, unknown)), encoding="utf-8")
            latest = bounded.load_latest(ledger, {key})
            self.assertEqual(latest[key], "unknown")
            self.assertEqual([json.loads(line) for line in ledger.read_text().splitlines()], [valid, unknown])
            rejected = ledger.with_name(".bounded-rejected-results.jsonl")
            self.assertEqual([json.loads(line) for line in rejected.read_text().splitlines()], [stale])

    def worker(self):
        args = argparse.Namespace(max_heartbeats=200_000, memory_gib=10)
        with mock.patch.object(bounded.selectors, "DefaultSelector"):
            return bounded.Worker(Path("/unused/AtomizerWorker"), {}, Path("/unused"), "Mathlib", args)

    def test_ready_module_must_match_import_request(self) -> None:
        for message, accepted in (({"status": "ready", "module": "Mathlib"}, True),
                                  ({"status": "ready", "module": "Other"}, False),
                                  ({"status": "ready"}, False),
                                  ({"status": "success", "module": "Mathlib"}, False)):
            with self.subTest(message=message):
                worker = self.worker()
                with mock.patch.object(bounded.subprocess, "Popen"), \
                        mock.patch.object(bounded.os, "set_blocking"), \
                        mock.patch.object(worker, "read_message", return_value=message):
                    if accepted:
                        worker.start(180)
                    else:
                        with self.assertRaisesRegex(RuntimeError, "startup reply"):
                            worker.start(180)

    def test_outcome_theorem_and_status_must_match_request(self) -> None:
        for message, accepted in (({"status": "success", "theorem": "Nat.le_refl"}, True),
                                  ({"status": "success", "theorem": "Nat.succ_pos"}, False),
                                  ({"status": "ready", "theorem": "Nat.le_refl"}, False)):
            with self.subTest(message=message):
                worker = self.worker()
                worker.proc = mock.Mock()
                with mock.patch.object(worker, "read_message", return_value=message):
                    if accepted:
                        self.assertEqual(worker.run("Nat.le_refl", Path("/unused/trace"), 30), message)
                    else:
                        with self.assertRaises(ValueError):
                            worker.run("Nat.le_refl", Path("/unused/trace"), 30)


if __name__ == "__main__":
    unittest.main()
