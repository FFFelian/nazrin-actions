from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "run_shard.py"
SPEC = importlib.util.spec_from_file_location("run_shard", SCRIPT)
assert SPEC and SPEC.loader
run_shard = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(run_shard)


class TerminalCoverageTests(unittest.TestCase):
    def test_runtime_provenance_is_required_for_nonempty_resume_state(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source, output = root / "source", root / "output"
            source.mkdir()
            output.mkdir()
            runtime = {
                "source_commit": "a" * 40,
                "mathlib_commit": "b" * 40,
                "runtime_manifest_sha256": "c" * 64,
            }
            runtime_path = source / ".nazrin-actions-runtime.json"
            runtime_path.write_text(json.dumps(runtime), encoding="utf-8")
            self.assertEqual(run_shard.bind_runtime_provenance(source, output, "a" * 40)[0], runtime)
            self.assertTrue((output / "runtime-provenance.json").is_file())

            (output / "runtime-provenance.json").unlink()
            (output / "shard-input.tsv").write_text("stale state\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "no runtime provenance"):
                run_shard.bind_runtime_provenance(source, output, "a" * 40)

            (output / "runtime-provenance.json").write_text("{}", encoding="utf-8")
            runtime["runtime_manifest_sha256"] = "d" * 64
            runtime_path.write_text(json.dumps(runtime), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "different assembled runtime"):
                run_shard.bind_runtime_provenance(source, output, "a" * 40)

    @unittest.skipUnless(sys.platform.startswith("linux") and Path("/proc/self/stat").exists(),
                         "requires Linux /proc process identities")
    def test_reaps_workers_after_supervisor_and_session_leader_exit(self) -> None:
        # Isolate the subreaper setting and guarantee fixture cleanup on assertion failure.
        with tempfile.TemporaryDirectory() as temp:
            for ignore_term, exit_leader in ((False, False), (True, False), (True, True)):
                with self.subTest(ignore_term=ignore_term, exit_leader=exit_leader):
                    marker = Path(temp) / f"term-{ignore_term}-{exit_leader}"
                    ready = marker.with_suffix(".ready")
                    child = "\n".join([
                        "import os,signal,time",
                        "def stop(*_):",
                        f"    open({str(marker)!r}, 'w').write('term')",
                        "    return" if ignore_term else "    raise SystemExit(0)",
                        "signal.signal(signal.SIGTERM, stop)",
                        f"open({str(ready)!r}, 'w').write(str(os.getsid(0)))",
                        "while True: time.sleep(.02)",
                    ])
                    if exit_leader:
                        leader = "\n".join([
                            "import subprocess,sys",
                            f"subprocess.Popen([sys.executable, '-c', {child!r}])",
                        ])
                        spawn = f"subprocess.Popen([sys.executable, '-c', {leader!r}], start_new_session=True).wait()"
                    else:
                        spawn = f"subprocess.Popen([sys.executable, '-c', {child!r}], start_new_session=True)"
                    supervisor = "\n".join(["import subprocess,sys,time", spawn, "time.sleep(60)"])
                    harness = "\n".join([
                        "import subprocess,sys,time",
                        "from pathlib import Path",
                        f"sys.path.insert(0, {str(SCRIPT.parent)!r})",
                        "import run_shard as runner",
                        "assert runner._enable_child_subreaper()",
                        f"proc=subprocess.Popen([sys.executable, '-c', {supervisor!r}], start_new_session=True)",
                        "sessions={}",
                        "try:",
                        "    deadline=time.monotonic()+5",
                        f"    while not Path({str(ready)!r}).exists() and time.monotonic()<deadline: time.sleep(.02)",
                        f"    assert Path({str(ready)!r}).exists(), 'worker did not start'",
                        "    proc.kill()",
                        "    proc.wait(timeout=5)",
                        "    sessions=runner._adopted_worker_sessions()",
                        "    assert sessions, 'orphan worker not adopted'",
                        "    runner._reap_worker_sessions(sessions, .15)",
                        f"    assert Path({str(marker)!r}).exists(), 'worker did not receive TERM'",
                        "    assert not runner._live_worker_members(sessions), 'worker survived cleanup'",
                        "finally:",
                        "    if proc.poll() is None: proc.kill(); proc.wait(timeout=5)",
                        "    runner._reap_worker_sessions(sessions, 0)",
                    ])
                    result = subprocess.run([sys.executable, "-B", "-c", harness],
                                            capture_output=True, text=True, timeout=15)
                    self.assertEqual(result.returncode, 0, result.stderr)

    def test_only_valid_committed_outcomes_leave_pending_set(self) -> None:
        rows = [
            {"index": i, "theorem": f"Test.thm{i}", "module": "Mathlib.Test"}
            for i in range(5)
        ]
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            (output / "success.txt").write_text("goal\ttactic\t\n", encoding="utf-8")
            (output / "timeout.log").write_text("timeout\n", encoding="utf-8")
            (output / "crash.log").write_text("worker exited\n", encoding="utf-8")
            records = [
                {"index": 0, "theorem": "Test.thm0", "module": "Mathlib.Test", "status": "success", "filename": "success.txt"},
                {"index": 1, "theorem": "Test.thm1", "module": "Mathlib.Test", "status": "timeout", "filename": "timeout.log"},
                {"index": 2, "theorem": "Test.thm2", "module": "Mathlib.Test", "status": "crash", "filename": "missing.log"},
                {"index": 3, "theorem": "Test.thm3", "module": "Mathlib.Test", "status": "import_failure", "filename": "import.log"},
                {"index": 99, "theorem": "Unknown.thm", "module": "Mathlib.Test", "status": "failure", "filename": "crash.log"},
                {"index": 4, "theorem": "Test.thm4", "module": "Mathlib.Test", "status": "unknown", "filename": "crash.log"},
            ]
            (output / ".bounded-results.jsonl").write_text(
                "".join(json.dumps(record) + "\n" for record in records), encoding="utf-8"
            )

            pending, stats = run_shard.terminal_coverage(rows, output)

            self.assertEqual([row["index"] for row in pending], [2, 3, 4])
            self.assertEqual(stats["terminal_rows"], 2)
            self.assertEqual(stats["pending_rows"], 3)
            self.assertEqual(stats["terminal_status_counts"], {"success": 1, "timeout": 1})
            self.assertEqual(stats["missing_terminal_artifacts"], 1)
            self.assertEqual(stats["unknown_ledger_rows"], 1)

    def test_malformed_or_partial_ledger_rows_do_not_complete_inventory(self) -> None:
        rows = [{"index": 7, "theorem": "Test.pending", "module": "Mathlib.Test"}]
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            (output / ".bounded-results.jsonl").write_text('{"status":"success"\nnot json\n', encoding="utf-8")
            pending, stats = run_shard.terminal_coverage(rows, output)
            self.assertEqual(pending, rows)
            self.assertEqual(stats["terminal_rows"], 0)
            self.assertEqual(stats["invalid_ledger_rows"], 2)

    def test_boolean_and_float_indices_never_alias_integer_inventory_keys(self) -> None:
        row = {"index": 1, "theorem": "Test.pending", "module": "Mathlib.Test"}
        for invalid_index in (True, 1.0):
            with self.subTest(index=invalid_index), tempfile.TemporaryDirectory() as temp:
                output = Path(temp)
                (output / "trace.txt").write_text("trace\n", encoding="utf-8")
                record = {**row, "index": invalid_index, "status": "success", "filename": "trace.txt"}
                (output / ".bounded-results.jsonl").write_text(json.dumps(record) + "\n", encoding="utf-8")
                pending, stats = run_shard.terminal_coverage([row], output)
                self.assertEqual(pending, [row])
                self.assertEqual(stats["terminal_rows"], 0)
                self.assertEqual(stats["invalid_ledger_rows"], 1)


if __name__ == "__main__":
    unittest.main()
