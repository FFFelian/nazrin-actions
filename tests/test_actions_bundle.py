from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

try:
    import yaml
except ImportError:
    yaml = None

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW_DIR = ROOT / ".github" / "workflows"
WORKFLOW = WORKFLOW_DIR / "mathlib-atomization.yml"


class ActionsBundleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.text = WORKFLOW.read_text(encoding="utf-8")
        cls.setup = (ROOT / "scripts" / "setup_runtime.sh").read_text(encoding="utf-8")
        cls.readme = (ROOT / "README.md").read_text(encoding="utf-8")
        cls.workflow = yaml.safe_load(cls.text) if yaml is not None else None

    def parsed(self) -> dict:
        if self.workflow is None:
            self.skipTest("PyYAML is unavailable; text checks still run")
        self.assertIsInstance(self.workflow, dict)
        return self.workflow

    def step(self, job: str, name: str) -> dict:
        return next(step for step in self.parsed()["jobs"][job]["steps"]
                    if step.get("name") == name)

    def test_only_one_manual_workflow_and_no_push_or_mirror(self) -> None:
        workflows = sorted([*WORKFLOW_DIR.glob("*.yml"), *WORKFLOW_DIR.glob("*.yaml")])
        self.assertEqual(workflows, [WORKFLOW])
        self.assertIn("workflow_dispatch:", self.text)
        self.assertNotRegex(self.text, r"(?m)^\s*(push|pull_request|schedule|workflow_run):")
        self.assertNotRegex(self.text + self.setup, r"\bgit(?:\s+-C\s+\S+)?\s+push\b|--mirror\b")
        self.assertNotRegex(self.text, r"\bgh\s+(workflow\s+run|api)\b")
        self.assertNotIn("package_results.py", self.text)

    def test_dispatch_contract_pins_source_and_mathlib(self) -> None:
        workflow = self.parsed()
        self.assertEqual(set(workflow["on"]), {"workflow_dispatch"})
        inputs = workflow["on"]["workflow_dispatch"]["inputs"]
        self.assertEqual(set(inputs), {"source_repository", "source_ref", "mathlib_commit",
                                       "shard_count", "max_parallel", "scan_minutes", "runner_label"})
        self.assertEqual(inputs["source_repository"]["default"], "https://codeberg.org/aniva/Nazrin.git")
        self.assertEqual(inputs["source_ref"]["required"], True)
        self.assertEqual(inputs["source_ref"]["type"], "string")
        self.assertEqual(inputs["mathlib_commit"]["default"], "5e932f97dd25535344f80f9dd8da3aab83df0fe6")
        self.assertEqual(inputs["shard_count"]["default"], 10)
        self.assertEqual(inputs["max_parallel"]["default"], 10)
        self.assertEqual(inputs["scan_minutes"]["default"], 300)
        self.assertEqual(inputs["runner_label"]["default"], "ubuntu-24.04")
        self.assertEqual(workflow["env"]["NAZRIN_SOURCE_URL"], "${{ inputs.source_repository }}")
        self.assertEqual(workflow["env"]["NAZRIN_SOURCE_REF"], "${{ inputs.source_ref }}")
        self.assertEqual(workflow["env"]["MATHLIB_COMMIT"], "${{ inputs.mathlib_commit }}")
        self.assertEqual(workflow["permissions"], {"contents": "read"})

    def test_validate_step_rejects_mutable_refs_and_bad_repository(self) -> None:
        script = self.step("prepare", "Validate dispatch inputs")["run"]
        cases = [
            ("https://codeberg.org/aniva/Nazrin.git", "main", "b" * 40, "10", "10", "300", False),
            ("https://github.com/aniva/Nazrin.git", "a" * 40, "b" * 40, "10", "10", "300", False),
            ("https://codeberg.org/other/Nazrin.git", "a" * 40, "b" * 40, "10", "10", "300", False),
            ("https://codeberg.org/aniva/Nazrin.git", "a" * 40, "v4.29.1", "10", "10", "300", False),
            ("https://codeberg.org/aniva/Nazrin.git", "A" * 40, "b" * 40, "10", "10", "300", True),
        ]
        for url, source, mathlib, shards, parallel, minutes, valid in cases:
            with self.subTest(url=url, source=source, mathlib=mathlib):
                environment = {
                    **os.environ,
                    "NAZRIN_SOURCE_URL": url,
                    "NAZRIN_SOURCE_REF": source,
                    "MATHLIB_COMMIT": mathlib,
                    "SHARD_COUNT": shards,
                    "MAX_PARALLEL": parallel,
                    "SCAN_MINUTES": minutes,
                    "GITHUB_OUTPUT": os.devnull,
                }
                result = subprocess.run(["bash", "-c", script], env=environment,
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, valid, result.stderr)

    def test_setup_verifies_the_pinned_project_and_can_skip_duplicate_inventory(self) -> None:
        for required in (
            "NAZRIN_SOURCE_URL", "verify_source.py", "--expected-commit",
            "--expected-mathlib-commit", '"$MATHLIB_COMMIT"', "GENERATE_INVENTORY",
            'lake env lean --run "$NAZRIN_DIR/Standalone/Inventory.lean" "$FULL_INVENTORY" Mathlib',
            'export LEAN_PATH="$NAZRIN_LEAN_PATH:$MATHLIB_LEAN_PATH"',
        ):
            self.assertIn(required, self.setup)
        self.assertIn("--assemble", self.setup)
        self.assertIn("smoke_runtime.py", self.setup)
        self.assertLess(self.setup.index("verify_source.py"), self.setup.index("elan-init.sh"))
        self.assertLess(self.setup.index("smoke_runtime.py"), self.setup.index('lake env lean --run'))
        self.assertIn("https://codeberg.org/aniva/Nazrin.git", self.setup)
        self.assertNotIn("git push", self.setup)
        self.assertNotIn("--mirror", self.setup)
        prepare = self.step("prepare", "Bootstrap pinned source, worker and full Mathlib inventory")
        worker = self.step("shards", "Bootstrap pinned source and Mathlib runtime")
        self.assertEqual(prepare["run"], "bash scripts/setup_runtime.sh")
        self.assertEqual(worker["run"], "bash scripts/setup_runtime.sh")
        self.assertEqual(worker["env"]["GENERATE_INVENTORY"], "false")
        self.assertIn("PLAN_SHA256", self.step("shards", "Verify plan and assigned shard inventory digests")["env"])

    def test_plan_exports_complete_inventory_and_ten_default_shards(self) -> None:
        script = self.step("prepare", "Plan exact nonoverlapping shards")["run"]
        self.assertIn('--inventory "$FULL_INVENTORY"', script)
        self.assertIn('--shards "$SHARD_COUNT"', script)
        self.assertIn('--source-commit "$NAZRIN_SOURCE_REF"', script)
        self.assertIn("plan[\"shards\"]", script)
        self.assertIn("hashlib.sha256(path.read_bytes()).hexdigest()", script)
        self.assertNotRegex(script, r"\b(head|sample|limit)\b|--(take|limit|sample)")

    def test_shards_have_fixed_theorem_deadline_and_dynamic_upload_reserve(self) -> None:
        job = self.parsed()["jobs"]["shards"]
        self.assertEqual(job["needs"], "prepare")
        self.assertIs(job["strategy"]["fail-fast"], False)
        self.assertEqual(job["timeout-minutes"], 350)
        self.assertEqual(job["strategy"]["max-parallel"], "${{ fromJSON(needs.prepare.outputs.max_parallel) }}")
        step = self.step("shards", "Run one theorem worker with two Lean internal workers")
        for argument in (
            "scripts/run_shard.py", '--shard-id "$SHARD_ID"', '--shard-count "$SHARD_COUNT"',
            "--timeout-seconds 30", "--internal-workers 2", '--max-runtime-seconds "$runtime_seconds"',
            '--project "$MATHLIB_PROJECT_DIR"',
        ):
            self.assertIn(argument, step["run"])
        self.assertIn("350 * 60", step["run"])
        self.assertIn("15 * 60", step["run"])
        self.assertIn('min(int(os.environ["SCAN_MINUTES"]) * 60, remaining)', step["run"])

    def test_artifacts_are_unique_hidden_and_pinned(self) -> None:
        uploads = [step for job in self.parsed()["jobs"].values() for step in job["steps"]
                   if step.get("uses", "").startswith("actions/upload-artifact@")]
        self.assertEqual(len(uploads), 3)
        names = []
        for upload in uploads:
            self.assertRegex(upload["uses"], r"actions/upload-artifact@[0-9a-f]{40}")
            options = upload["with"]
            self.assertIs(options["include-hidden-files"], True)
            self.assertIn(options["if-no-files-found"], {"warn", "error"})
            for value in ("github.run_id", "inputs.source_ref", "inputs.mathlib_commit"):
                self.assertIn("${{ " + value + " }}", options["name"])
            if upload is self.step("package", "Upload package before enforcing completeness"):
                self.assertIn("github.run_attempt", options["name"])
            else:
                self.assertNotIn("github.run_attempt", options["name"])
            self.assertIs(options["overwrite"], True)
            names.append(options["name"])
        self.assertEqual(len(set(names)), 3)
        package_upload = self.step("package", "Upload package before enforcing completeness")
        self.assertIn("github.run_attempt", package_upload["with"]["name"])
        self.assertNotIn("github.run_attempt", self.step("prepare", "Upload immutable plan and canonical inventory")["with"]["name"])
        restore_plan = self.step("prepare", "Download prior plan when rerunning this workflow")
        self.assertTrue(restore_plan["continue-on-error"])
        restore_shard = self.step("shards", "Restore this shard output when rerunning failed jobs")
        self.assertTrue(restore_shard["continue-on-error"])
        self.assertIn("github.run_id", restore_shard["with"]["name"])
        shard = self.step("shards", "Upload shard results including hidden supervisor state")
        self.assertIn("always()", shard["if"])
        self.assertIn("steps.restore_shard.outcome == 'success'", shard["if"])
        self.assertIn("github.run_attempt > 1", self.step("shards", "Require restored shard on later attempts")["if"])
        self.assertIn("github.run_attempt > 1", self.step("prepare", "Require restored plan on later attempts")["if"])
        self.assertIn("${{ matrix.id }}", shard["with"]["name"])
        self.assertFalse(shard["with"]["path"].startswith("${{ runner.temp }}"))

    def test_package_runs_after_failures_and_preserves_header_only_fallback(self) -> None:
        package = self.parsed()["jobs"]["package"]
        self.assertEqual(package["if"], "always()")
        self.assertEqual(set(package["needs"]), {"prepare", "shards"})
        self.assertTrue(self.step("package", "Download plan when available")["continue-on-error"])
        self.assertTrue(self.step("package", "Download available shard artifacts")["continue-on-error"])
        script = self.step("package", "Validate coverage and package available results")["run"]
        self.assertIn("package_run import package", script)
        self.assertIn("plan digest mismatch", script)
        self.assertIn("pending-inventory.tsv", script)
        self.assertIn("canonical plan unavailable", script)
        self.assertIn("list(range", script)
        self.assertIn("tarfile.open", script)
        upload = self.step("package", "Upload package before enforcing completeness")
        fail = self.step("package", "Fail workflow if coverage is incomplete")
        self.assertEqual(upload["if"], "always()")
        self.assertLess(package["steps"].index(upload), package["steps"].index(fail))
        self.assertIn('report.get("complete") is not True', fail["run"])
        self.assertIn("RUNNER_TEMP", fail["env"])

    def test_no_plan_fallback_writes_diagnostic_archive_and_header(self) -> None:
        package_step = self.step("package", "Validate coverage and package available results")
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "plan").mkdir()
            (root / "downloaded-shards").mkdir()
            environment = {
                **os.environ,
                "RUNNER_TEMP": str(root),
                "EXPECTED_PLAN_SHA256": "wrong",
                "PREPARE_RESULT": "failure",
                "SHARDS_RESULT": "skipped",
                "SHARD_COUNT": "10",
                "GITHUB_STEP_SUMMARY": str(root / "summary.md"),
                "PYTHONDONTWRITEBYTECODE": "1",
            }
            result = subprocess.run(["bash", "-c", package_step["run"]], cwd=ROOT,
                                    env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            output = root / "final-package"
            report = json.loads((output / "package-content/package-report.json").read_text())
            self.assertFalse(report["complete"])
            self.assertIn("canonical plan unavailable", report["issues"][0])
            self.assertEqual(report["missing_shards"], list(range(10)))
            self.assertIsNone(report["inventory_rows"])
            self.assertIsNone(report["pending_rows"])
            self.assertEqual((output / "package-content/pending-inventory.tsv").read_text(),
                             "index\ttheorem\tmodule\n")
            self.assertTrue((output / "nazrin-atomization-results.tar.gz").is_file())
            enforce = self.step("package", "Fail workflow if coverage is incomplete")["run"]
            result = subprocess.run(["bash", "-c", enforce], cwd=ROOT, env=environment,
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Atomization incomplete", result.stderr)
            self.assertIn("header-only pending TSV", self.readme)

    def test_fallback_preserves_plan_and_artifacts_for_invalid_dispatch_count(self) -> None:
        package_step = self.step("package", "Validate coverage and package available results")
        for count in ("invalid", "999999999999999999999999", "-1"):
            with self.subTest(count=count), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                plan = root / "plan"
                plan.mkdir()
                (plan / "plan.json").write_text('{"schema": 1}')
                (plan / "canonical-inventory.tsv").write_text("index\ttheorem\tmodule\n")
                artifacts = root / "downloaded-shards/partial"
                artifacts.mkdir(parents=True)
                (artifacts / "supervisor.log").write_text("partial work\n")
                (artifacts / "bad-link").symlink_to(plan / "plan.json")
                environment = {
                    **os.environ, "RUNNER_TEMP": str(root), "EXPECTED_PLAN_SHA256": "",
                    "PREPARE_RESULT": "failure", "SHARDS_RESULT": "skipped",
                    "SHARD_COUNT": count, "GITHUB_STEP_SUMMARY": str(root / "summary.md"),
                    "PYTHONDONTWRITEBYTECODE": "1",
                }
                result = subprocess.run(["bash", "-c", package_step["run"]], cwd=ROOT,
                                        env=environment, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                content = root / "final-package/package-content"
                report = json.loads((content / "package-report.json").read_text())
                self.assertFalse(report["complete"])
                self.assertIsNone(report["missing_shards"])
                self.assertIn("plan digest mismatch", report["issues"][0])
                self.assertEqual((content / "unvalidated-plan/plan.json").read_bytes(),
                                 (plan / "plan.json").read_bytes())
                self.assertTrue((content / "unvalidated-artifacts/partial/supervisor.log").is_file())
                self.assertFalse(any(path.is_symlink() for path in content.rglob("*")))
                self.assertIn("Atomization package complete", (root / "summary.md").read_text())

    def test_readme_states_scope_and_runtime_limits(self) -> None:
        for required in (
            "324004", "scan_minutes", "30 seconds", "350-minute", "RLIMIT_AS", "10 GiB",
            "runtime/manifest.json", "LEAN_PATH", "pending-inventory.tsv",
            "upstream algorithm", "A new Actions dispatch creates a fresh plan", "header-only",
        ):
            self.assertIn(required, self.readme)
        self.assertNotRegex(self.readme, r"(?m)^NAZRIN_SOURCE_REF=[0-9a-fA-F]{40}$")


if __name__ == "__main__":
    unittest.main()
