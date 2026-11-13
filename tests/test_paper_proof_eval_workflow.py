from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

try:
    import yaml
except ImportError:
    yaml = None

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW_DIR = ROOT / ".github" / "workflows"
WORKFLOW = WORKFLOW_DIR / "paper-proof-eval.yml"
OVERLAY = ROOT / "paper-eval-overlay"
SOURCE_TREE = Path("/home/felian/lab/Nazrin/nazrin-repo")


def load_script(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


planner = load_script("plan_paper_shards")
packager = load_script("package_proof_eval")


class PaperProofEvalWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.text = WORKFLOW.read_text(encoding="utf-8")
        cls.workflow = yaml.safe_load(cls.text) if yaml is not None else None

    def parsed(self) -> dict:
        if self.workflow is None:
            self.skipTest("PyYAML is unavailable")
        self.assertIsInstance(self.workflow, dict)
        return self.workflow

    def step(self, job: str, name: str) -> dict:
        return next(step for step in self.parsed()["jobs"][job]["steps"]
                    if step.get("name") == name)

    def upload(self, name: str) -> dict:
        return next(step for job in self.parsed()["jobs"].values()
                    for step in job["steps"]
                    if step.get("name") == name)

    def test_workflow_is_manual_only_and_has_no_push_or_mirror(self) -> None:
        workflow = self.parsed()
        self.assertEqual(set(workflow["on"]), {"workflow_dispatch"})
        self.assertEqual(workflow["permissions"], {"contents": "read"})
        self.assertNotRegex(self.text, r"(?m)^\s*(push|pull_request|schedule|workflow_run):")
        self.assertNotRegex(self.text, r"\bgit(?:\s+-C\s+\S+)?\s+push\b|--mirror\b")
        self.assertNotRegex(self.text, r"\bgh\s+(workflow\s+run|api)\b")

    def test_dispatch_inputs_and_defaults_match_the_contract(self) -> None:
        inputs = self.parsed()["on"]["workflow_dispatch"]["inputs"]
        self.assertEqual(
            set(inputs),
            {
                "theorems", "shard_count", "max_parallel", "checkpoint_url",
                "checkpoint_sha256", "time_limit", "max_steps", "top_k",
                "source_ref", "mathlib_commit", "runner_label",
            },
        )
        self.assertEqual(inputs["theorems"]["default"],
                         "paper-eval-overlay/paper-slices/slice-01.tsv")
        self.assertEqual(inputs["shard_count"]["default"], 10)
        self.assertEqual(inputs["max_parallel"]["default"], 10)
        self.assertEqual(inputs["time_limit"]["default"], 15)
        self.assertEqual(inputs["max_steps"]["default"], 100)
        self.assertEqual(inputs["top_k"]["default"], 5)
        self.assertEqual(inputs["source_ref"]["default"],
                         "e34a0535fc767479f7939a98f5699b1a6513a919")
        self.assertEqual(inputs["mathlib_commit"]["default"],
                         "5e932f97dd25535344f80f9dd8da3aab83df0fe6")
        self.assertEqual(inputs["runner_label"]["default"], "ubuntu-24.04")
        for name in ("checkpoint_url", "checkpoint_sha256"):
            self.assertIs(inputs[name]["required"], True)
            self.assertNotIn("default", inputs[name])
            self.assertEqual(inputs[name]["type"], "string")
        for name in ("shard_count", "max_parallel", "time_limit", "max_steps", "top_k"):
            self.assertEqual(inputs[name]["type"], "number")

    def test_matrix_is_bounded_and_shards_are_parallel_without_fail_fast(self) -> None:
        shards = self.parsed()["jobs"]["shards"]
        self.assertEqual(shards["needs"], "prepare")
        self.assertEqual(shards["timeout-minutes"], 360)
        self.assertIs(shards["strategy"]["fail-fast"], False)
        self.assertEqual(
            shards["strategy"]["max-parallel"],
            "${{ fromJSON(needs.prepare.outputs.max_parallel) }}",
        )
        self.assertEqual(
            shards["strategy"]["matrix"],
            "${{ fromJSON(needs.prepare.outputs.matrix) }}",
        )
        plan = self.step("prepare", "Plan deterministic contiguous shards")
        self.assertIn("--shards \"$SHARD_COUNT\"", plan["run"])
        self.assertIn("plan_paper_shards.py", plan["run"])
        self.assertIn('"id": shard["id"]', plan["run"])
        self.assertIn('"label": f"{shard[\'id\']:02d}"', plan["run"])
        self.assertIn('"rows": shard["rows"]', plan["run"])

    def test_checkpoint_is_required_verified_and_not_uploaded(self) -> None:
        validate = self.step("prepare", "Validate dispatch inputs and theorem manifest")["run"]
        for token in ("CHECKPOINT_URL", "CHECKPOINT_SHA256", "fullmatch(r\"[0-9a-f]{64}\"",
                      "CHECKPOINT_URL must be an absolute HTTPS URL"):
            self.assertIn(token, validate)
        download = self.step("prepare", "Download and verify checkpoint")["run"]
        for token in ("curl -fL", "sha256sum", "checkpoint digest mismatch",
                      "plan/checkpoint.json", "CHECKPOINT_SHA256"):
            self.assertIn(token, download)
        plan_upload = self.upload("Upload immutable shard plan and checkpoint metadata")
        self.assertEqual(plan_upload["with"]["name"],
                         "paper-proof-eval-plan-${{ github.run_id }}")
        self.assertEqual(plan_upload["with"]["path"], "plan/")
        self.assertNotIn("checkpoint.pt", plan_upload["with"]["path"])
        shard_download = self.step("shards", "Download and verify checkpoint")["run"]
        self.assertIn("curl -fL", shard_download)
        self.assertIn("checkpoint digest mismatch", shard_download)

    def test_shard_environment_and_evaluation_command(self) -> None:
        run = self.step("shards", "Run paper-aligned NPA evaluation")["run"]
        for token in (
            'export PYTHONPATH="$NAZRIN_DIR',
            "$NAZRIN_DIR/.lake/build/lib/lean",
            "$NAZRIN_DIR/.lake/packages/pantograph/.lake/build/lib/lean",
            'MATHLIB_LEAN_PATH=$(cd "$MATHLIB_PROJECT_DIR" && lake env printenv LEAN_PATH)',
            'export LEAN_PATH="$NAZRIN_DIR/.lake/build/lib/lean:'
            '$NAZRIN_DIR/.lake/packages/pantograph/.lake/build/lib/lean:'
            '$MATHLIB_LEAN_PATH"',
            'cd "$MATHLIB_PROJECT_DIR"',
            "python3 -m experiments.npa_search.run_eval",
            "--module Mathlib",
            "--device cpu",
            '--time-limit "$TIME_LIMIT"',
            '--max-steps "$MAX_STEPS"',
            '--top-k "$TOP_K"',
            "LAKE",
        ):
            self.assertIn(token, run)
        # The Mathlib build directory alone does not contain Batteries/Qq/Aesop.
        self.assertNotIn(
            'export LEAN_PATH="$NAZRIN_DIR/.lake/build/lib/lean:'
            '$NAZRIN_DIR/.lake/packages/pantograph/.lake/build/lib/lean:'
            '$MATHLIB_PROJECT_DIR/.lake/packages/mathlib/.lake/build/lib/lean',
            run,
        )
        for job, name in (
            ("prepare", "Install CPU PyTorch"),
            ("shards", "Install CPU PyTorch"),
        ):
            install = self.step(job, name)["run"]
            self.assertIn("torch==2.6.0", install)
            self.assertIn("https://download.pytorch.org/whl/cpu", install)

    def test_artifacts_are_pinned_and_have_distinct_roles(self) -> None:
        uploads = [
            step for job in self.parsed()["jobs"].values()
            for step in job["steps"]
            if step.get("uses", "").startswith("actions/upload-artifact@")
        ]
        self.assertEqual(len(uploads), 3)
        for upload in uploads:
            self.assertRegex(upload["uses"], r"actions/upload-artifact@[0-9a-f]{40}")
            self.assertIs(upload["with"]["include-hidden-files"], True)
            self.assertIs(upload["with"]["overwrite"], True)
            self.assertIn(upload["with"]["if-no-files-found"], {"warn", "error"})
        names = [upload["with"]["name"] for upload in uploads]
        self.assertEqual(len(set(names)), 3)
        self.assertIn("paper-proof-eval-plan-${{ github.run_id }}", names)
        self.assertIn("paper-proof-eval-shard-${{ matrix.label }}-${{ github.run_id }}", names)
        self.assertIn("paper-proof-eval-results-${{ github.run_id }}-${{ github.run_attempt }}", names)
        package_upload = self.upload("Upload evaluation package")
        self.assertEqual(package_upload["with"]["if-no-files-found"], "error")
        package = self.parsed()["jobs"]["package"]
        self.assertEqual(package["if"], "always()")
        self.assertEqual(set(package["needs"]), {"prepare", "shards"})
        package_steps = package["steps"]
        upload_index = package_steps.index(package_upload)
        fail_index = next(index for index, step in enumerate(package_steps)
                          if step.get("name") == "Fail workflow if evaluation is incomplete")
        self.assertLess(upload_index, fail_index)
        self.assertIn("evaluation-report.json", package_steps[fail_index]["run"])

    def test_overlay_checksums_and_manifest_row_count(self) -> None:
        result = subprocess.run(
            ["sha256sum", "-c", "SHA256SUMS"], cwd=OVERLAY,
            capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = (OVERLAY / "paper-slices/slice-01.tsv").read_text(encoding="utf-8").splitlines()
        self.assertEqual(len(lines), 20604)
        self.assertEqual(lines[0], "index\ttheorem\tmodule\tslice\ttopo_rank")
        self.assertEqual(len(lines) - 1, 20603)
        self.assertFalse(any("__pycache__" in path.parts for path in OVERLAY.rglob("*")))
        self.assertFalse((OVERLAY / ".lake").exists())
        lakefile = (OVERLAY / "lakefile.append").read_text(encoding="utf-8")
        self.assertIn("lean_lib GoalGraphCore", lakefile)
        self.assertIn("lean_exe NPARepl", lakefile)

    @unittest.skipUnless(SOURCE_TREE.is_dir(), "local source tree is unavailable")
    def test_overlay_files_match_the_local_source_bytes(self) -> None:
        for path in sorted(OVERLAY.rglob("*")):
            if not path.is_file() or path.name in {"SHA256SUMS", "README.md", "lakefile.append"}:
                continue
            relative = path.relative_to(OVERLAY)
            source = SOURCE_TREE / relative
            if relative.parts[:1] == ("paper-slices",):
                source = SOURCE_TREE / "experiments" / relative
            self.assertTrue(source.is_file(), f"missing source for {relative}")
            self.assertEqual(path.read_bytes(), source.read_bytes(), f"drifted {relative}")

    def test_aggregation_merges_valid_shards_and_counts_every_status(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_dir, plan, checkpoint = self.make_plan(root)
            self.write_artifact(root, plan_dir, plan, 0, ["success", "failure", "timeout"], checkpoint)
            self.write_artifact(root, plan_dir, plan, 1, ["error", "success", "success"], checkpoint)
            report = packager.package(
                plan_dir / "plan.json", root / "downloads", root / "package",
                run_id="123", shard_count=2, checkpoint_sha256=checkpoint,
                expected_plan_sha=hashlib.sha256((plan_dir / "plan.json").read_bytes()).hexdigest(),
            )
            self.assertTrue(report["complete"], report["issues"])
            self.assertEqual(report["totals"]["total"], 6)
            self.assertEqual(report["totals"]["success"], 3)
            self.assertEqual(report["totals"]["failure"], 1)
            self.assertEqual(report["totals"]["timeout"], 1)
            self.assertEqual(report["totals"]["error"], 1)
            summary = json.loads((root / "package/evaluation-summary.json").read_text())
            self.assertTrue(summary["complete"])
            self.assertEqual(summary["success_rate"], 0.5)
            records = [json.loads(line) for line in
                       (root / "package/results.jsonl").read_text().splitlines()]
            self.assertEqual([record["theorem"] for record in records],
                             [f"Test.thm{index}" for index in range(6)])
            self.assertTrue((root / "package/evaluation-report.json").is_file())

    def test_aggregation_rejects_a_tampered_summary_and_keeps_partial_diagnostics(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_dir, plan, checkpoint = self.make_plan(root)
            self.write_artifact(root, plan_dir, plan, 0, ["success", "failure", "timeout"], checkpoint)
            artifact = self.write_artifact(
                root, plan_dir, plan, 1, ["error", "success", "success"], checkpoint
            )
            summary = json.loads((artifact / "summary.json").read_text())
            summary["success"] += 1
            (artifact / "summary.json").write_text(json.dumps(summary))
            report = packager.package(
                plan_dir / "plan.json", root / "downloads", root / "package",
                run_id="123", shard_count=2, checkpoint_sha256=checkpoint,
            )
            self.assertFalse(report["complete"])
            self.assertEqual(report["invalid_shards"], [1])
            self.assertEqual(report["totals"]["total"], 3)
            self.assertEqual(len((root / "package/results.jsonl").read_text().splitlines()), 3)
            self.assertTrue(report["issues"])

    def test_aggregation_reports_missing_shards_and_missing_plan(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_dir, plan, checkpoint = self.make_plan(root)
            self.write_artifact(root, plan_dir, plan, 0, ["success", "failure", "timeout"], checkpoint)
            report = packager.package(
                plan_dir / "plan.json", root / "downloads", root / "package",
                run_id="123", shard_count=2, checkpoint_sha256=checkpoint,
            )
            self.assertFalse(report["complete"])
            self.assertEqual(report["missing_shards"], [1])
            self.assertEqual(report["totals"]["total"], 3)
            missing = packager.package(
                root / "absent-plan.json", root / "downloads", root / "missing-package",
                run_id="123", shard_count=2, checkpoint_sha256=checkpoint,
            )
            self.assertFalse(missing["complete"])
            self.assertEqual(missing["missing_shards"], [0, 1])
            self.assertTrue((root / "missing-package/evaluation-report.json").is_file())
            self.assertTrue((root / "missing-package/evaluation-summary.json").is_file())

    def test_validation_script_rejects_bad_dispatch_values(self) -> None:
        script = self.step("prepare", "Validate dispatch inputs and theorem manifest")["run"]
        base = {
            **os.environ,
            "SOURCE_REF": "e34a0535fc767479f7939a98f5699b1a6513a919",
            "MATHLIB_COMMIT": "5e932f97dd25535344f80f9dd8da3aab83df0fe6",
            "SHARD_COUNT": "10",
            "MAX_PARALLEL": "10",
            "CHECKPOINT_URL": "https://example.com/checkpoint.pt",
            "CHECKPOINT_SHA256": "a" * 64,
            "TIME_LIMIT": "15",
            "MAX_STEPS": "100",
            "TOP_K": "5",
            "RUNNER_LABEL": "ubuntu-24.04",
            "THEOREMS": "paper-eval-overlay/paper-slices/slice-01.tsv",
            "GITHUB_WORKSPACE": str(ROOT),
        }
        cases = [
            ({}, True),
            ({"SHARD_COUNT": "0"}, False),
            ({"SHARD_COUNT": "21"}, False),
            ({"MAX_PARALLEL": "21"}, False),
            ({"CHECKPOINT_URL": "http://example.com/checkpoint.pt"}, False),
            ({"CHECKPOINT_SHA256": ""}, False),
            ({"TIME_LIMIT": "0"}, False),
        ]
        for extra, valid in cases:
            with self.subTest(extra=extra), tempfile.NamedTemporaryFile(delete=False) as output:
                result = subprocess.run(
                    ["bash", "-c", script],
                    env={**base, "GITHUB_OUTPUT": output.name, **extra},
                    capture_output=True, text=True,
                )
            self.assertEqual(result.returncode == 0, valid, result.stderr)

    def test_readme_has_dispatch_example_and_limitations(self) -> None:
        readme = (OVERLAY / "README.md").read_text(encoding="utf-8")
        self.assertIn("gh workflow run paper-proof-eval.yml", readme)
        for phrase in (
            "20,603", "CPU only", "No shared build cache",
            "Checkpoint URL must be reachable", "15-second budget scope",
            "Lean process startup", "not uploaded as an Actions artifact",
            "cd \"$MATHLIB_PROJECT_DIR\"",
            "MATHLIB_LEAN_PATH=$(cd \"$MATHLIB_PROJECT_DIR\" && lake env printenv LEAN_PATH)",
            "unknown module prefix 'Batteries'",
        ):
            self.assertIn(phrase, readme)

    def make_plan(self, root: Path) -> tuple[Path, dict, str]:
        source = root / "slice.tsv"
        lines = ["index\ttheorem\tmodule\tslice\ttopo_rank"]
        lines.extend(
            f"{index}\tTest.thm{index}\tMathlib.Test\t1\t{index}"
            for index in range(6)
        )
        source.write_text("\n".join(lines) + "\n", encoding="utf-8")
        plan_dir = root / "plan"
        plan = planner.plan(source, plan_dir, 2)
        checkpoint = "a" * 64
        return plan_dir, plan, checkpoint

    def write_artifact(
        self,
        root: Path,
        plan_dir: Path,
        plan: dict,
        shard_id: int,
        statuses: list[str],
        checkpoint: str,
    ) -> Path:
        entry = plan["shards"][shard_id]
        artifact = root / "downloads" / f"paper-proof-eval-shard-{shard_id:02d}-123"
        artifact.mkdir(parents=True, exist_ok=True)
        shard_path = plan_dir / entry["file"]
        (artifact / "shard.tsv").write_bytes(shard_path.read_bytes())
        lines = shard_path.read_text(encoding="utf-8").splitlines()
        names = [line.split("\t")[1] for line in lines[1:]]
        self.assertEqual(len(names), len(statuses))
        results = [
            {
                "theorem": name,
                "status": status,
                "elapsed_ms": 10.0 + index,
                "steps": index,
            }
            for index, (name, status) in enumerate(zip(names, statuses))
        ]
        (artifact / "results.jsonl").write_text(
            "".join(json.dumps(record) + "\n" for record in results), encoding="utf-8"
        )
        summary = {
            "total": len(results),
            "success": statuses.count("success"),
            "failure": statuses.count("failure"),
            "timeout": statuses.count("timeout"),
            "error": statuses.count("error"),
            "module": "Mathlib",
            "policy": "npa",
            "mock": False,
            "checkpoint_sha256": checkpoint,
            "time_limit_seconds": 15.0,
            "max_steps": 100,
            "top_k": 5,
            "device": "cpu",
        }
        (artifact / "summary.json").write_text(json.dumps(summary), encoding="utf-8")
        (artifact / "checkpoint.json").write_text(
            json.dumps({"sha256": checkpoint, "size_bytes": 16}), encoding="utf-8"
        )
        return artifact


if __name__ == "__main__":
    unittest.main()
