from __future__ import annotations

import gzip
import hashlib
import importlib.util
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
WORKFLOW = WORKFLOW_DIR / "schema4-trace-export.yml"
OVERLAY = ROOT / "paper-overlay"
FIXTURE = ROOT / "tests" / "fixtures" / "fake_schema4_exporter.py"
RUNNER = ROOT / "scripts" / "run_schema4_shard.py"
MERGER = ROOT / "scripts" / "merge_schema4_artifacts.py"
SOURCE_TREE = Path("/home/felian/lab/Nazrin/nazrin-repo")
SLICE = OVERLAY / "paper-slices" / "slice-00.tsv"

NEW_OVERLAY_FILES = (
    "Standalone/ExprGraphV2.lean",
    "Standalone/ExprGraphV3.lean",
    "Standalone/StructuredTraceV4.lean",
    "experiments/exprgraph/v3/validate_exprgraph_v3.py",
    "experiments/npa_data/validate_structured_v4.py",
)

EXPECTED_INPUTS = {
    "slice", "shard_count", "max_parallel", "start", "end", "limit",
    "heartbeats", "timeout_seconds", "source_ref", "runner_label",
}


def load_script(name: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


runner_module = load_script("run_schema4_shard")
merge_module = load_script("merge_schema4_artifacts")
planner = load_script("plan_paper_shards")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fixture_command() -> str:
    return f"{sys.executable} {FIXTURE}"


def write_slice(path: Path, rows: list[tuple[str, str]]) -> Path:
    header = "index\ttheorem\tmodule\tslice\ttopo_rank\n"
    payload = header + "".join(
        f"{index}\t{theorem}\t{module}\tsmoke\t{index}\n"
        for index, (theorem, module) in enumerate(rows))
    path.write_text(payload, encoding="utf-8")
    return path


def slice_head(path: Path, count: int) -> Path:
    lines = SLICE.read_text(encoding="utf-8").splitlines()
    path.write_text("\n".join([lines[0], *lines[1:count + 1]]) + "\n", encoding="utf-8")
    return path


def run_cli(arguments: list[str], *, cwd: Path = ROOT, env: dict[str, str] | None = None,
            timeout: float = 120.0) -> subprocess.CompletedProcess:
    environment = dict(os.environ)
    environment.setdefault("PYTHONDONTWRITEBYTECODE", "1")
    if env:
        environment.update(env)
    return subprocess.run(
        [sys.executable, "-B", *arguments],
        cwd=str(cwd), env=environment, capture_output=True, text=True,
        timeout=timeout,
    )


class OverlayTests(unittest.TestCase):
    def test_sha256sums_cover_every_schema4_source(self) -> None:
        result = subprocess.run(["sha256sum", "-c", "SHA256SUMS"], cwd=OVERLAY,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        entries = dict(
            (line.split(maxsplit=1)[1].strip(), line.split(maxsplit=1)[0])
            for line in (OVERLAY / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
            if line.strip()
        )
        for name in NEW_OVERLAY_FILES:
            self.assertIn(name, entries)
            actual = sha256_hex((OVERLAY / name).read_bytes())
            self.assertEqual(actual, entries[name], name)

    def test_lakefile_schema4_append_is_self_contained(self) -> None:
        lakefile = (OVERLAY / "lakefile.schema4.append").read_text(encoding="utf-8")
        self.assertIn("lean_lib GoalGraphCore", lakefile)
        self.assertIn("lean_lib ExprGraphV2", lakefile)
        self.assertIn("lean_lib ExprGraphV3", lakefile)
        self.assertIn("lean_exe StructuredTraceV4", lakefile)
        self.assertIn("`Standalone.StructuredTraceV4", lakefile)
        self.assertNotIn("PaperTraceExport", lakefile)
        # The old workflow appends only lakefile.append; it must not see these
        # targets because it never installs their root files.
        old = (OVERLAY / "lakefile.append").read_text(encoding="utf-8")
        self.assertNotIn("ExprGraphV3", old)
        self.assertNotIn("StructuredTraceV4", old)

    @unittest.skipUnless(SOURCE_TREE.is_dir(), "local source tree is unavailable")
    def test_overlay_files_match_the_local_source_bytes(self) -> None:
        for name in NEW_OVERLAY_FILES:
            source = SOURCE_TREE / name
            self.assertTrue(source.is_file(), f"missing source for {name}")
            self.assertEqual((OVERLAY / name).read_bytes(), source.read_bytes(), name)


class WorkflowTests(unittest.TestCase):
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

    def test_workflow_is_manual_only_and_read_only(self) -> None:
        workflow = self.parsed()
        self.assertEqual(set(workflow["on"]), {"workflow_dispatch"})
        self.assertEqual(workflow["permissions"], {"contents": "read"})
        self.assertNotRegex(self.text, r"(?m)^\s*(push|pull_request|schedule|workflow_run):")
        self.assertNotRegex(self.text, r"\bgit(?:\s+-C\s+\S+)?\s+push\b|--mirror\b")
        self.assertNotRegex(self.text, r"\bgh\s+(workflow\s+run|api)\b")
        self.assertNotRegex(self.text, r"\$\{\{\s*secrets\.")

    def test_dispatch_inputs_and_defaults(self) -> None:
        inputs = self.parsed()["on"]["workflow_dispatch"]["inputs"]
        self.assertEqual(set(inputs), EXPECTED_INPUTS)
        self.assertEqual(inputs["slice"]["default"], "paper-overlay/paper-slices/slice-00.tsv")
        self.assertEqual(inputs["shard_count"]["default"], 20)
        self.assertEqual(inputs["max_parallel"]["default"], 20)
        self.assertEqual(inputs["start"]["default"], 0)
        self.assertEqual(inputs["end"]["default"], -1)
        self.assertEqual(inputs["limit"]["default"], 0)
        self.assertEqual(inputs["heartbeats"]["default"], 200000)
        self.assertEqual(inputs["timeout_seconds"]["default"], 180)
        self.assertEqual(inputs["source_ref"]["default"],
                         "e34a0535fc767479f7939a98f5699b1a6513a919")
        self.assertEqual(len(inputs), 10)  # workflow_dispatch allows at most 10
        self.assertEqual(inputs["runner_label"]["default"], "ubuntu-24.04")
        for name in ("shard_count", "max_parallel", "start", "end", "limit"):
            self.assertEqual(inputs[name]["type"], "number")
        for name in ("slice", "source_ref", "runner_label"):
            self.assertEqual(inputs[name]["type"], "string")
        self.assertTrue((ROOT / inputs["slice"]["default"]).is_file())

    def test_matrix_is_bounded_and_shards_run_in_parallel(self) -> None:
        shards = self.parsed()["jobs"]["shards"]
        self.assertEqual(shards["needs"], "prepare")
        self.assertEqual(shards["timeout-minutes"], 480)
        self.assertIs(shards["strategy"]["fail-fast"], False)
        self.assertEqual(shards["strategy"]["max-parallel"],
                         "${{ fromJSON(needs.prepare.outputs.max_parallel) }}")
        self.assertEqual(shards["strategy"]["matrix"],
                         "${{ fromJSON(needs.prepare.outputs.matrix) }}")
        plan_step = self.step("prepare", "Plan deterministic contiguous shards")
        plan = plan_step["run"]
        self.assertIn("plan_paper_shards.py", plan)
        self.assertIn('--shards "$SHARD_COUNT"', plan)
        self.assertEqual(plan_step.get("env", {}).get("SLICE_WINDOW"), "plan/input-window.tsv")
        self.assertIn('"id": shard["id"]', plan)
        self.assertIn('"label": f"{shard[\'id\']:02d}"', plan)

    def test_prepare_reuses_runtime_and_builds_the_exporter(self) -> None:
        validate = self.step("prepare", "Validate dispatch inputs and slice window")["run"]
        for token in ("SOURCE_REF", "HEARTBEATS", "TIMEOUT_SECONDS",
                      "input-window.tsv", "shard_count exceeds"):
            self.assertIn(token, validate)
        for job in ("prepare", "shards"):
            resolve = self.step(job, "Resolve pinned runtime manifest")["run"]
            self.assertIn("runtime/manifest.json", resolve)
            self.assertIn("MATHLIB_COMMIT", resolve)
            self.assertIn("NAZRIN_SOURCE_REF", resolve)
            self.assertIn("requested source_ref", resolve)
        setup = self.step("prepare", "Bootstrap pinned Nazrin and Mathlib runtime")["run"]
        self.assertIn("scripts/setup_runtime.sh", setup)
        self.assertEqual(self.step("prepare", "Bootstrap pinned Nazrin and Mathlib runtime")
                         .get("env", {}).get("GENERATE_INVENTORY"), "false")
        overlay = self.step("prepare", "Apply schema-4 overlay and build the exporter")["run"]
        for name in ("GoalGraphCore.lean", "ExprGraphV2.lean", "ExprGraphV3.lean",
                     "StructuredTraceV4.lean"):
            self.assertIn(name, overlay)
        self.assertIn("lakefile.schema4.append", overlay)
        self.assertIn("lake build StructuredTraceV4", overlay)
        self.assertIn("validate_structured_v4.py", overlay)

    def test_shard_command_matches_the_theorem_isolated_runner_contract(self) -> None:
        run = self.step("shards", "Export one schema-4 trace shard")["run"]
        for token in (
            "scripts/run_schema4_shard.py",
            '--slice "$GITHUB_WORKSPACE/plan/$SHARD_FILE"',
            '--output-dir "$GITHUB_WORKSPACE/outputs/shard-$SHARD_ID"',
            '--repo "$NAZRIN_DIR"',
            '--jobs "$JOBS"',
            '--timeout-seconds "$TIMEOUT_SECONDS"',
            '--max-heartbeats "$HEARTBEATS"',
            "--max-steps 3000",
            '--envelope-schema "$ENVELOPE_SCHEMA"',
            '--shard-id "$SHARD_ID"',
            '--plan-sha256 "$PLAN_SHA256"',
            '--limit "$LIMIT"',
            "--exporter-mode lean-run",
            "--archive-work",
            "--gzip-only",
        ):
            self.assertIn(token, run)
        self.assertEqual(self.parsed()["env"]["JOBS"], "2")
        self.assertEqual(self.parsed()["env"]["ENVELOPE_SCHEMA"], "3")
        step = self.step("shards", "Export one schema-4 trace shard")
        self.assertIs(step.get("continue-on-error"), True)
        self.assertEqual(step.get("timeout-minutes"), 300)

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
            self.assertEqual(upload["with"]["retention-days"], 14
                             if "shard" in upload["with"]["name"] or "plan" in upload["with"]["name"]
                             else 30)
        names = [upload["with"]["name"] for upload in uploads]
        self.assertEqual(len(set(names)), 3)
        self.assertIn("schema4-plan-${{ github.run_id }}", names)
        self.assertIn("schema4-shard-${{ matrix.label }}-${{ github.run_id }}", names)
        self.assertIn("schema4-package-${{ github.run_id }}-${{ github.run_attempt }}", names)
        downloads = [
            step for job in self.parsed()["jobs"].values()
            for step in job["steps"]
            if step.get("uses", "").startswith("actions/download-artifact@")
        ]
        for download in downloads:
            self.assertRegex(download["uses"], r"actions/download-artifact@[0-9a-f]{40}")
        checkouts = [
            step for job in self.parsed()["jobs"].values()
            for step in job["steps"]
            if step.get("uses", "").startswith("actions/checkout@")
        ]
        for checkout in checkouts:
            self.assertRegex(checkout["uses"], r"actions/checkout@[0-9a-f]{40}")
            self.assertIs(checkout["with"]["persist-credentials"], False)

    def test_merge_job_is_always_run_and_gated_on_completeness(self) -> None:
        merge = self.parsed()["jobs"]["merge"]
        self.assertEqual(merge["if"], "always()")
        self.assertEqual(set(merge["needs"]), {"prepare", "shards"})
        steps = merge["steps"]
        names = [step.get("name") for step in steps]
        upload_index = names.index("Upload schema-4 package")
        fail_index = names.index("Fail workflow if the package is incomplete")
        self.assertLess(upload_index, fail_index)
        self.assertIn("merge-report.json", steps[fail_index]["run"])
        sample = steps[names.index("Validate a merged-record sample (report only)")]["run"]
        self.assertIn("steps.jsonl.gz", sample)
        self.assertIn("validation-sample.jsonl", sample)
        run = steps[names.index("Merge schema-4 shards")]["run"]
        for token in ("scripts/merge_schema4_artifacts.py", "--expected-plan-sha",
                      '--output "$RUNNER_TEMP/schema4-package"', "--gzip-only",
                      '--step-summary "$GITHUB_STEP_SUMMARY"'):
            self.assertIn(token, run)

    def test_every_expression_references_a_declared_input_or_output(self) -> None:
        workflow = self.parsed()
        inputs = set(workflow["on"]["workflow_dispatch"]["inputs"])
        prepare_outputs = set(workflow["jobs"]["prepare"]["outputs"])
        expressions = re.findall(r"\$\{\{(.*?)\}\}", self.text, re.S)
        self.assertTrue(expressions)
        referenced_inputs: set[str] = set()
        for expression in expressions:
            for name in re.findall(r"\binputs\.([A-Za-z0-9_]+)", expression):
                referenced_inputs.add(name)
                self.assertIn(name, inputs, f"undeclared input in {expression!r}")
            for name in re.findall(r"\bneeds\.prepare\.outputs\.([A-Za-z0-9_]+)", expression):
                self.assertIn(name, prepare_outputs, f"undeclared prepare output in {expression!r}")
            for name in re.findall(r"\bneeds\.(?!prepare\b)([A-Za-z0-9_]+)\.outputs\.", expression):
                self.fail(f"unexpected job output reference: {expression!r}")
        self.assertEqual(referenced_inputs, inputs)


class RunnerUnitTests(unittest.TestCase):
    def test_help(self) -> None:
        result = run_cli([str(RUNNER), "--help"])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("schema-4", result.stdout)
        self.assertIn("--exporter-mode", result.stdout)

    def test_exporter_mode_resolution(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            repo = Path(temp)
            cfg = runner_module.Config(
                repo=repo, slice_path=SLICE, output_dir=repo / "out",
                rows_total=1, rows_selected=1, exporter_mode="lean-run")
            with self.assertRaises(runner_module.ConfigError):
                runner_module.resolve_exporter(cfg)
            source = repo / "Standalone" / "StructuredTraceV4.lean"
            source.parent.mkdir(parents=True)
            source.write_text("-- stub\n", encoding="utf-8")
            argv, mode = runner_module.resolve_exporter(cfg)
            self.assertEqual(mode, "lean-run")
            self.assertEqual(argv, ["lake", "env", "lean", "--run",
                                    "Standalone/StructuredTraceV4.lean"])
            binary = repo / ".lake" / "build" / "bin" / "StructuredTraceV4"
            binary.parent.mkdir(parents=True)
            binary.write_text("#!/bin/sh\n", encoding="utf-8")
            binary.chmod(0o755)
            cfg.exporter_mode = "auto"
            argv, mode = runner_module.resolve_exporter(cfg)
            self.assertEqual(mode, "binary")
            self.assertEqual(argv, [str(binary)])

    def test_one_hundred_theorem_fixture_shard(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            shard = slice_head(root / "shard.tsv", 100)
            output = root / "out"
            result = run_cli([
                str(RUNNER), "--slice", str(shard), "--output-dir", str(output),
                "--repo", str(ROOT), "--jobs", "2", "--timeout-seconds", "10",
                "--run-id", "smoke-100", "--shard-id", "3",
                "--plan-sha256", "a" * 64,
                "--exporter-cmd", fixture_command(),
                "--archive-work", "--quiet",
            ])
            self.assertEqual(result.returncode, 0, result.stderr)
            for name in ("steps.jsonl", "steps.jsonl.gz", "theorems.jsonl",
                         "theorems.jsonl.gz", "stats.json", "stats.md", "meta.json",
                         "provenance.json", "state.json", "shard.tsv", "work.tgz"):
                self.assertTrue((output / name).is_file(), name)
            self.assertFalse((output / "work").exists())
            stats = json.loads((output / "stats.json").read_text())
            self.assertEqual(stats["theorems"]["processed"], 100)
            self.assertEqual(stats["theorems"]["succeeded"], 100)
            self.assertEqual(stats["steps"]["total"], 200)
            self.assertTrue(stats["steps"]["consistent"])
            self.assertEqual(stats["shard_id"], 3)
            meta = json.loads((output / "meta.json").read_text())
            self.assertEqual(meta["rows"], 100)
            self.assertEqual(meta["steps"], 200)
            self.assertEqual(meta["plan_sha256"], "a" * 64)
            self.assertEqual(meta["schema_version"], 4)
            self.assertFalse(meta["artifacts"]["steps"]["gzip_only"])
            self.assertEqual(meta["artifacts"]["steps"]["sha256"],
                             sha256_hex((output / "steps.jsonl").read_bytes()))
            self.assertEqual(
                gzip.decompress((output / "steps.jsonl.gz").read_bytes()),
                (output / "steps.jsonl").read_bytes())
            theorems = [json.loads(line) for line in
                        (output / "theorems.jsonl").read_text().splitlines()]
            self.assertEqual(len(theorems), 100)
            expected = [line.split("\t")[1] for line in
                        shard.read_text(encoding="utf-8").splitlines()[1:]]
            self.assertEqual([item["theorem"] for item in theorems], expected)
            provenance = json.loads((output / "provenance.json").read_text())
            self.assertEqual(provenance["jobs"], 2)
            self.assertEqual(provenance["theorems"], 100)
            self.assertEqual(provenance["envelope_schema"], 3)

    def test_resume_skips_completed_theorems(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            shard = slice_head(root / "shard.tsv", 20)
            output = root / "out"
            base = [
                str(RUNNER), "--slice", str(shard), "--output-dir", str(output),
                "--repo", str(ROOT), "--jobs", "2", "--timeout-seconds", "10",
                "--exporter-cmd", fixture_command(), "--quiet",
            ]
            first = run_cli(base)
            self.assertEqual(first.returncode, 0, first.stderr)
            second = run_cli(base)
            self.assertEqual(second.returncode, 0, second.stderr)
            stats = json.loads((output / "stats.json").read_text())
            self.assertEqual(stats["theorems"]["resumed"], 20)
            self.assertEqual(stats["theorems"]["processed"], 20)
            self.assertEqual(stats["steps"]["total"], 40)

    def test_timeouts_crashes_failures_and_retry(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            shard = write_slice(root / "shard.tsv", [
                ("Fixture.Ok", "Fixture.Mod"),
                ("Fixture.Fail", "Fixture.Mod"),
                ("Fixture.Crash", "Fixture.Mod"),
                ("Fixture.Slow", "Fixture.Mod"),
            ])
            output = root / "out"
            base = [
                str(RUNNER), "--slice", str(shard), "--output-dir", str(output),
                "--repo", str(ROOT), "--jobs", "2", "--timeout-seconds", "1",
                "--exporter-cmd", fixture_command(), "--quiet",
            ]
            result = run_cli(base, env={"FAKE_EXPORTER_SLEEP": "30"})
            self.assertEqual(result.returncode, 0, result.stderr)
            theorems = {json.loads(line)["theorem"]: json.loads(line)
                        for line in (output / "theorems.jsonl").read_text().splitlines()}
            self.assertEqual(theorems["Fixture.Ok"]["status"], "success")
            self.assertEqual(theorems["Fixture.Fail"]["status"], "failure")
            self.assertEqual(theorems["Fixture.Fail"]["stage"], "tactic_rejected")
            self.assertEqual(theorems["Fixture.Crash"]["status"], "failure")
            self.assertTrue(theorems["Fixture.Crash"]["synthetic_summary"])
            self.assertEqual(theorems["Fixture.Crash"]["stage"], "crash")
            self.assertEqual(theorems["Fixture.Slow"]["status"], "failure")
            self.assertTrue(theorems["Fixture.Slow"]["timed_out"])
            self.assertEqual(theorems["Fixture.Slow"]["stage"], "wall_timeout")
            stats = json.loads((output / "stats.json").read_text())
            self.assertEqual(stats["theorems"]["synthetic_summaries"], 2)
            self.assertEqual(stats["theorems"]["timeouts"], 1)
            retry = run_cli(base + ["--retry-failures"],
                            env={"FAKE_EXPORTER_SLEEP": "0.2"})
            self.assertEqual(retry.returncode, 0, retry.stderr)
            stats = json.loads((output / "stats.json").read_text())
            self.assertEqual(stats["theorems"]["resumed"], 1)
            theorems = {json.loads(line)["theorem"]: json.loads(line)
                        for line in (output / "theorems.jsonl").read_text().splitlines()}
            self.assertEqual(theorems["Fixture.Slow"]["status"], "success")

    def test_envelope_violations_are_dropped_and_never_rewritten(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            shard = write_slice(root / "shard.tsv", [("Fixture.BadEnvelope", "Fixture.Mod")])
            output = root / "out"
            result = run_cli([
                str(RUNNER), "--slice", str(shard), "--output-dir", str(output),
                "--repo", str(ROOT), "--jobs", "1", "--timeout-seconds", "10",
                "--exporter-cmd", fixture_command(), "--quiet",
            ], env={"FAKE_EXPORTER_BAD_SCHEMA": "1", "FAKE_EXPORTER_STEPS": "3"})
            self.assertEqual(result.returncode, 0, result.stderr)
            summary = json.loads((output / "theorems.jsonl").read_text().strip())
            self.assertEqual(len(summary["envelope_violations"]), 1)
            lines = (output / "steps.jsonl").read_text().splitlines()
            self.assertEqual(len(lines), 2)
            for line in lines:
                self.assertEqual(json.loads(line)["schema_version"], 4)
            stats = json.loads((output / "stats.json").read_text())
            self.assertEqual(stats["steps"]["total"], 2)
            self.assertTrue(stats["steps"]["consistent"])

    def test_limit_selects_a_prefix_but_keeps_the_exact_shard_input(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            shard = slice_head(root / "shard.tsv", 10)
            output = root / "out"
            result = run_cli([
                str(RUNNER), "--slice", str(shard), "--output-dir", str(output),
                "--repo", str(ROOT), "--jobs", "1", "--limit", "3",
                "--exporter-cmd", fixture_command(), "--quiet",
            ])
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual((output / "shard.tsv").read_bytes(), shard.read_bytes())
            meta = json.loads((output / "meta.json").read_text())
            self.assertEqual(meta["rows"], 3)
            self.assertEqual(meta["limit"], 3)
            self.assertEqual(meta["slice"]["rows_total"], 10)


class MergeTests(unittest.TestCase):
    def make_plan(self, root: Path, rows: int, shards: int) -> tuple[Path, dict, str]:
        source = slice_head(root / "input.tsv", rows)
        plan_dir = root / "plan"
        plan = planner.plan(source, plan_dir, shards)
        digest = sha256_hex((plan_dir / "plan.json").read_bytes())
        return plan_dir, plan, digest

    def run_shard(self, plan_dir: Path, plan: dict, identifier: int, destinations: Path,
                  plan_sha: str, *, gzip_only: bool = True) -> Path:
        entry = plan["shards"][identifier]
        output = destinations / f"schema4-shard-{identifier:02d}-777"
        arguments = [
            str(RUNNER), "--slice", str(plan_dir / entry["file"]),
            "--output-dir", str(output), "--repo", str(ROOT),
            "--jobs", "2", "--timeout-seconds", "10",
            "--run-id", "777", "--shard-id", str(identifier),
            "--plan-sha256", plan_sha, "--exporter-cmd", fixture_command(), "--quiet",
        ]
        if gzip_only:
            arguments.append("--gzip-only")
        result = run_cli(arguments)
        self.assertEqual(result.returncode, 0, result.stderr)
        return output

    def test_merge_two_shards(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_dir, plan, digest = self.make_plan(root, 40, 2)
            downloads = root / "downloads"
            for identifier in range(2):
                self.run_shard(plan_dir, plan, identifier, downloads, digest)
            result = run_cli([
                str(MERGER), "--plan", str(plan_dir / "plan.json"),
                "--downloads", str(downloads), "--output", str(root / "package"),
                "--run-id", "777", "--expected-plan-sha", digest,
                "--shard-count", "2", "--limit", "0",
                "--step-summary", str(root / "summary.md"),
            ])
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads((root / "package/merge-report.json").read_text())
            self.assertTrue(report["complete"], report)
            self.assertEqual(report["totals"]["accepted"], 2)
            self.assertEqual(report["totals"]["theorems"], 40)
            self.assertEqual(report["totals"]["steps"], 80)
            stats = json.loads((root / "package/stats.json").read_text())
            self.assertEqual(stats["shards"]["accepted"], 2)
            expected = []
            for entry in plan["shards"]:
                lines = (plan_dir / entry["file"]).read_text(encoding="utf-8").splitlines()
                expected.extend(line.split("\t")[1] for line in lines[1:])
            theorems = [json.loads(line) for line in
                        (root / "package/theorems.jsonl").read_text().splitlines()]
            self.assertEqual([item["theorem"] for item in theorems], expected)
            self.assertIn("Schema-4 structured trace package",
                          (root / "package/stats.md").read_text())
            self.assertIn("### Schema-4 trace package", (root / "summary.md").read_text())

    def test_gzip_only_package_streams_compressed_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_dir, plan, digest = self.make_plan(root, 20, 2)
            downloads = root / "downloads"
            for identifier in range(2):
                self.run_shard(plan_dir, plan, identifier, downloads, digest)
            result = run_cli([
                str(MERGER), "--plan", str(plan_dir / "plan.json"),
                "--downloads", str(downloads), "--output", str(root / "package"),
                "--run-id", "777", "--expected-plan-sha", digest, "--gzip-only",
            ])
            self.assertEqual(result.returncode, 0, result.stderr)
            package = root / "package"
            self.assertFalse((package / "steps.jsonl").exists())
            self.assertFalse((package / "theorems.jsonl").exists())
            steps = gzip.decompress((package / "steps.jsonl.gz").read_bytes()).splitlines()
            theorems = gzip.decompress((package / "theorems.jsonl.gz").read_bytes()).splitlines()
            self.assertEqual(len(theorems), 20)
            self.assertEqual(len(steps), 40)
            report = json.loads((package / "merge-report.json").read_text())
            self.assertTrue(report["complete"], report)
            self.assertTrue(report["artifacts"]["steps"]["gzip_only"])
            payload = gzip.decompress((package / "steps.jsonl.gz").read_bytes())
            self.assertEqual(report["artifacts"]["steps"]["uncompressed_bytes"], len(payload))
            self.assertEqual(report["artifacts"]["steps"]["uncompressed_sha256"],
                             hashlib.sha256(payload).hexdigest())

    def test_tampered_shard_is_rejected_and_the_other_is_kept(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_dir, plan, digest = self.make_plan(root, 20, 2)
            downloads = root / "downloads"
            self.run_shard(plan_dir, plan, 0, downloads, digest)
            tampered = self.run_shard(plan_dir, plan, 1, downloads, digest)
            path = tampered / "theorems.jsonl.gz"
            lines = gzip.decompress(path.read_bytes()).splitlines()
            record = json.loads(lines[0])
            record["status"] = "success"
            record["theorem"] = "Tampered.Theorem"
            lines[0] = json.dumps(record, sort_keys=True).encode()
            with gzip.GzipFile(filename="", mode="wb", mtime=0,
                                fileobj=path.open("wb")) as handle:
                handle.write(b"\n".join(lines) + b"\n")
            result = run_cli([
                str(MERGER), "--plan", str(plan_dir / "plan.json"),
                "--downloads", str(downloads), "--output", str(root / "package"),
                "--run-id", "777", "--expected-plan-sha", digest,
            ])
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads((root / "package/merge-report.json").read_text())
            self.assertFalse(report["complete"])
            self.assertEqual(report["invalid_shards"], [1])
            self.assertEqual(report["totals"]["accepted"], 1)
            self.assertEqual(report["totals"]["theorems"], 10)
            merged = [json.loads(line)["theorem"] for line in
                      (root / "package/theorems.jsonl").read_text().splitlines()]
            self.assertTrue(merged)
            self.assertNotIn("Tampered.Theorem", merged)

    def test_missing_shard_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_dir, plan, digest = self.make_plan(root, 20, 2)
            downloads = root / "downloads"
            self.run_shard(plan_dir, plan, 0, downloads, digest)
            result = run_cli([
                str(MERGER), "--plan", str(plan_dir / "plan.json"),
                "--downloads", str(downloads), "--output", str(root / "package"),
                "--run-id", "777", "--expected-plan-sha", digest,
            ])
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads((root / "package/merge-report.json").read_text())
            self.assertFalse(report["complete"])
            self.assertEqual(report["missing_shards"], [1])
            self.assertEqual(report["totals"]["theorems"], 10)

    def test_merge_without_a_plan(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            shard = slice_head(root / "shard.tsv", 5)
            downloads = root / "downloads"
            output = downloads / "schema4-shard-00-9"
            result = run_cli([
                str(RUNNER), "--slice", str(shard), "--output-dir", str(output),
                "--repo", str(ROOT), "--jobs", "1", "--run-id", "9",
                "--shard-id", "0", "--exporter-cmd", fixture_command(), "--quiet",
            ])
            self.assertEqual(result.returncode, 0, result.stderr)
            merged = run_cli([
                str(MERGER), "--downloads", str(downloads),
                "--output", str(root / "package"), "--shard-count", "1",
            ])
            self.assertEqual(merged.returncode, 0, merged.stderr)
            report = json.loads((root / "package/merge-report.json").read_text())
            self.assertTrue(report["complete"], report)
            self.assertEqual(report["totals"]["theorems"], 5)
            # The plain JSONL artifacts (no gzip-only) are read directly.
            self.assertTrue((root / "package/steps.jsonl").is_file())


class SourceAnchorTests(unittest.TestCase):
    """The exporter and overlay must stay anchored to the paper and source tree."""

    def test_overlay_exporter_documents_the_paper_contract(self) -> None:
        text = (OVERLAY / "Standalone/StructuredTraceV4.lean").read_text(encoding="utf-8")
        for anchor in ("§IV", "§V", "§VI", "3,000", "schema_version", "Usage:"):
            self.assertIn(anchor, text)
        self.assertIn("lean --run Standalone/StructuredTraceV4.lean MODULE THEOREM OUTPUT_PATH",
                      text)


if __name__ == "__main__":
    unittest.main()