from __future__ import annotations

import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"


def load(name: str):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


planner = load("plan_paper_shards")
packager = load("package_paper_shards")


class PackagePaperShardsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.run_id = "12345"

    def make_plan(self, rows: int = 6, shards: int = 2) -> tuple[Path, dict]:
        source = self.root / "slice.tsv"
        lines = ["index\ttheorem\tmodule\ttopo_rank"]
        lines.extend(
            f"{index}\tTest.thm{index}\tMathlib.Test\t{index}" for index in range(rows)
        )
        source.write_text("\n".join(lines) + "\n", encoding="utf-8")
        plan_dir = self.root / "plan"
        result = planner.plan(source, plan_dir, shards)
        return plan_dir, result

    def write_artifact(self, plan_dir: Path, plan: dict, shard_id: int, *,
                       limit: int = 0, tamper: bool = False) -> Path:
        entry = plan["shards"][shard_id]
        artifact = self.root / "downloads" / f"paper-trace-shard-{shard_id:02d}-{self.run_id}"
        artifact.mkdir(parents=True)
        shard_tsv = plan_dir / entry["file"]
        (artifact / "shard.tsv").write_bytes(shard_tsv.read_bytes())
        lines = shard_tsv.read_text(encoding="utf-8").splitlines()
        theorem_column = lines[0].split("\t").index("theorem")
        names = [line.split("\t")[theorem_column] for line in lines[1:]]
        if limit > 0:
            names = names[:limit]
        steps = [
            {"schema": 1, "theorem": name, "step": 0, "goal_id": f"{name}:g0"}
            for name in names
        ]
        graphs = [
            {"schema": 1, "theorem": name, "goal_id": f"{name}:g0",
             "graph": {"schema": 1, "root": 0, "nodes": [], "edges": []}}
            for name in names
        ]
        for filename, records in (("steps.jsonl", steps), ("graphs.jsonl", graphs),
                                  ("failures.jsonl", [])):
            (artifact / filename).write_text(
                "".join(json.dumps(record) + "\n" for record in records), encoding="utf-8"
            )
        meta = {
            "schema": 1,
            "module": "Mathlib",
            "input_sha256": entry["sha256"],
            "theorems_requested": len(names),
            "theorems_succeeded": len(names),
            "theorems_failed": 0,
            "steps": len(steps) + (1 if tamper else 0),
            "graphs": len(graphs),
            "warnings": 0,
            "unmodeled_steps": 0,
            "elapsed_ms": 10,
        }
        (artifact / "meta.json").write_text(json.dumps(meta), encoding="utf-8")
        return artifact

    def test_complete_merge_copies_shards_and_reports_totals(self) -> None:
        plan_dir, plan = self.make_plan()
        for shard_id in range(2):
            self.write_artifact(plan_dir, plan, shard_id)
        output = self.root / "package"
        report = packager.package(
            plan_dir / "plan.json", self.root / "downloads", output,
            run_id=self.run_id,
            expected_plan_sha=hashlib.sha256((plan_dir / "plan.json").read_bytes()).hexdigest(),
            shard_count=2,
        )
        self.assertTrue(report["complete"], report["issues"])
        summary = json.loads((output / "package-summary.json").read_text())
        self.assertEqual(summary["steps"], 6)
        self.assertEqual(summary["theorems_succeeded"], 6)
        self.assertEqual(len((output / "steps.jsonl").read_text().splitlines()), 6)
        self.assertTrue((output / "shards/shard-01/meta.json").is_file())
        self.assertTrue((output / "plan/shard-01.tsv").is_file())

    def test_missing_shard_is_reported_and_not_merged(self) -> None:
        plan_dir, plan = self.make_plan(rows=6, shards=2)
        self.write_artifact(plan_dir, plan, 0)
        report = packager.package(
            plan_dir / "plan.json", self.root / "downloads", self.root / "package",
            run_id=self.run_id, shard_count=2,
        )
        self.assertFalse(report["complete"])
        self.assertEqual(report["missing_shards"], [1])
        self.assertEqual(report["totals"]["steps"], 3)
        self.assertEqual(len(report["shards"]), 2)

    def test_meta_step_count_mismatch_invalidates_only_that_shard(self) -> None:
        plan_dir, plan = self.make_plan(rows=6, shards=2)
        self.write_artifact(plan_dir, plan, 0, tamper=True)
        self.write_artifact(plan_dir, plan, 1)
        report = packager.package(
            plan_dir / "plan.json", self.root / "downloads", self.root / "package",
            run_id=self.run_id, shard_count=2,
        )
        self.assertFalse(report["complete"])
        self.assertEqual(report["invalid_shards"], [0])
        self.assertEqual(report["totals"]["steps"], 3)
        self.assertEqual(len((self.root / "package/steps.jsonl").read_text().splitlines()), 3)

    def test_limit_changes_expected_requested_rows(self) -> None:
        plan_dir, plan = self.make_plan(rows=6, shards=2)
        for shard_id in range(2):
            self.write_artifact(plan_dir, plan, shard_id, limit=2)
        report = packager.package(
            plan_dir / "plan.json", self.root / "downloads", self.root / "package",
            run_id=self.run_id, limit=2, shard_count=2,
        )
        self.assertTrue(report["complete"], report["issues"])
        self.assertEqual(report["totals"]["theorems_requested"], 4)
        self.assertEqual(report["totals"]["steps"], 4)


if __name__ == "__main__":
    unittest.main()
