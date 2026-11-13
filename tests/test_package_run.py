from __future__ import annotations

import hashlib
import importlib.util
import json
import shutil
import tarfile
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
for name in ("plan_shards", "run_shard", "package_run"):
    script = ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, script)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    import sys

    sys.path.insert(0, str(ROOT / "scripts"))
    spec.loader.exec_module(module)
    globals()[name] = module


class PackageRunTests(unittest.TestCase):
    def make_plan(self, root: Path) -> tuple[Path, dict]:
        inventory = root / "full-inventory.tsv"
        lines = ["index\ttheorem\tmodule"]
        lines.extend(f"{i}\tTest.thm{i}\tMathlib.Test" for i in range(23))
        inventory.write_text("\n".join(lines) + "\n", encoding="utf-8")
        plan_dir = root / "plan"
        plan = plan_shards.plan(inventory, plan_dir, 2, "a" * 40)
        return plan_dir / "plan.json", plan

    def make_artifact(self, artifacts: Path, plan_dir: Path, plan: dict, shard_id: int) -> Path:
        entry = plan["shards"][shard_id]
        root = artifacts / f"worker-{shard_id}" / f"shard-{shard_id}"
        root.mkdir(parents=True)
        inventory = plan_dir / entry["inventory"]
        (root / "shard-input.tsv").write_bytes(inventory.read_bytes())
        rows = plan_shards.parse_inventory(inventory)
        records = []
        for row in rows:
            trace = f"trace-{row['index']}.txt"
            (root / trace).write_text("goal\ttactic\t\n", encoding="utf-8")
            records.append({"index": row["index"], "theorem": row["theorem"],
                            "module": row["module"], "status": "success", "filename": trace})
        (root / ".bounded-results.jsonl").write_text(
            "".join(json.dumps(record) + "\n" for record in records), encoding="utf-8"
        )
        (root / "shard-summary.json").write_text(json.dumps({
            "schema": 1,
            "shard_id": shard_id,
            "status": "finished",
            "source_commit": plan["source_commit"],
            "inventory_sha256": entry["sha256"],
            "inventory_rows": len(rows),
            "terminal_rows": len(rows),
            "pending_rows": 0,
            "terminal_status_counts": {"success": len(rows)},
            "timeout_seconds_per_theorem": 30,
            "lean_internal_workers": 2,
            "supervisor_exit_code": 0,
        }), encoding="utf-8")
        return root

    def test_missing_shard_rows_remain_in_pending_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan = self.make_plan(root)
            artifacts = root / "artifacts"
            artifacts.mkdir()
            self.make_artifact(artifacts, plan_path.parent, plan, 0)
            result = package_run.package(plan_path, artifacts, root / "output")
            pending = plan_shards.parse_inventory(root / "output" / "package-content" / "pending-inventory.tsv")
            expected_missing = plan_shards.parse_inventory(plan_path.parent / plan["shards"][1]["inventory"])
            self.assertFalse(result["complete"])
            self.assertEqual(result["pending_rows"], len(expected_missing))
            self.assertEqual(
                {(r["index"], r["theorem"], r["module"]) for r in pending},
                {(r["index"], r["theorem"], r["module"]) for r in expected_missing},
            )

    def test_complete_shards_are_validated_and_kept_namespaced(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan = self.make_plan(root)
            artifacts = root / "artifacts"
            for shard_id in range(2):
                self.make_artifact(artifacts, plan_path.parent, plan, shard_id)
            result = package_run.package(plan_path, artifacts, root / "output")
            self.assertTrue(result["complete"], result["issues"])
            self.assertEqual(result["pending_rows"], 0)
            self.assertTrue((root / "output/package-content/plan/canonical-inventory.tsv").is_file())
            self.assertTrue((root / "output/package-content/plan/plan.json").is_file())
            for shard_id in range(2):
                self.assertTrue((root / "output" / "package-content" / "shards" /
                                 f"shard-{shard_id:02d}" / ".bounded-results.jsonl").is_file())
            self.assertTrue(Path(result["archive"]).is_file())

    def test_runtime_provenance_mismatch_revokes_only_affected_shard(self) -> None:
        for tamper in (False, True):
            with self.subTest(tamper=tamper), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                plan_path, plan = self.make_plan(root)
                identity = {"source_commit": plan["source_commit"], "mathlib_commit": "b" * 40,
                            "runtime_manifest_sha256": "c" * 64}
                provenance = plan_path.parent / "runtime-provenance.json"
                provenance.write_text(json.dumps(identity))
                plan = plan_shards.plan(root / "full-inventory.tsv", plan_path.parent, 2,
                                        plan["source_commit"], provenance)
                artifacts = root / "artifacts"
                for shard_id in range(2):
                    shard = self.make_artifact(artifacts, plan_path.parent, plan, shard_id)
                    (shard / "runtime-provenance.json").write_bytes(provenance.read_bytes())
                    summary_path = shard / "shard-summary.json"
                    summary = json.loads(summary_path.read_text())
                    summary["runtime_manifest_sha256"] = identity["runtime_manifest_sha256"]
                    summary_path.write_text(json.dumps(summary))
                    if tamper and shard_id == 0:
                        (shard / "runtime-provenance.json").write_text('{}')
                result = package_run.package(plan_path, artifacts, root / "output")
                self.assertEqual(result["complete"], not tamper, result["issues"])
                self.assertEqual(result["pending_rows"], plan["shards"][0]["rows"] if tamper else 0)
                self.assertTrue((root / "output/package-content/plan/runtime-provenance.json").is_file())

    def test_source_mismatch_keeps_the_shard_pending(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan = self.make_plan(root)
            artifacts = root / "artifacts"
            shard = self.make_artifact(artifacts, plan_path.parent, plan, 0)
            summary_path = shard / "shard-summary.json"
            summary = json.loads(summary_path.read_text())
            summary["source_commit"] = "b" * 40
            summary_path.write_text(json.dumps(summary))

            result = package_run.package(plan_path, artifacts, root / "output")
            expected = plan_shards.parse_inventory(plan_path.parent / plan["shards"][0]["inventory"])
            pending = plan_shards.parse_inventory(root / "output/package-content/pending-inventory.tsv")
            self.assertFalse(result["complete"])
            self.assertTrue(any("source commit mismatch" in issue for issue in result["issues"]))
            self.assertEqual({row["index"] for row in pending},
                             {row["index"] for row in expected} |
                             {row["index"] for row in plan_shards.parse_inventory(
                                 plan_path.parent / plan["shards"][1]["inventory"])})

    def test_summary_coverage_mismatch_keeps_all_shard_rows_pending(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan = self.make_plan(root)
            artifacts = root / "artifacts"
            shard = self.make_artifact(artifacts, plan_path.parent, plan, 0)
            summary_path = shard / "shard-summary.json"
            summary = json.loads(summary_path.read_text())
            summary["pending_rows"] = 1
            summary_path.write_text(json.dumps(summary))

            result = package_run.package(plan_path, artifacts, root / "output")
            pending = plan_shards.parse_inventory(root / "output/package-content/pending-inventory.tsv")
            shard_rows = plan_shards.parse_inventory(plan_path.parent / plan["shards"][0]["inventory"])
            self.assertFalse(result["complete"])
            self.assertTrue(any("summary pending row count mismatch" in issue for issue in result["issues"]))
            self.assertTrue({row["index"] for row in shard_rows}.issubset({row["index"] for row in pending}))

    def test_failed_and_interrupted_shards_retain_valid_partial_coverage(self) -> None:
        for status in ("failed", "interrupted"):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                plan_path, plan = self.make_plan(root)
                artifacts = root / "artifacts"
                shard = self.make_artifact(artifacts, plan_path.parent, plan, 0)
                rows = plan_shards.parse_inventory(shard / "shard-input.tsv")
                ledger = shard / ".bounded-results.jsonl"
                ledger.write_text(ledger.read_text().splitlines()[0] + "\n")
                summary_path = shard / "shard-summary.json"
                summary = json.loads(summary_path.read_text())
                summary.update(status=status, terminal_rows=1, pending_rows=len(rows) - 1,
                               terminal_status_counts={"success": 1}, supervisor_exit_code=1)
                summary_path.write_text(json.dumps(summary))

                result = package_run.package(plan_path, artifacts, root / "output")
                pending = plan_shards.parse_inventory(root / "output/package-content/pending-inventory.tsv")
                self.assertFalse(result["complete"])
                self.assertEqual(result["completed_terminal_rows"], 1)
                self.assertEqual(result["pending_rows"], plan["inventory"]["rows"] - 1)
                self.assertNotIn(rows[0]["index"], {row["index"] for row in pending})

    def test_duplicate_and_unexpected_artifacts_are_preserved_without_coverage(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan = self.make_plan(root)
            artifacts = root / "artifacts"
            shard = self.make_artifact(artifacts, plan_path.parent, plan, 0)
            shutil.copytree(shard, artifacts / "duplicate")
            unexpected = artifacts / "unexpected"
            shutil.copytree(shard, unexpected)
            summary_path = unexpected / "shard-summary.json"
            summary = json.loads(summary_path.read_text())
            summary["shard_id"] = 9
            summary_path.write_text(json.dumps(summary))

            result = package_run.package(plan_path, artifacts, root / "output")
            self.assertFalse(result["complete"])
            self.assertEqual(result["duplicate_shards"], [0])
            self.assertEqual(result["pending_rows"], plan["inventory"]["rows"])
            packaged = root / "output/package-content/shards"
            self.assertTrue((packaged / "duplicate-00-0/.bounded-results.jsonl").is_file())
            self.assertTrue((packaged / "duplicate-00-1/.bounded-results.jsonl").is_file())
            self.assertTrue((packaged / "unexpected-9-0/.bounded-results.jsonl").is_file())

    def test_symlinked_ledger_and_unclassified_artifact_do_not_count(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan = self.make_plan(root)
            artifacts = root / "artifacts"
            shard = self.make_artifact(artifacts, plan_path.parent, plan, 0)
            ledger = shard / ".bounded-results.jsonl"
            ledger.unlink()
            ledger.symlink_to(shard / "shard-input.tsv")
            orphan = artifacts / "orphan"
            orphan.mkdir(parents=True)
            (orphan / "trace.txt").write_text("partial")

            result = package_run.package(plan_path, artifacts, root / "output")
            pending = plan_shards.parse_inventory(root / "output/package-content/pending-inventory.tsv")
            shard_rows = plan_shards.parse_inventory(plan_path.parent / plan["shards"][0]["inventory"])
            self.assertFalse(result["complete"])
            self.assertTrue(any("unclassified result artifact" in issue for issue in result["issues"]))
            self.assertTrue({row["index"] for row in shard_rows}.issubset({row["index"] for row in pending}))
            self.assertTrue(any(path.name.startswith("unclassified-")
                                for path in (root / "output/package-content/shards").iterdir()))
            with tarfile.open(result["archive"]) as archive:
                self.assertFalse(any(item.issym() or item.islnk() for item in archive.getmembers()))
                self.assertTrue(any(item.name.endswith(".rejected-symlink.txt")
                                    for item in archive.getmembers()))


if __name__ == "__main__":
    unittest.main()
