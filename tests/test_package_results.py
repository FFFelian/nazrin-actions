from __future__ import annotations

import importlib.util
import json
import tarfile
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "package_results.py"
SPEC = importlib.util.spec_from_file_location("package_results", SCRIPT)
assert SPEC and SPEC.loader
package_results = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(package_results)


class PackageResultsTests(unittest.TestCase):
    def make_plan(self, root: Path) -> tuple[Path, Path]:
        plan_dir = root / "plan"
        plan_dir.mkdir()
        shards = []
        for shard_id in range(2):
            name = f"shard-{shard_id:02d}.tsv"
            path = plan_dir / name
            path.write_text(
                "index\ttheorem\tmodule\n"
                f"{shard_id}\tTest.thm{shard_id}\tMathlib.Test\n",
                encoding="utf-8",
            )
            import hashlib

            shards.append({"id": shard_id, "inventory": name, "rows": 1,
                           "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        plan_path = plan_dir / "plan.json"
        plan_path.write_text(json.dumps({"schema": 1, "shard_count": 2, "shards": shards}), encoding="utf-8")
        return plan_path, plan_dir

    def make_archive(self, root: Path, plan_dir: Path, shard_id: int, status: str = "success") -> Path:
        import hashlib

        inventory = plan_dir / f"shard-{shard_id:02d}.tsv"
        inventory_sha = hashlib.sha256(inventory.read_bytes()).hexdigest()
        stage = root / f"stage-{shard_id}"
        stage.mkdir()
        (stage / "shard-manifest.json").write_text(
            json.dumps({"shard_id": shard_id, "status": "complete", "input_rows": 1,
                        "inventory_sha256": inventory_sha, "terminal_rows": 1,
                        "terminal_status_counts": {status: 1}}),
            encoding="utf-8",
        )
        (stage / "deferred.tsv").write_text("index\ttheorem\tmodule\n", encoding="utf-8")
        (stage / ".bounded-results.jsonl").write_text(
            json.dumps({"index": shard_id, "theorem": f"Test.thm{shard_id}",
                        "module": "Mathlib.Test", "status": status,
                        "filename": f"trace-{shard_id}.txt"}) + "\n",
            encoding="utf-8",
        )
        (stage / f"trace-{shard_id}.txt").write_text("goal\ttactic\t\n", encoding="utf-8")
        archives = root / "artifacts"
        archives.mkdir(exist_ok=True)
        archive = archives / f"shard-{shard_id:02d}.tar.gz"
        with tarfile.open(archive, "w:gz") as tar:
            for item in stage.iterdir():
                tar.add(item, arcname=item.name)
        return archive

    def test_missing_shard_is_incomplete_and_names_deferred_rows(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan_dir = self.make_plan(root)
            self.make_archive(root, plan_dir, 0)
            report = package_results.package(plan_path, plan_dir, root / "artifacts", root / "out")
            self.assertFalse(report["complete"])
            self.assertEqual(report["missing_shard_ids"], [1])
            self.assertEqual(report["deferred_rows"], 1)
            self.assertTrue((root / "out" / "atomization-results.tar.gz").is_file())

    def test_full_package_preserves_hidden_ledgers_per_shard(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            plan_path, plan_dir = self.make_plan(root)
            self.make_archive(root, plan_dir, 0)
            self.make_archive(root, plan_dir, 1, status="failure")
            report = package_results.package(plan_path, plan_dir, root / "artifacts", root / "out")
            self.assertTrue(report["complete"])
            self.assertEqual(report["terminal_rows"], 2)
            self.assertTrue((root / "out" / "shards" / "shard-00" / ".bounded-results.jsonl").is_file())
            self.assertTrue((root / "out" / "shards" / "shard-01" / ".bounded-results.jsonl").is_file())
            self.assertEqual(report["terminal_status_counts"], {"failure": 1, "success": 1})


if __name__ == "__main__":
    unittest.main()
