from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "plan_shards.py"
SPEC = importlib.util.spec_from_file_location("plan_shards", SCRIPT)
assert SPEC and SPEC.loader
plan_shards = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(plan_shards)


class PlanShardsTests(unittest.TestCase):
    def test_partition_is_stable_disjoint_and_complete(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            inventory = root / "theorems.tsv"
            rows = ["index\ttheorem\tmodule"]
            rows.extend(
                f"{index}\tTest.theorem{index}\tMathlib.Module{index % 7}"
                for index in range(103)
            )
            inventory.write_text("\n".join(rows) + "\n", encoding="utf-8")

            first = plan_shards.plan(inventory, root / "first", 10, "a" * 40)
            second = plan_shards.plan(inventory, root / "second", 10, "a" * 40)
            self.assertEqual(first["shards"], second["shards"])

            observed: dict[tuple[str, str], int] = {}
            for shard in first["shards"]:
                shard_rows = plan_shards.parse_inventory(root / "first" / shard["inventory"])
                self.assertEqual(len(shard_rows), shard["rows"])
                for row in shard_rows:
                    key = (str(row["module"]), str(row["theorem"]))
                    self.assertNotIn(key, observed)
                    observed[key] = int(shard["id"])
                    self.assertEqual(
                        observed[key],
                        plan_shards.stable_shard(key[0], key[1], 10),
                    )

            self.assertEqual(len(observed), 103)
            self.assertEqual(sum(item["rows"] for item in first["shards"]), 103)

    def test_invalid_duplicate_inventory_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            inventory = Path(temp) / "theorems.tsv"
            inventory.write_text(
                "index\ttheorem\tmodule\n"
                "0\tTest.one\tMathlib.Test\n"
                "0\tTest.two\tMathlib.Test\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "duplicate inventory index"):
                plan_shards.parse_inventory(inventory)

    def test_source_revision_must_be_full_commit(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            inventory = root / "theorems.tsv"
            inventory.write_text(
                "index\ttheorem\tmodule\n0\tTest.one\tMathlib.Test\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "full 40-character Git SHA"):
                plan_shards.plan(inventory, root / "out", 10, "main")


if __name__ == "__main__":
    unittest.main()
