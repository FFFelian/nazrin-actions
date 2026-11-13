from __future__ import annotations

import hashlib
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "plan_paper_shards.py"
SPEC = importlib.util.spec_from_file_location("plan_paper_shards", SCRIPT)
assert SPEC and SPEC.loader
plan_paper_shards = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(plan_paper_shards)


class PlanPaperShardsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def write_tsv(self, rows: int, name: str = "slice.tsv") -> Path:
        lines = ["index\ttheorem\tmodule\tslice\ttopo_rank"]
        lines.extend(
            f"{index}\tTest.theorem{index}\tMathlib.Module{index % 5}\t0\t{index}"
            for index in range(rows)
        )
        path = self.root / name
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        return path

    def test_balanced_contiguous_partition_preserves_every_row(self) -> None:
        source = self.write_tsv(23)
        result = plan_paper_shards.plan(source, self.root / "plan", 5)
        self.assertEqual([shard["rows"] for shard in result["shards"]], [5, 5, 5, 4, 4])
        self.assertEqual(result["total_rows"], 23)

        observed: list[str] = []
        for shard in result["shards"]:
            path = self.root / "plan" / shard["file"]
            lines = path.read_text(encoding="utf-8").splitlines()
            self.assertEqual(lines[0], "index\ttheorem\tmodule\tslice\ttopo_rank")
            self.assertEqual(len(lines) - 1, shard["rows"])
            observed.extend(line.split("\t")[1] for line in lines[1:])
        self.assertEqual(observed, [f"Test.theorem{index}" for index in range(23)])

    def test_plan_and_shards_are_byte_deterministic(self) -> None:
        source = self.write_tsv(31)
        first = plan_paper_shards.plan(source, self.root / "first", 7)
        second = plan_paper_shards.plan(source, self.root / "second", 7)
        self.assertEqual(first, second)
        self.assertEqual(
            (self.root / "first" / "plan.json").read_bytes(),
            (self.root / "second" / "plan.json").read_bytes(),
        )
        for shard in first["shards"]:
            self.assertEqual(
                (self.root / "first" / shard["file"]).read_bytes(),
                (self.root / "second" / shard["file"]).read_bytes(),
            )

    def test_sha256_fields_match_actual_file_bytes(self) -> None:
        source = self.write_tsv(17)
        result = plan_paper_shards.plan(source, self.root / "plan", 4)
        self.assertEqual(
            result["input"]["sha256"], hashlib.sha256(source.read_bytes()).hexdigest()
        )
        for shard in result["shards"]:
            payload = (self.root / "plan" / shard["file"]).read_bytes()
            self.assertEqual(shard["sha256"], hashlib.sha256(payload).hexdigest())
        self.assertEqual(
            sum(int(shard["rows"]) for shard in result["shards"]), 17
        )

    def test_empty_and_header_only_inputs_are_rejected(self) -> None:
        empty = self.root / "empty.tsv"
        empty.write_bytes(b"")
        with self.assertRaisesRegex(ValueError, "empty input"):
            plan_paper_shards.plan(empty, self.root / "empty-plan", 2)

        header_only = self.root / "header.tsv"
        header_only.write_text("index\ttheorem\tmodule\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "no data rows"):
            plan_paper_shards.plan(header_only, self.root / "header-plan", 2)

    def test_missing_theorem_column_and_malformed_rows_are_rejected(self) -> None:
        cases = {
            "missing.tsv": (
                "index\tname\tmodule\n0\tTest.one\tMathlib.Test\n",
                "exactly one 'theorem' column",
            ),
            "duplicate-header.tsv": (
                "index\ttheorem\ttheorem\n0\tTest.one\tTest.two\n",
                "duplicate column names",
            ),
            "short-row.tsv": (
                "index\ttheorem\tmodule\n0\tTest.one\n",
                "expected 3 columns",
            ),
            "empty-theorem.tsv": (
                "index\ttheorem\tmodule\n0\t\tMathlib.Test\n",
                "empty theorem name",
            ),
            "duplicate-theorem.tsv": (
                "index\ttheorem\tmodule\n0\tTest.one\tMathlib.Test\n"
                "1\tTest.one\tMathlib.Other\n",
                "duplicate theorem",
            ),
            "blank-line.tsv": (
                "index\ttheorem\tmodule\n0\tTest.one\tMathlib.Test\n\n",
                "blank lines",
            ),
        }
        for name, (text, message) in cases.items():
            with self.subTest(name=name):
                path = self.root / name
                path.write_text(text, encoding="utf-8")
                with self.assertRaisesRegex(ValueError, message):
                    plan_paper_shards.plan(path, self.root / f"out-{name}", 1)

    def test_shard_count_bounds_and_empty_shards_are_rejected(self) -> None:
        source = self.write_tsv(3)
        for count in (0, 21):
            with self.subTest(count=count):
                with self.assertRaisesRegex(ValueError, "between 1 and 20"):
                    plan_paper_shards.plan(source, self.root / f"out-{count}", count)
        with self.assertRaisesRegex(ValueError, "empty shards are not supported"):
            plan_paper_shards.plan(source, self.root / "out-too-many", 4)

    def test_extra_columns_and_crlf_are_preserved_without_theorem_duplication(self) -> None:
        source = self.root / "proof-eval.tsv"
        source.write_bytes(
            b"theorem\tmodule\tnote\r\n"
            b"Test.alpha\tMathlib.Alpha\tfirst\r\n"
            b"Test.beta\tMathlib.Beta\tsecond\r\n"
        )
        result = plan_paper_shards.plan(source, self.root / "plan", 2)
        self.assertEqual(result["input"]["columns"], ["theorem", "module", "note"])
        self.assertEqual(result["input"]["theorem_column"], 0)
        self.assertEqual([shard["rows"] for shard in result["shards"]], [1, 1])
        self.assertEqual(
            (self.root / "plan" / "shard-00.tsv").read_bytes(),
            b"theorem\tmodule\tnote\nTest.alpha\tMathlib.Alpha\tfirst\n",
        )

    def test_cli_returns_nonzero_for_bad_input_and_writes_nothing(self) -> None:
        bad = self.root / "bad.tsv"
        bad.write_text("index\tname\n0\tTest.one\n", encoding="utf-8")
        output = self.root / "cli-plan"
        process = __import__("subprocess").run(
            [__import__("sys").executable, str(SCRIPT), "--input", str(bad),
             "--output", str(output), "--shards", "2"],
            capture_output=True,
            text=True,
        )
        self.assertEqual(process.returncode, 2)
        self.assertIn("theorem", process.stderr)
        self.assertFalse((output / "plan.json").exists())


if __name__ == "__main__":
    unittest.main()
