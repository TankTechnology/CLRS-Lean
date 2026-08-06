#!/usr/bin/env python3
"""Regression tests for deterministic Verso shard planning."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from plan_literate_shards import ModuleCost, discover_modules, partition_modules, write_plan


class LiterateShardPlannerTests(unittest.TestCase):
    def test_discovers_tab_separated_module_map_and_json_sizes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            first = root / "A.json"
            second = root / "B.json"
            first.write_bytes(b"1234")
            second.write_bytes(b"123456")
            module_map = root / "module-map"
            module_map.write_text(
                f"CLRSLean.Chapter_01\t{first}\t.\n"
                f"CLRSLean.Chapter_02\t{second}\t.\n",
                encoding="utf-8",
            )

            modules = discover_modules(module_map)

        self.assertEqual(
            [("CLRSLean.Chapter_01", 4), ("CLRSLean.Chapter_02", 6)],
            [(module.name, module.size_bytes) for module in modules],
        )

    def test_partition_is_deterministic_complete_and_balanced(self) -> None:
        modules = [
            ModuleCost("CLRSLean.Chapter_01.Section_01_1", Path("a"), 40),
            ModuleCost("CLRSLean.Chapter_01.Section_01_2", Path("b"), 30),
            ModuleCost("CLRSLean.Chapter_02", Path("c"), 60),
            ModuleCost("CLRSLean.Chapter_03", Path("d"), 10),
        ]

        first = partition_modules(modules, 2)
        second = partition_modules(list(reversed(modules)), 2)

        self.assertEqual(first, second)
        flattened = [module.name for shard in first for module in shard]
        self.assertCountEqual([module.name for module in modules], flattened)
        self.assertEqual(len(flattened), len(set(flattened)))
        # Chapter affinity: both Chapter 1 pages stay together.
        chapter_one_shards = {
            index
            for index, shard in enumerate(first)
            if any(module.name.startswith("CLRSLean.Chapter_01") for module in shard)
        }
        self.assertEqual({0}, chapter_one_shards)

    def test_rejects_non_positive_shard_count(self) -> None:
        with self.assertRaisesRegex(ValueError, "positive"):
            partition_modules([], 0)

    def test_write_plan_defaults_to_four_shards_and_reports_skew(self) -> None:
        modules = [
            ModuleCost(f"CLRSLean.Chapter_{index:02d}", Path(str(index)), index)
            for index in range(1, 9)
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = write_plan(
                modules,
                root,
                input_digest="abc123",
            )
            loaded = json.loads((root / "manifest.json").read_text(encoding="utf-8"))

            self.assertEqual(4, manifest["shard_count"])
            self.assertEqual(manifest, loaded)
            self.assertEqual(8, loaded["module_count"])
            self.assertIn("max_load_skew_bytes", loaded)
            for index in range(4):
                self.assertTrue((root / f"shard-{index}.txt").is_file())


if __name__ == "__main__":
    unittest.main()
