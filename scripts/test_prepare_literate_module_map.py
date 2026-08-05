#!/usr/bin/env python3
"""Tests for creating a portable Verso module map from literate JSON."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from prepare_literate_module_map import write_module_map


class PrepareLiterateModuleMapTests(unittest.TestCase):
    def test_writes_sorted_modules_and_ignores_sidecars(self) -> None:
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as tmp:
            root = Path(tmp)
            literate = root / "literate"
            (literate / "CLRSLean" / "Chapter_02").mkdir(parents=True)
            sources = root / "sources"
            (sources / "CLRSLean" / "Chapter_02").mkdir(parents=True)
            (sources / "CLRSLean" / "Chapter_02.lean").write_text("")
            (sources / "CLRSLean" / "Chapter_02" / "Section.lean").write_text("")
            (literate / "CLRSLean" / "Chapter_02.json").write_text("{}")
            nested = literate / "CLRSLean" / "Chapter_02" / "Section.json"
            nested.write_text("{}")
            nested.with_suffix(".json.hash").write_text("ignored")
            output = root / "module-map"

            count = write_module_map(literate, output, sources)

            rows = output.read_text(encoding="utf-8").splitlines()
        self.assertEqual(2, count)
        self.assertEqual("CLRSLean.Chapter_02", rows[0].split("\t")[0])
        self.assertEqual("CLRSLean.Chapter_02.Section", rows[1].split("\t")[0])
        self.assertTrue(all(len(row.split("\t")) == 3 for row in rows))

    def test_prunes_orphan_json_and_sidecars_but_retains_current_module(self) -> None:
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as tmp:
            root = Path(tmp)
            literate = root / "literate" / "CLRSLean"
            literate.mkdir(parents=True)
            sources = root / "sources"
            (sources / "CLRSLean").mkdir(parents=True)

            current_source = sources / "CLRSLean" / "Current.lean"
            current_source.write_text("")
            current_json = literate / "Current.json"
            stale_json = literate / "Renamed.json"
            current_json.write_text("current")
            stale_json.write_text("stale")
            current_json.with_suffix(".json.hash").write_text("current hash")
            stale_json.with_suffix(".json.hash").write_text("stale hash")
            stale_json.with_suffix(".json.trace").write_text("stale trace")
            output = root / "module-map"

            count = write_module_map(
                root / "literate",
                output,
                sources,
                prune_orphans=True,
            )

            rows = output.read_text(encoding="utf-8").splitlines()
            self.assertEqual(1, count)
            self.assertEqual("CLRSLean.Current", rows[0].split("\t")[0])
            self.assertTrue(current_json.is_file())
            self.assertTrue(current_json.with_suffix(".json.hash").is_file())
            self.assertFalse(stale_json.exists())
            self.assertFalse(stale_json.with_suffix(".json.hash").exists())
            self.assertFalse(stale_json.with_suffix(".json.trace").exists())

    def test_rejects_empty_input(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaisesRegex(ValueError, "no literate JSON"):
                write_module_map(root, root / "module-map", Path("."))


if __name__ == "__main__":
    unittest.main()
