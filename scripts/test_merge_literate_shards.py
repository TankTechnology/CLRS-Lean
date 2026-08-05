#!/usr/bin/env python3
"""Regression tests for validating and atomically merging Verso shards."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from merge_literate_shards import merge_shards


def write_manifest(root: Path, modules: list[list[str]], digest: str = "digest") -> Path:
    manifest = {
        "schema_version": 1,
        "input_digest": digest,
        "shard_count": len(modules),
        "module_count": sum(map(len, modules)),
        "shards": [
            {"index": index, "modules": names, "module_file": f"shard-{index}.txt"}
            for index, names in enumerate(modules)
        ],
    }
    path = root / "manifest.json"
    path.write_text(json.dumps(manifest), encoding="utf-8")
    return path


def write_shard(
    root: Path,
    index: int,
    modules: list[str],
    *,
    digest: str = "digest",
    shared: str = "same",
    docs: dict[str, object] | None = None,
) -> Path:
    shard = root / f"shard-{index}"
    html = shard / "html"
    html.mkdir(parents=True)
    for module in modules:
        page = html.joinpath(*module.split("."), "index.html")
        page.parent.mkdir(parents=True)
        page.write_text(module, encoding="utf-8")
    (html / "shared.css").write_text(shared, encoding="utf-8")
    metadata = shard / "verso-docs.json"
    metadata.write_text(json.dumps(docs or {f"doc-{index}": index}), encoding="utf-8")
    (shard / "shard-record.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "shard_index": index,
                "input_digest": digest,
                "modules": modules,
                "output_dir": "html",
                "metadata_path": "verso-docs.json",
            }
        ),
        encoding="utf-8",
    )
    return shard


class LiterateShardMergeTests(unittest.TestCase):
    def test_merges_matching_shards_deterministically(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = write_manifest(root, [["CLRSLean.A"], ["CLRSLean.B"]])
            shards = [
                write_shard(root, 1, ["CLRSLean.B"]),
                write_shard(root, 0, ["CLRSLean.A"]),
            ]
            output = root / "merged"

            errors = merge_shards(manifest, shards, output)

            self.assertEqual([], errors)
            self.assertEqual("CLRSLean.A", (output / "CLRSLean/A/index.html").read_text())
            self.assertEqual("CLRSLean.B", (output / "CLRSLean/B/index.html").read_text())
            self.assertEqual(
                {"doc-0": 0, "doc-1": 1},
                json.loads((output / "-verso-docs.json").read_text()),
            )

    def test_rejects_digest_mismatch_without_touching_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = write_manifest(root, [["CLRSLean.A"]])
            shard = write_shard(root, 0, ["CLRSLean.A"], digest="wrong")
            output = root / "merged"
            output.mkdir()
            sentinel = output / "keep"
            sentinel.write_text("untouched")

            errors = merge_shards(manifest, [shard], output)

            self.assertTrue(any("digest" in error for error in errors))
            self.assertEqual("untouched", sentinel.read_text())

    def test_reports_duplicate_missing_and_unexpected_modules(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = write_manifest(root, [["CLRSLean.A"], ["CLRSLean.B"]])
            shards = [
                write_shard(root, 0, ["CLRSLean.A", "CLRSLean.X"]),
                write_shard(root, 1, ["CLRSLean.A"]),
            ]

            errors = merge_shards(manifest, shards, root / "merged")

            rendered = "\n".join(errors)
            self.assertIn("duplicate module: CLRSLean.A", rendered)
            self.assertIn("missing module: CLRSLean.B", rendered)
            self.assertIn("unexpected module: CLRSLean.X", rendered)

    def test_rejects_unequal_file_and_metadata_collisions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = write_manifest(root, [["CLRSLean.A"], ["CLRSLean.B"]])
            shards = [
                write_shard(root, 0, ["CLRSLean.A"], shared="first", docs={"same": 1}),
                write_shard(root, 1, ["CLRSLean.B"], shared="second", docs={"same": 2}),
            ]

            errors = merge_shards(manifest, shards, root / "merged")

            rendered = "\n".join(errors)
            self.assertIn("unequal output collision: shared.css", rendered)
            self.assertIn("unequal metadata key collision: same", rendered)

    def test_rejects_missing_rendered_module_page(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = write_manifest(root, [["CLRSLean.A"]])
            shard = write_shard(root, 0, ["CLRSLean.A"])
            (shard / "html/CLRSLean/A/index.html").unlink()
            output = root / "merged"
            output.mkdir()
            sentinel = output / "keep"
            sentinel.write_text("untouched", encoding="utf-8")

            errors = merge_shards(manifest, [shard], output)

            self.assertIn(
                "shard 0: missing rendered module page: CLRSLean/A/index.html",
                errors,
            )
            self.assertEqual("untouched", sentinel.read_text(encoding="utf-8"))

    def test_rejects_unexpected_module_page_but_allows_shared_pages_and_assets(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            manifest = write_manifest(root, [["CLRSLean.A"]])
            shard = write_shard(root, 0, ["CLRSLean.A"])
            html = shard / "html"
            unexpected = html / "CLRSLean/X/index.html"
            unexpected.parent.mkdir(parents=True)
            unexpected.write_text("unexpected", encoding="utf-8")
            (html / "index.html").write_text("landing", encoding="utf-8")
            search = html / "search/index.html"
            search.parent.mkdir(parents=True)
            search.write_text("search", encoding="utf-8")
            (html / "xref.json").write_text("{}", encoding="utf-8")

            errors = merge_shards(manifest, [shard], root / "merged")

            self.assertEqual(
                ["shard 0: unexpected rendered module page: CLRSLean/X/index.html"],
                errors,
            )


if __name__ == "__main__":
    unittest.main()
