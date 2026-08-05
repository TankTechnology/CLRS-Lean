#!/usr/bin/env python3
"""Tests for the provenance-recording single-shard renderer wrapper."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from render_literate_shard import HOVER_ID_STRIDE, render_shard


FAKE_RENDERER = """#!/usr/bin/env python3
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1])
args = sys.argv[4:]
emit = pathlib.Path(args[args.index('--emit-list') + 1])
metadata = pathlib.Path(args[args.index('--metadata-out') + 1])
out.mkdir(parents=True)
for module in emit.read_text().splitlines():
    page = out.joinpath(*module.split('.'), 'index.html')
    page.parent.mkdir(parents=True, exist_ok=True)
    page.write_text(module)
(out / 'renderer-args.json').write_text(json.dumps(args))
metadata.parent.mkdir(parents=True, exist_ok=True)
metadata.write_text('{}')
"""


def fixture(root: Path, index: int = 0) -> tuple[Path, Path, Path, Path]:
    executable = root / "renderer"
    executable.write_text(FAKE_RENDERER, encoding="utf-8")
    executable.chmod(0o755)
    module_map = root / "module-map"
    module_map.write_text("CLRSLean.A\ta.json\t.\n", encoding="utf-8")
    config = root / "literate.toml"
    config.write_text("", encoding="utf-8")
    plan = root / "plan"
    plan.mkdir()
    (plan / f"shard-{index}.txt").write_text("CLRSLean.A\n", encoding="utf-8")
    (plan / "manifest.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "input_digest": "digest",
                "shards": [
                    {
                        "index": index,
                        "module_file": f"shard-{index}.txt",
                        "modules": ["CLRSLean.A"],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    return executable, module_map, config, plan / "manifest.json"


class RenderLiterateShardTests(unittest.TestCase):
    def test_records_provenance_and_coordinator_role(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            executable, module_map, config, manifest = fixture(root)
            output = root / "shard-0"

            record = render_shard(executable, module_map, config, manifest, 0, output)
            args = json.loads((output / "html" / "renderer-args.json").read_text())

        self.assertEqual("digest", record["input_digest"])
        self.assertEqual(["CLRSLean.A"], record["modules"])
        self.assertIn("--coordinator", args)
        self.assertEqual("0", args[args.index("--hover-id-offset") + 1])

    def test_noncoordinator_uses_disjoint_hover_range(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            executable, module_map, config, manifest = fixture(root, index=2)
            output = root / "shard-2"

            render_shard(executable, module_map, config, manifest, 2, output)
            args = json.loads((output / "html" / "renderer-args.json").read_text())

        self.assertNotIn("--coordinator", args)
        self.assertEqual(
            str(2 * HOVER_ID_STRIDE), args[args.index("--hover-id-offset") + 1]
        )

    def test_rejects_emit_list_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            executable, module_map, config, manifest = fixture(root)
            (manifest.parent / "shard-0.txt").write_text("CLRSLean.B\n")

            with self.assertRaisesRegex(ValueError, "differs from the signed manifest"):
                render_shard(executable, module_map, config, manifest, 0, root / "out")


if __name__ == "__main__":
    unittest.main()
