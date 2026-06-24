#!/usr/bin/env python3
"""Tests for the CLRS-Lean generated HTML optimizer."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_PATH = Path(__file__).with_name("optimize_literate_html.py")
SPEC = importlib.util.spec_from_file_location("optimize_literate_html", SCRIPT_PATH)
assert SPEC is not None
optimizer = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = optimizer
SPEC.loader.exec_module(optimizer)


class OptimizeLiterateHtmlTests(unittest.TestCase):
    def test_injects_persistent_module_tree_state_script(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "index.html"
            page.write_text(
                """<!doctype html>
<html>
  <head><title>CLRS-Lean</title></head>
  <body>
    <aside class="sidebar">
      <nav class="module-tree">
        <details><summary><a href="CLRSLean/Chapter_02/">Chapter 2</a></summary>
          <div class="leaf"><a href="CLRSLean/Chapter_02/Section_02_1/">2.1</a></div>
        </details>
      </nav>
    </aside>
  </body>
</html>
""",
                encoding="utf-8",
            )

            stats = optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            text = page.read_text(encoding="utf-8")

        self.assertTrue(stats.changed)
        self.assertIn("<details open>", text)
        self.assertIn("id=\"clrs-nav-state-script\"", text)
        self.assertIn("sessionStorage", text)
        self.assertIn("details.open = true", text)
        self.assertIn("clrs.nav.state", text)

    def test_nav_state_injection_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "index.html"
            page.write_text(
                """<!doctype html>
<html>
  <body>
    <nav class="module-tree">
      <details><summary><a href="CLRSLean/Chapter_02/">Chapter 2</a></summary></details>
    </nav>
  </body>
</html>
""",
                encoding="utf-8",
            )

            first = optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            first_text = page.read_text(encoding="utf-8")
            second = optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            second_text = page.read_text(encoding="utf-8")

        self.assertTrue(first.changed)
        self.assertFalse(second.changed)
        self.assertEqual(first_text, second_text)
        self.assertEqual(second_text.count("clrs-nav-state-script"), 1)


if __name__ == "__main__":
    unittest.main()
