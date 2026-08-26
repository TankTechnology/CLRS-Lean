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
    def test_converts_marked_progress_matrix_to_semantic_table_once(self) -> None:
        self.assertTrue(
            hasattr(optimizer, "replace_progress_matrix"),
            "optimizer must expose the Progress matrix transform",
        )
        source = (
            '<section><h2 id="Chapter-Matrix">Chapter Matrix</h2>'
            "<pre>CLRS-PROGRESS-MATRIX\n"
            "Ch\tChapter\tStatus\tSections\tTracked\tGap units\n"
            "34\t34. NP-Completeness\tmain-proof-complete\t34.1;34.2\t49\t0"
            "</pre></section>"
        )

        first, first_changes = optimizer.replace_progress_matrix(source)
        second, second_changes = optimizer.replace_progress_matrix(first)

        self.assertEqual(1, first_changes)
        self.assertEqual(0, second_changes)
        self.assertEqual(first, second)
        self.assertIn('<table class="clrs-progress-matrix">', first)
        self.assertIn('<th scope="col">Chapter</th>', first)
        self.assertIn('<td data-label="Status">main-proof-complete</td>', first)
        self.assertNotIn("CLRS-PROGRESS-MATRIX", first)

    def test_canonical_link_injection_replaces_stale_link_idempotently(self) -> None:
        self.assertTrue(
            hasattr(optimizer, "inject_canonical_link"),
            "optimizer must expose canonical-link normalization",
        )
        source = (
            '<html><head><link rel="canonical" href="https://old.example/page">'
            "<title>CLRS-Lean</title></head><body></body></html>"
        )
        expected_url = "https://example.test/CLRS-Lean/CLRSLean/Progress/"

        first, first_changes = optimizer.inject_canonical_link(source, expected_url)
        second, second_changes = optimizer.inject_canonical_link(first, expected_url)

        self.assertEqual(1, first_changes)
        self.assertEqual(0, second_changes)
        self.assertEqual(first, second)
        self.assertEqual(1, first.count('rel="canonical"'))
        self.assertIn(f'href="{expected_url}"', first)
        self.assertNotIn("old.example", first)

    def test_injects_google_site_verification_meta_once(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "index.html"
            page.write_text(
                """<!doctype html>
<html>
  <head><title>CLRS-Lean</title></head>
  <body><main>CLRS-Lean</main></body>
</html>
""",
                encoding="utf-8",
            )

            first = optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            first_text = page.read_text(encoding="utf-8")
            second = optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            second_text = page.read_text(encoding="utf-8")

        self.assertTrue(first.changed)
        self.assertEqual(first.injected_verification_meta, 1)
        self.assertFalse(second.changed)
        self.assertEqual(second.injected_verification_meta, 0)
        self.assertEqual(first_text, second_text)
        self.assertEqual(first_text.count("google-site-verification"), 1)
        self.assertIn(
            '<meta name="google-site-verification" '
            'content="_r82oikN7_rmuMq-yxTixWGiNVPoxC-OJcNLDlO1Atk" />',
            first_text,
        )
        self.assertLess(
            first_text.index("google-site-verification"),
            first_text.index("</head>"),
        )

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
        self.assertIn("localStorage", text)
        self.assertIn("sessionStorage", text)
        self.assertIn("details.open = true", text)
        self.assertIn("clrs.nav.state.v7", text)
        self.assertIn("clrs.nav.scroll.v7", text)
        self.assertNotIn("clrs.nav.state.v6", text)
        self.assertNotIn("clrs.nav.scroll.v6", text)
        self.assertIn("stableNavPath", text)
        self.assertIn("new URL(raw, document.baseURI)", text)
        self.assertIn("CLRS-Lean", text)
        self.assertIn('replace(/^.*\\/CLRSLean\\//, "/CLRS-Lean/")', text)
        self.assertIn("window.location.href", text)
        self.assertIn("bestParent", text)
        self.assertIn("saveStateNow();", text)
        self.assertIn('window.addEventListener("pagehide"', text)

    def test_nav_script_keeps_summary_link_clicks_from_toggling(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "index.html"
            page.write_text(
                """<!doctype html>
<html>
  <body>
    <nav class="module-tree">
      <details><summary><a href="CLRSLean/Chapter_16/" title="CLRSLean.Chapter_16">Chapter 16</a></summary></details>
    </nav>
  </body>
</html>
""",
                encoding="utf-8",
            )

            optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            text = page.read_text(encoding="utf-8")

        self.assertIn('nav.querySelectorAll("summary a")', text)
        self.assertIn("event.stopPropagation()", text)

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
        self.assertEqual(second.removed_nav_modules, 0)
        self.assertEqual(second.flattened_nav_details, 0)
        self.assertEqual(first_text, second_text)
        self.assertEqual(second_text.count("clrs-nav-state-script"), 1)

    def test_nav_state_script_replaces_stale_version(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "index.html"
            page.write_text(
                """<!doctype html>
<html>
  <body>
    <nav class="module-tree">
      <details><summary><a href="CLRSLean/Chapter_02/">Chapter 2</a></summary></details>
    </nav>
    <script id="clrs-nav-state-script">const oldKey = "clrs.nav.state.v4";</script>
  </body>
</html>
""",
                encoding="utf-8",
            )

            stats = optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            text = page.read_text(encoding="utf-8")

        self.assertTrue(stats.changed)
        self.assertEqual(text.count("clrs-nav-state-script"), 1)
        self.assertIn("clrs.nav.state.v7", text)
        self.assertNotIn("clrs.nav.state.v4", text)

    def test_prunes_hidden_sidebar_modules_and_flattens_parent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "index.html"
            page.write_text(
                """<!doctype html>
<html>
  <body>
    <nav class="module-tree">
      <details open><summary class="current"><a href="CLRSLean/FourthEdition/Chapter_20/" title="CLRSLean.FourthEdition.Chapter_20">Chapter 20</a></summary>
        <div class="leaf"><a href="CLRSLean/FourthEdition/Chapter_20/Helper/" title="CLRSLean.FourthEdition.Chapter_20.Helper">Helper</a></div>
      </details>
    </nav>
  </body>
</html>
""",
                encoding="utf-8",
            )

            stats = optimizer.optimize_file(page, strip_attrs_min_bytes=1_000_000)
            text = page.read_text(encoding="utf-8")

        self.assertNotIn("Chapter_20.Helper", text)
        self.assertIn('title="CLRSLean.FourthEdition.Chapter_20"', text)
        self.assertIn('<div class="leaf current">', text)
        self.assertEqual(stats.removed_nav_modules, 1)
        self.assertEqual(stats.flattened_nav_details, 1)


if __name__ == "__main__":
    unittest.main()
