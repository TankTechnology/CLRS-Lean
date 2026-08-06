#!/usr/bin/env python3
"""Tests for the raw Verso HTML weight and proof-state guard."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_literate_html_weight.py"
READ_CHUNK_BYTES = 64 * 1024


def write_page(site: Path, relative: str, html: str) -> Path:
    page = site / relative / "index.html"
    page.parent.mkdir(parents=True, exist_ok=True)
    page.write_text(html, encoding="utf-8")
    return page


def run_script(
    site: Path, *, max_page_bytes: int | None = None
) -> subprocess.CompletedProcess[str]:
    command = [sys.executable, str(SCRIPT), str(site)]
    if max_page_bytes is not None:
        command.extend(["--max-page-bytes", str(max_page_bytes)])
    return subprocess.run(
        command,
        text=True,
        capture_output=True,
        check=False,
    )


class CheckLiterateHtmlWeightTests(unittest.TestCase):
    def test_accepts_bounded_page_without_tactic_markup(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_page(site, "CLRSLean/Chapter_01", "<main><code>theorem ok</code></main>")
            result = run_script(site)

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIn("checked 1 raw HTML pages", result.stdout)

    def test_reports_inline_tactic_state(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_page(
                site,
                "CLRSLean/Chapter_22",
                '<span class="other tactic-state">goal</span>',
            )
            result = run_script(site)

        self.assertEqual(1, result.returncode)
        self.assertIn("inline tactic-state markup", result.stderr)

    def test_reports_inline_tactic_toggle(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_page(
                site,
                "CLRSLean/Chapter_22",
                '<input class="tactic-toggle" type="checkbox">',
            )
            result = run_script(site)

        self.assertEqual(1, result.returncode)
        self.assertIn("inline tactic-toggle markup", result.stderr)

    def test_reports_page_above_explicit_limit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_page(site, "large", "x" * 101)
            result = run_script(site, max_page_bytes=100)

        self.assertEqual(1, result.returncode)
        self.assertIn("exceeds 100 bytes", result.stderr)

    def test_detects_tactic_tag_across_read_boundary(self) -> None:
        tag = '<span class="other tactic-state">goal</span>'
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_page(site, "boundary", "x" * (READ_CHUNK_BYTES - 10) + tag)
            result = run_script(site)

        self.assertEqual(1, result.returncode)
        self.assertIn("inline tactic-state markup", result.stderr)

    def test_reports_pages_in_deterministic_path_order(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_page(site, "z", '<span class="tactic-state">goal</span>')
            write_page(site, "a", '<input class="tactic-toggle">')
            result = run_script(site)

        self.assertEqual(1, result.returncode)
        self.assertLess(
            result.stderr.index("a/index.html"),
            result.stderr.index("z/index.html"),
        )

    def test_rejects_site_without_index_pages(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            result = run_script(Path(tmp))

        self.assertEqual(1, result.returncode)
        self.assertIn("no index.html pages found", result.stderr)


if __name__ == "__main__":
    unittest.main()
