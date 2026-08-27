"""Tests for assembling the deployable CLRS-Lean literate site."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_PATH = Path(__file__).with_name("prepare_literate_site.py")


def load_preparer():
    spec = importlib.util.spec_from_file_location("prepare_literate_site", SCRIPT_PATH)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def write_module(site_root: Path, module_name: str, html: str) -> Path:
    path = site_root.joinpath(*module_name.split("."), "index.html")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(html, encoding="utf-8")
    return path


class PrepareLiterateSiteTests(unittest.TestCase):
    def test_mobile_stylesheet_keeps_only_the_root_breadcrumb(self) -> None:
        stylesheet = (
            SCRIPT_PATH.parents[1] / "docs" / "literate" / "clrs-literate.css"
        ).read_text(encoding="utf-8")

        self.assertIn(".breadcrumbs li:not(:first-child)", stylesheet)
        self.assertNotIn(
            ".breadcrumbs li:last-child:not(:first-child)", stylesheet
        )
        self.assertIn(".breadcrumbs li:not(:last-child)::after", stylesheet)

    def test_mobile_stylesheet_reflows_only_the_progress_matrix(self) -> None:
        stylesheet = (
            SCRIPT_PATH.parents[1] / "docs" / "literate" / "clrs-literate.css"
        ).read_text(encoding="utf-8")

        self.assertIn("table.clrs-progress-matrix", stylesheet)
        self.assertIn("table-layout: fixed", stylesheet)
        self.assertIn(".clrs-progress-matrix thead", stylesheet)
        self.assertIn(".clrs-progress-matrix tbody", stylesheet)
        self.assertIn(".clrs-progress-matrix tr", stylesheet)
        self.assertIn(".clrs-progress-matrix td", stylesheet)
        self.assertIn(".clrs-progress-matrix td::before", stylesheet)
        self.assertIn("content: attr(data-label)", stylesheet)

    def test_rejects_a_destination_that_contains_the_source(self) -> None:
        self.assertTrue(SCRIPT_PATH.is_file())
        preparer = load_preparer()

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            destination = root / "site"
            source = destination / "raw"
            source.mkdir(parents=True)
            stylesheet = root / "clrs-literate.css"
            stylesheet.write_text("body {}\n", encoding="utf-8")

            caught: Exception | None = None
            try:
                preparer.prepare_site(
                    source,
                    destination,
                    stylesheet=stylesheet,
                )
            except Exception as error:  # The assertions below check the contract.
                caught = error

            self.assertTrue(source.is_dir())
            self.assertIsInstance(caught, ValueError)
            self.assertIn("must not overlap", str(caught))

    def test_builds_the_same_optimized_site_used_for_pages(self) -> None:
        self.assertTrue(
            SCRIPT_PATH.is_file(),
            "prepare_literate_site.py must provide the shared assembly workflow",
        )
        preparer = load_preparer()

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "verso-output"
            destination = root / "site"
            stylesheet = root / "clrs-literate.css"
            stylesheet.write_text("body { color: black; }\n", encoding="utf-8")

            parent = "CLRSLean.FourthEdition.Chapter_09"
            child = "CLRSLean.FourthEdition.Chapter_09.Randomized_Select"
            child_href = child.replace(".", "/") + "/"
            write_module(
                source,
                parent,
                f"""<!doctype html>
<html><head><title>9.3</title></head><body>
<nav class="module-tree">
  <div class="leaf"><a href="CLRSLean/FourthEdition/Chapter_09/" title="{parent}">Chapter 9</a></div>
</nav>
<main><a href="{child_href}">Shared support page</a></main>
</body></html>
""",
            )
            write_module(
                source,
                child,
                "<html><head><title>Randomized select</title></head>"
                "<body>Expected time</body></html>\n",
            )
            destination.mkdir()
            (destination / "stale.html").write_text("stale", encoding="utf-8")

            result = preparer.prepare_site(
                source,
                destination,
                stylesheet=stylesheet,
                base_url="https://example.test/CLRS-Lean/",
                lastmod="2026-07-15",
            )

            parent_html = destination.joinpath(
                *parent.split("."), "index.html"
            ).read_text(encoding="utf-8")
            child_html = destination.joinpath(
                *child.split("."), "index.html"
            ).read_text(encoding="utf-8")
            sitemap = (destination / "sitemap.xml").read_text(encoding="utf-8")
            robots_path = destination / "robots.txt"
            self.assertTrue(robots_path.is_file())
            robots = robots_path.read_text(encoding="utf-8")
            stale_exists = (destination / "stale.html").exists()
            stylesheet_text = (destination / "clrs-literate.css").read_text(
                encoding="utf-8"
            )

        self.assertEqual(2, result.html_pages)
        self.assertEqual(2, result.sitemap_urls)
        self.assertFalse(stale_exists)
        self.assertEqual("body { color: black; }\n", stylesheet_text)
        self.assertNotIn(f'title="{child}"', parent_html)
        self.assertIn("clrs-nav-state-script", parent_html)
        self.assertIn(
            "https://example.test/CLRS-Lean/CLRSLean/FourthEdition/Chapter_09/",
            sitemap,
        )
        self.assertIn("<lastmod>2026-07-15</lastmod>", sitemap)
        self.assertEqual(1, parent_html.count('rel="canonical"'))
        self.assertIn(
            'href="https://example.test/CLRS-Lean/CLRSLean/FourthEdition/Chapter_09/"',
            parent_html,
        )
        self.assertEqual(1, child_html.count('rel="canonical"'))
        self.assertIn(
            'href="https://example.test/CLRS-Lean/CLRSLean/FourthEdition/'
            'Chapter_09/Randomized_Select/"',
            child_html,
        )
        self.assertEqual(
            "User-agent: *\n"
            "Allow: /\n"
            "Sitemap: https://example.test/CLRS-Lean/sitemap.xml\n",
            robots,
        )


if __name__ == "__main__":
    unittest.main()
