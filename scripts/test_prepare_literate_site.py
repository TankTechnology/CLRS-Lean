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

            parent = "CLRSLean.Chapter_09.Section_09_3_Deterministic_Select"
            child = f"{parent}.Randomized_Select"
            child_href = child.replace(".", "/") + "/"
            write_module(
                source,
                parent,
                f"""<!doctype html>
<html><head><title>9.3</title></head><body>
<nav class="module-tree">
  <details><summary><a href="CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/" title="{parent}">9.3</a></summary>
    <div class="leaf"><a href="{child_href}" title="{child}">Randomized SELECT</a></div>
  </details>
</nav>
<main><a href="{child_href}">Shared support page</a></main>
</body></html>
""",
            )
            write_module(source, child, "<html><body>Expected time</body></html>\n")
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
            sitemap = (destination / "sitemap.xml").read_text(encoding="utf-8")
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
            "https://example.test/CLRS-Lean/CLRSLean/Chapter_09/"
            "Section_09_3_Deterministic_Select/",
            sitemap,
        )
        self.assertIn("<lastmod>2026-07-15</lastmod>", sitemap)


if __name__ == "__main__":
    unittest.main()
