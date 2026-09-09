"""Tests for composing direct section pages into fourth-edition chapters."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_PATH = Path(__file__).with_name("inline_chapter_sections.py")


def load_composer():
    spec = importlib.util.spec_from_file_location("inline_chapter_sections", SCRIPT_PATH)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def write_module(site: Path, module: str, body: str) -> Path:
    path = site.joinpath(*module.split("."), "index.html")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return path


class InlineChapterSectionsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.composer = load_composer()
        self.parent = "CLRSLean.FourthEdition.Chapter_33"
        self.first = f"{self.parent}.Section_33_1_Clustering"
        self.second = f"{self.parent}.Section_33_2_Multiplicative_Weights"

    def test_embeds_direct_sections_in_configured_order_and_rewrites_links(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            first_href = self.first.replace(".", "/") + "/"
            second_href = self.second.replace(".", "/") + "/"
            parent_href = self.parent.replace(".", "/") + "/"
            parent_path = write_module(
                site,
                self.parent,
                f"""<html><body><main class="main-area">
<section class="code-content"><h1>Chapter 33</h1>
<a href="{first_href}">Clustering section</a>
<a href="{second_href}#regret">Weights theorem</a></section>
</main></body></html>""",
            )
            first_path = write_module(
                site,
                self.first,
                f"""<html><body><main><section class="code-content" id="first-module">
<section><h1 id="clustering">33.1 Clustering</h1>
<a href="{first_href}#mean">Mean theorem</a>
<a href="{first_href}#first-module">Module top</a>
<a href="{first_href}#external-target">External target</a>
<div id="mean">First body</div>
</section></section></main></body></html>""",
            )
            write_module(
                site,
                self.second,
                """<html><body><main><section class="code-content" id="second-module">
<section><h1 id="weights">33.2 Multiplicative Weights</h1>
<div id="regret">Second body</div></section>
</section></main></body></html>""",
            )
            first_before = first_path.read_text(encoding="utf-8")

            result = self.composer.compose_chapter_pages(
                site, {self.parent: [self.second, self.first]}
            )
            parent_html = parent_path.read_text(encoding="utf-8")

            self.assertEqual(1, result.chapters)
            self.assertEqual(2, result.sections)
            self.assertLess(parent_html.index("Second body"), parent_html.index("First body"))
            self.assertIn('data-clrs-inline-chapter="true"', parent_html)
            self.assertLess(
                parent_html.index('data-clrs-inline-chapter="true"'),
                parent_html.index("</section>"),
            )
            self.assertIn(
                f'href="{parent_href}#{self.composer.section_anchor(self.first)}"',
                parent_html,
            )
            second_anchor = self.composer.section_anchor(self.second)
            first_anchor = self.composer.section_anchor(self.first)
            self.assertIn(
                f'href="{parent_href}#{second_anchor}--regret"', parent_html
            )
            self.assertIn(f'id="{second_anchor}--regret"', parent_html)
            self.assertIn(f'href="{parent_href}#{first_anchor}--mean"', parent_html)
            self.assertIn(f'id="{first_anchor}--mean"', parent_html)
            self.assertIn(f'href="{parent_href}#{first_anchor}"', parent_html)
            self.assertIn(
                f'href="{first_href}#external-target"', parent_html
            )
            self.assertNotIn('id="mean"', parent_html)
            self.assertNotIn('id="regret"', parent_html)
            self.assertEqual(first_before, first_path.read_text(encoding="utf-8"))

    def test_namespaces_duplicate_ids_from_different_sections(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            parent_path = write_module(
                site,
                self.parent,
                '<html><body><main><section class="code-content">Guide</section>'
                "</main></body></html>",
            )
            for module, label in ((self.first, "First"), (self.second, "Second")):
                write_module(
                    site,
                    module,
                    '<html><body><main><section class="code-content">'
                    f'<h2 id="Implementation-details">{label}</h2>'
                    '<a href="#Implementation-details">Details</a>'
                    "</section></main></body></html>",
                )

            self.composer.compose_chapter_pages(
                site, {self.parent: [self.first, self.second]}
            )
            parent_html = parent_path.read_text(encoding="utf-8")

            for module in (self.first, self.second):
                target = (
                    f"{self.composer.section_anchor(module)}--Implementation-details"
                )
                self.assertIn(f'id="{target}"', parent_html)
                parent_href = self.parent.replace(".", "/") + "/"
                self.assertIn(f'href="{parent_href}#{target}"', parent_html)
            self.assertNotIn('id="Implementation-details"', parent_html)

    def test_composition_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            parent_path = write_module(
                site,
                self.parent,
                '<html><body><main><section class="code-content">Guide</section>'
                "</main></body></html>",
            )
            write_module(
                site,
                self.first,
                '<html><body><main><section class="code-content">Section body</section>'
                "</main></body></html>",
            )

            first = self.composer.compose_chapter_pages(
                site, {self.parent: [self.first]}
            )
            first_html = parent_path.read_text(encoding="utf-8")
            second = self.composer.compose_chapter_pages(
                site, {self.parent: [self.first]}
            )

            self.assertEqual((1, 1), (first.chapters, first.sections))
            self.assertEqual((0, 0), (second.chapters, second.sections))
            self.assertEqual(first_html, parent_path.read_text(encoding="utf-8"))

    def test_missing_configured_section_page_is_an_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            write_module(
                site,
                self.parent,
                '<html><body><main><section class="code-content">Guide</section>'
                "</main></body></html>",
            )

            with self.assertRaisesRegex(ValueError, "section page is missing"):
                self.composer.compose_chapter_pages(
                    site, {self.parent: [self.first]}
                )

    def test_ignores_non_section_children(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            site = Path(tmp)
            parent_path = write_module(
                site,
                self.parent,
                '<html><body><main><section class="code-content">Guide</section>'
                "</main></body></html>",
            )

            result = self.composer.compose_chapter_pages(
                site, {self.parent: [f"{self.parent}.Helper"]}
            )

            self.assertEqual((0, 0), (result.chapters, result.sections))
            self.assertNotIn(
                "data-clrs-inline-chapter", parent_path.read_text(encoding="utf-8")
            )


if __name__ == "__main__":
    unittest.main()
