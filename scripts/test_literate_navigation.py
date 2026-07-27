import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.literate_navigation import is_reader_sidebar_module, prune_reader_sidebar


MODULE_TREE = """<nav class="module-tree">
  <details open><summary><a href="CLRSLean/ProofPatterns/" title="CLRSLean.ProofPatterns">Patterns</a></summary>
    <div class="leaf"><a href="CLRSLean/ProofPatterns/Boundary/" title="CLRSLean.ProofPatterns.Boundary">Boundary</a></div>
  </details>
  <details open><summary><a href="CLRSLean/Chapter_22/" title="CLRSLean.Chapter_22">Chapter 22</a></summary>
    <details open><summary class="current"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/" title="CLRSLean.Chapter_22.Section_22_3_DFS">22.3</a></summary>
      <div class="leaf"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/" title="CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath">White Path</a></div>
    </details>
    <div class="leaf"><a href="CLRSLean/Chapter_22/Section_22_4_Topological_Sort/" title="CLRSLean.Chapter_22.Section_22_4_Topological_Sort">22.4</a></div>
  </details>
</nav>"""


class ReaderSidebarModuleTests(unittest.TestCase):
    def test_keeps_root_and_top_level_pages(self) -> None:
        self.assertTrue(is_reader_sidebar_module("CLRSLean"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.ProofPatterns"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.Chapter_22"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.Progress"))

    def test_keeps_direct_chapter_sections(self) -> None:
        self.assertTrue(
            is_reader_sidebar_module("CLRSLean.Chapter_22.Section_22_3_DFS")
        )

    def test_hides_nonchapter_children_and_section_descendants(self) -> None:
        hidden = [
            "CLRSLean.ProofPatterns.Boundary",
            "CLRSLean.Probability.FiniteExpectation",
            "CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath",
            "CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.S3_ExecutablePrim",
        ]
        self.assertTrue(all(not is_reader_sidebar_module(name) for name in hidden))

    def test_rejects_unrelated_or_malformed_names(self) -> None:
        self.assertFalse(is_reader_sidebar_module("Other.Root"))
        self.assertFalse(is_reader_sidebar_module("CLRSLean.Chapter_22.Helper"))


class ReaderSidebarRewriteTests(unittest.TestCase):
    def test_removes_hidden_modules_and_flattens_empty_details(self) -> None:
        result = prune_reader_sidebar(MODULE_TREE)

        self.assertEqual(
            result.removed_modules,
            (
                "CLRSLean.ProofPatterns.Boundary",
                "CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath",
            ),
        )
        self.assertEqual(
            result.flattened_modules,
            (
                "CLRSLean.ProofPatterns",
                "CLRSLean.Chapter_22.Section_22_3_DFS",
            ),
        )
        self.assertNotIn("Boundary", result.html)
        self.assertNotIn("White Path", result.html)
        self.assertIn(
            '<div class="leaf"><a href="CLRSLean/ProofPatterns/"', result.html
        )
        self.assertIn(
            '<div class="leaf current"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/"',
            result.html,
        )
        self.assertIn(
            '<details open><summary><a href="CLRSLean/Chapter_22/"', result.html
        )
        self.assertLess(result.html.index(">22.3</a>"), result.html.index(">22.4</a>"))

    def test_rewrite_is_idempotent(self) -> None:
        first = prune_reader_sidebar(MODULE_TREE)
        second = prune_reader_sidebar(first.html)

        self.assertEqual(second.html, first.html)
        self.assertEqual(second.removed_modules, ())
        self.assertEqual(second.flattened_modules, ())

    def test_keeps_and_reports_unclassified_links(self) -> None:
        source = """<nav class="module-tree">
  <div class="leaf"><a href="mystery/">Mystery</a></div>
</nav>"""

        result = prune_reader_sidebar(source)

        self.assertEqual(result.html, source)
        self.assertEqual(result.unclassified_hrefs, ("mystery/",))


if __name__ == "__main__":
    unittest.main()
