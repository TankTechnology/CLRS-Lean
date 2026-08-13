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
  <details open><summary><a href="CLRSLean/FourthEdition/" title="CLRSLean.FourthEdition">Fourth Edition</a></summary>
    <details open><summary class="current"><a href="CLRSLean/FourthEdition/Chapter_22/" title="CLRSLean.FourthEdition.Chapter_22">Chapter 22</a></summary>
      <div class="leaf"><a href="CLRSLean/FourthEdition/Chapter_22/Helper/" title="CLRSLean.FourthEdition.Chapter_22.Helper">Helper</a></div>
    </details>
    <div class="leaf"><a href="CLRSLean/FourthEdition/Chapter_23/" title="CLRSLean.FourthEdition.Chapter_23">Chapter 23</a></div>
  </details>
  <details open><summary><a href="CLRSLean/Chapter_22/" title="CLRSLean.Chapter_22">Chapter 22</a></summary>
    <details open><summary class="current"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/" title="CLRSLean.Chapter_22.Section_22_3_DFS">22.3</a></summary>
      <div class="leaf"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/" title="CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath">White Path</a></div>
    </details>
    <div class="leaf"><a href="CLRSLean/Chapter_22/Section_22_4_Topological_Sort/" title="CLRSLean.Chapter_22.Section_22_4_Topological_Sort">22.4</a></div>
  </details>
</nav>"""


class ReaderSidebarModuleTests(unittest.TestCase):
    def test_keeps_root_fourth_edition_tree_and_support_pages(self) -> None:
        self.assertTrue(is_reader_sidebar_module("CLRSLean"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.FourthEdition"))
        self.assertTrue(
            is_reader_sidebar_module("CLRSLean.FourthEdition.Chapter_22")
        )
        self.assertTrue(is_reader_sidebar_module("CLRSLean.OnlineMaterial"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.ProofPatterns"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.Progress"))

    def test_keeps_fourth_edition_sections(self) -> None:
        self.assertTrue(
            is_reader_sidebar_module(
                "CLRSLean.FourthEdition.Chapter_31.Section_31_1_Elementary_Number_Theory"
            )
        )
        self.assertTrue(
            is_reader_sidebar_module(
                "CLRSLean.FourthEdition.Chapter_30.Section_30_2_DFT_And_FFT"
            )
        )

    def test_hides_legacy_chapter_tree_and_deep_helpers(self) -> None:
        hidden = [
            "CLRSLean.Chapter_22",
            "CLRSLean.Chapter_22.Section_22_3_DFS",
            "CLRSLean.ProofPatterns.Boundary",
            "CLRSLean.Probability.FiniteExpectation",
            "CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath",
            "CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.S3_ExecutablePrim",
            "CLRSLean.FourthEdition.Chapter_22.Helper",
            "CLRSLean.FourthEdition.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT",
        ]
        self.assertTrue(all(not is_reader_sidebar_module(name) for name in hidden))

    def test_rejects_unrelated_or_malformed_names(self) -> None:
        self.assertFalse(is_reader_sidebar_module("Other.Root"))
        self.assertFalse(is_reader_sidebar_module("CLRSLean.Chapter_22.Helper"))
        self.assertFalse(is_reader_sidebar_module("CLRSLean.NotAReaderPage"))


class ReaderSidebarRewriteTests(unittest.TestCase):
    def test_removes_hidden_modules_and_flattens_empty_details(self) -> None:
        result = prune_reader_sidebar(MODULE_TREE)

        self.assertEqual(
            result.removed_modules,
            (
                "CLRSLean.ProofPatterns.Boundary",
                "CLRSLean.FourthEdition.Chapter_22.Helper",
                "CLRSLean.Chapter_22",
            ),
        )
        self.assertEqual(
            result.flattened_modules,
            (
                "CLRSLean.ProofPatterns",
                "CLRSLean.FourthEdition.Chapter_22",
            ),
        )
        self.assertNotIn("Boundary", result.html)
        self.assertNotIn("Helper", result.html)
        self.assertNotIn("White Path", result.html)
        self.assertIn(
            '<div class="leaf"><a href="CLRSLean/ProofPatterns/"', result.html
        )
        self.assertIn(
            '<div class="leaf current"><a href="CLRSLean/FourthEdition/Chapter_22/"',
            result.html,
        )
        self.assertIn(
            '<details open><summary><a href="CLRSLean/FourthEdition/"', result.html
        )
        self.assertLess(
            result.html.index(">Chapter 22</a>"),
            result.html.index(">Chapter 23</a>"),
        )

    def test_keeps_fourth_edition_section_rows_and_prunes_helpers(self) -> None:
        source = """<nav class="module-tree">
  <details open><summary><a href="CLRSLean/FourthEdition/Chapter_31/" title="CLRSLean.FourthEdition.Chapter_31">Chapter 31</a></summary>
    <details open><summary><a href="CLRSLean/FourthEdition/Chapter_31/Section_31_2_Greatest_Common_Divisor/" title="CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor">31.2</a></summary>
      <div class="leaf"><a href="CLRSLean/FourthEdition/Chapter_31/Section_31_2_Greatest_Common_Divisor/Helper/" title="CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor.Helper">Helper</a></div>
    </details>
    <div class="leaf"><a href="CLRSLean/FourthEdition/Chapter_31/Section_31_1_Elementary_Number_Theory/" title="CLRSLean.FourthEdition.Chapter_31.Section_31_1_Elementary_Number_Theory">31.1</a></div>
  </details>
</nav>"""

        result = prune_reader_sidebar(source)

        self.assertEqual(
            result.removed_modules,
            (
                "CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor.Helper",
            ),
        )
        self.assertEqual(
            result.flattened_modules,
            (
                "CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor",
            ),
        )
        self.assertNotIn("Helper", result.html)
        self.assertIn(
            'title="CLRSLean.FourthEdition.Chapter_31.Section_31_1_Elementary_Number_Theory"',
            result.html,
        )
        self.assertIn(
            'title="CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor"',
            result.html,
        )

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

    def test_routes_hidden_current_module_to_canonical_reader_page(self) -> None:
        source = """<nav class="module-tree">
  <details open><summary><a href="CLRSLean/FourthEdition/" title="CLRSLean.FourthEdition">Fourth Edition</a></summary>
    <div class="leaf"><a href="CLRSLean/FourthEdition/Chapter_20/" title="CLRSLean.FourthEdition.Chapter_20">Chapter 20</a></div>
  </details>
  <details open><summary><a href="CLRSLean/Chapter_22/" title="CLRSLean.Chapter_22">Chapter 22</a></summary>
    <div class="leaf current"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/" title="CLRSLean.Chapter_22.Section_22_3_DFS">22.3</a></div>
  </details>
</nav>"""

        result = prune_reader_sidebar(
            source,
            {"CLRSLean.Chapter_22": "CLRSLean.FourthEdition.Chapter_20"},
        )

        self.assertNotIn('title="CLRSLean.Chapter_22"', result.html)
        self.assertIn(
            '<div class="leaf current"><a href="CLRSLean/FourthEdition/Chapter_20/"',
            result.html,
        )


if __name__ == "__main__":
    unittest.main()
