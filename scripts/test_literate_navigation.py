import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.literate_navigation import is_reader_sidebar_module


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


if __name__ == "__main__":
    unittest.main()
