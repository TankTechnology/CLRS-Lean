import re
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LITERATE_TOML = ROOT / "literate.toml"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.literate_navigation import is_reader_sidebar_module

COMPATIBILITY_MODULES = {
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap",
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts",
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts",
}

LINK_EXEMPT_MODULES = COMPATIBILITY_MODULES | {
    "CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis.OnlineHiring",
    "CLRSLean.Chapter_06.Section_06_4_Heapsort.CostedExecution",
}


def _module_source(module: str) -> Path:
    parts = module.split(".")
    if parts == ["CLRSLean"]:
        return ROOT / "CLRSLean.lean"
    return ROOT / Path(*parts[:-1]) / f"{parts[-1]}.lean"


def _parse_order_children(text: str) -> dict[str, list[str]]:
    blocks: dict[str, list[str]] = {}
    pattern = re.compile(r'^"([^"]+)"\s*=\s*\[(.*?)^\]', re.MULTILINE | re.DOTALL)
    for match in pattern.finditer(text):
        parent = match.group(1)
        children = re.findall(r'"([^"]+)"', match.group(2))
        blocks[parent] = children
    return blocks


def _parse_module_titles(text: str) -> set[str]:
    return set(re.findall(r'^\[modules\."([^"]+)"\]\s*\ntitle\s*=', text, re.MULTILINE))


def _ordered_descendants(
    order_children: dict[str, list[str]], parent: str
) -> list[str]:
    descendants: list[str] = []
    visiting: set[str] = set()

    def visit(current: str) -> None:
        if current in visiting:
            raise ValueError(f"cycle in literate navigation at {current}")
        visiting.add(current)
        for child in order_children.get(current, []):
            descendants.append(child)
            visit(child)
        visiting.remove(current)

    visit(parent)
    return descendants


class LiterateConfigTest(unittest.TestCase):
    def test_landing_page_imports_are_ordered_and_titled(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = _parse_order_children(text)
        titled_modules = _parse_module_titles(text)

        imported_modules = [
            module
            for module in re.findall(
                r"^import\s+(CLRSLean\.[^\s]+)",
                (ROOT / "CLRSLean.lean").read_text(),
                re.MULTILINE,
            )
            if module not in COMPATIBILITY_MODULES
        ]

        self.assertEqual(imported_modules, order_children["CLRSLean"])

        missing_titles = [module for module in imported_modules if module not in titled_modules]
        self.assertEqual([], missing_titles)

    def test_chapter_imported_sections_are_ordered_and_titled(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = _parse_order_children(text)
        titled_modules = _parse_module_titles(text)

        for chapter_file in sorted((ROOT / "CLRSLean").glob("Chapter_[0-9][0-9].lean")):
            chapter = chapter_file.stem
            chapter_module = f"CLRSLean.{chapter}"
            if chapter_module not in order_children:
                continue

            imported_sections = re.findall(
                rf"^import\s+(CLRSLean\.{chapter}\.Section_[^\s]+)",
                chapter_file.read_text(),
                re.MULTILINE,
            )
            if not imported_sections:
                continue

            ordered_sections = [
                module
                for module in _ordered_descendants(order_children, chapter_module)
                if module not in COMPATIBILITY_MODULES
            ]
            with self.subTest(chapter=chapter_module):
                self.assertEqual(imported_sections, ordered_sections)

            missing_titles = [module for module in imported_sections if module not in titled_modules]
            with self.subTest(chapter=f"{chapter_module} titles"):
                self.assertEqual([], missing_titles)

    def test_support_pages_are_nested(self) -> None:
        order_children = _parse_order_children(LITERATE_TOML.read_text())
        expected = {
            "CLRSLean.Chapter_08.Section_08_2_Counting_Sort": [
                "CLRSLean.Chapter_08.Section_08_2_Counting_Sort.CountTables",
                "CLRSLean.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray",
            ],
            "CLRSLean.Chapter_17.Section_17_1_Amortized_Framework": [
                "CLRSLean.Chapter_17.Section_17_1_Amortized_Framework.Section_17_2_Stack_And_Counter",
            ],
            "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model": [
                "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap",
                "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts",
                "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts",
            ],
            "CLRSLean.Chapter_19.Section_19_3_Decreasing_A_Key_And_Deleting_A_Node": [
                "CLRSLean.Chapter_19.Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.Amortized_Costs",
            ],
            "CLRSLean.Chapter_22.Section_22_3_DFS": [
                "CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath",
                "CLRSLean.Chapter_22.Section_22_3_DFS.S2_Intervals",
                "CLRSLean.Chapter_22.Section_22_3_DFS.S3_Bridge",
                "CLRSLean.Chapter_22.Section_22_3_DFS.S4_SCC",
                "CLRSLean.Chapter_22.Section_22_3_DFS.S5_EdgeClassification",
            ],
            "CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components": [
                "CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components.MergeSortCongr",
            ],
        }

        for parent, children in expected.items():
            with self.subTest(parent=parent):
                self.assertEqual(children, order_children[parent])

    def test_hidden_support_pages_are_linked_from_reader_pages(self) -> None:
        order_children = _parse_order_children(LITERATE_TOML.read_text())

        for chapter in order_children["CLRSLean"]:
            if not chapter.startswith("CLRSLean.Chapter_"):
                continue
            chapter_text = _module_source(chapter).read_text()
            for module in _ordered_descendants(order_children, chapter):
                if is_reader_sidebar_module(module) or module in LINK_EXEMPT_MODULES:
                    continue
                parts = module.split(".")
                while len(parts) > 1:
                    parts.pop()
                    parent = ".".join(parts)
                    if is_reader_sidebar_module(parent):
                        break
                parent_text = _module_source(parent).read_text()
                expected_link = f"{module.replace('.', '/')}/"
                with self.subTest(module=module):
                    self.assertTrue(
                        expected_link in parent_text or expected_link in chapter_text,
                        f"missing implementation link for {module}: {expected_link}",
                    )

    def test_sibling_pages_do_not_repeat_clrs_section_numbers(self) -> None:
        order_children = _parse_order_children(LITERATE_TOML.read_text())

        for parent, children in order_children.items():
            seen: dict[tuple[str, str], str] = {}
            for child in children:
                leaf = child.rsplit(".", 1)[-1]
                match = re.fullmatch(r"Section_(\d+)_(\d+)(?:_.*)?", leaf)
                if match is None:
                    continue
                section = (match.group(1), match.group(2))
                with self.subTest(parent=parent, section=section):
                    self.assertNotIn(section, seen, f"also listed by {seen.get(section)}")
                seen[section] = child

    def test_proof_pattern_imports_are_ordered_and_titled(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = _parse_order_children(text)
        titled_modules = _parse_module_titles(text)
        parent = "CLRSLean.ProofPatterns"

        imported_modules = re.findall(
            r"^import\s+(CLRSLean\.ProofPatterns\.[^\s]+)",
            (ROOT / "CLRSLean" / "ProofPatterns.lean").read_text(),
            re.MULTILINE,
        )

        self.assertEqual(imported_modules, order_children[parent])
        missing_titles = [module for module in imported_modules if module not in titled_modules]
        self.assertEqual([], missing_titles)


if __name__ == "__main__":
    unittest.main()
