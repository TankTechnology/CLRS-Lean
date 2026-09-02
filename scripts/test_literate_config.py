import re
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LITERATE_TOML = ROOT / "literate.toml"
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_literate_config import (
    FOURTH_EDITION_CHAPTER_TITLES,
    PRIMARY_ROOT_MODULES,
    parse_module_titles,
    parse_order_children,
    validate_config,
)
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
        return ROOT / "src" / "CLRSLean.lean"
    return ROOT / "src" / Path(*parts[:-1]) / f"{parts[-1]}.lean"


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
    def test_primary_root_is_fourth_edition_first(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = parse_order_children(text)
        titled_modules = parse_module_titles(text)

        self.assertEqual(list(PRIMARY_ROOT_MODULES), order_children["CLRSLean"])
        self.assertEqual("CLRS Fourth Edition", titled_modules.get(PRIMARY_ROOT_MODULES[0]))
        self.assertEqual("Online Material", titled_modules.get(PRIMARY_ROOT_MODULES[1]))

    def test_fourth_edition_chapters_are_ordered_and_titled(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = parse_order_children(text)
        titled_modules = parse_module_titles(text)
        parent = "CLRSLean.FourthEdition"
        expected_modules = [
            f"{parent}.Chapter_{chapter:02d}" for chapter in range(1, 36)
        ]
        imported_modules = re.findall(
            rf"^import\s+({re.escape(parent)}\.Chapter_[^\s]+)",
            (ROOT / "src" / "CLRSLean" / "FourthEdition.lean").read_text(),
            re.MULTILINE,
        )

        self.assertEqual(expected_modules, imported_modules)
        self.assertEqual(expected_modules, order_children.get(parent, []))

        expected_titles = {
            module: f"Chapter {chapter}. {title}"
            for chapter, (module, title) in enumerate(
                zip(expected_modules, FOURTH_EDITION_CHAPTER_TITLES), start=1
            )
        }
        self.assertEqual(
            expected_titles,
            {module: titled_modules.get(module) for module in expected_modules},
        )

    def test_fourth_edition_landing_links_every_reader_route(self) -> None:
        source = (ROOT / "src" / "CLRSLean" / "FourthEdition.lean").read_text(
            encoding="utf-8"
        )
        modules = [
            *(
                f"CLRSLean.FourthEdition.Chapter_{chapter:02d}"
                for chapter in range(1, 36)
            ),
            "CLRSLean.Progress",
            "CLRSLean.Status",
            "CLRSLean.OnlineMaterial",
        ]

        for module in modules:
            with self.subTest(module=module):
                self.assertIn(f"]({module.replace('.', '/')}/)", source)

    def test_fourth_edition_chapter_34_has_five_reader_sections(self) -> None:
        chapter = "CLRSLean.FourthEdition.Chapter_34"
        expected = [
            f"{chapter}.Section_34_1_Polynomial_Time",
            f"{chapter}.Section_34_2_Polynomial_Time_Verification",
            f"{chapter}.Section_34_3_NP_Completeness_And_Reducibility",
            f"{chapter}.Section_34_4_NP_Completeness_Proofs",
            f"{chapter}.Section_34_5_NP_Complete_Problems",
        ]
        chapter_source = _module_source(chapter).read_text(encoding="utf-8")
        imported_sections = re.findall(
            rf"^import\s+({re.escape(chapter)}\.Section_[^\s]+)",
            chapter_source,
            re.MULTILINE,
        )
        config_text = LITERATE_TOML.read_text(encoding="utf-8")
        order_children = parse_order_children(config_text)
        titled_modules = parse_module_titles(config_text)

        self.assertEqual(expected, imported_sections)
        self.assertEqual(expected, order_children.get(chapter, []))
        self.assertTrue(all(module in titled_modules for module in expected))
        self.assertTrue(
            all(
                f"]({module.replace('.', '/')}/)" in chapter_source
                for module in expected
            )
        )

    def test_completed_fourth_edition_sections_have_canonical_titles(self) -> None:
        titles = parse_module_titles(LITERATE_TOML.read_text(encoding="utf-8"))
        expected = {
            "CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp":
                "24.2. The Edmonds-Karp Algorithm",
            "CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.Ford_Fulkerson_Augmentation":
                "Ford-Fulkerson Augmentation Foundation",
            "CLRSLean.FourthEdition.Chapter_24.Section_24_3_Bipartite_Matching":
                "24.3. Maximum Bipartite Matching",
            "CLRSLean.FourthEdition.Chapter_24.Section_24_6_MaxFlow_MinCut":
                "Theorem 24.6. Max-Flow Min-Cut",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality":
                "29.3. Duality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.Definitions":
                "29.3. Dual Feasibility",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.WeakDuality":
                "29.3. Weak Duality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.Optimality":
                "29.3. Primal and Dual Optimality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.ComplementarySlackness":
                "29.3. Complementary-Slackness Gap Identity",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.TerminalCertificate":
                "29.3. Terminal Dual Certificates",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.DictionaryBridge":
                "29.3. Dictionary/Primal Bridge",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.StrongDuality":
                "29.3. Strong Duality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.ComplementarySlacknessTheorem":
                "29.3. Complementary-Slackness Theorem",
        }

        self.assertEqual(
            expected,
            {module: titles.get(module) for module in expected},
        )

    def test_legacy_chapter_pages_stay_titled_but_leave_primary_root(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = parse_order_children(text)
        titled_modules = parse_module_titles(text)
        imported_legacy_guides = re.findall(
            r"^import\s+(CLRSLean\.Chapter_[0-9][0-9])$",
            (ROOT / "src" / "CLRSLean.lean").read_text(),
            re.MULTILINE,
        )

        self.assertTrue(imported_legacy_guides)
        self.assertTrue(all(module in titled_modules for module in imported_legacy_guides))
        self.assertTrue(
            all(module not in order_children["CLRSLean"] for module in imported_legacy_guides)
        )
        reader_catalog_text = (ROOT / "src" / "CLRSLean" / "OnlineMaterial.lean").read_text()
        reader_catalog_text += "".join(
            chapter_file.read_text()
            for chapter_file in sorted(
                (ROOT / "src" / "CLRSLean" / "FourthEdition").glob("Chapter_[0-9][0-9].lean")
            )
        )
        self.assertTrue(
            all(f"{{lit}}`{module}`" in reader_catalog_text for module in imported_legacy_guides)
        )

    def test_chapter_imported_sections_are_ordered_and_titled(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = parse_order_children(text)
        titled_modules = parse_module_titles(text)

        for chapter_file in sorted((ROOT / "src" / "CLRSLean").glob("Chapter_[0-9][0-9].lean")):
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
                if module.startswith(f"{chapter_module}.Section_")
                and module not in COMPATIBILITY_MODULES
            ]
            with self.subTest(chapter=chapter_module):
                self.assertEqual(imported_sections, ordered_sections)

            missing_titles = [module for module in imported_sections if module not in titled_modules]
            with self.subTest(chapter=f"{chapter_module} titles"):
                self.assertEqual([], missing_titles)

    def test_support_pages_are_nested(self) -> None:
        order_children = parse_order_children(LITERATE_TOML.read_text())
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
        order_children = parse_order_children(LITERATE_TOML.read_text())

        for guide in order_children["CLRSLean"]:
            guide_text = _module_source(guide).read_text()
            support_modules = _ordered_descendants(order_children, guide)
            for module in support_modules:
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
                        f"]({expected_link})" in parent_text
                        or f"]({expected_link})" in guide_text,
                        f"missing implementation link for {module}: {expected_link}",
                    )

    def test_sibling_pages_do_not_repeat_clrs_section_numbers(self) -> None:
        order_children = parse_order_children(LITERATE_TOML.read_text())

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
        order_children = parse_order_children(text)
        titled_modules = parse_module_titles(text)
        parent = "CLRSLean.ProofPatterns"

        imported_modules = re.findall(
            r"^import\s+(CLRSLean\.ProofPatterns\.[^\s]+)",
            (ROOT / "src" / "CLRSLean" / "ProofPatterns.lean").read_text(),
            re.MULTILINE,
        )

        self.assertEqual(imported_modules, order_children[parent])
        missing_titles = [module for module in imported_modules if module not in titled_modules]
        self.assertEqual([], missing_titles)


class LiterateConfigCheckerTest(unittest.TestCase):
    def _validate_config(self, text: str) -> list[str]:
        return validate_config(
            text,
            (ROOT / "src" / "CLRSLean" / "FourthEdition.lean").read_text(),
        )

    def test_accepts_fourth_edition_primary_config(self) -> None:
        self.assertEqual([], self._validate_config(LITERATE_TOML.read_text()))

    def test_rejects_legacy_chapter_in_primary_root(self) -> None:
        broken = LITERATE_TOML.read_text().replace(
            '  "CLRSLean.OnlineMaterial",',
            '  "CLRSLean.Chapter_01",',
            1,
        )

        self.assertTrue(
            any("primary root order" in error for error in self._validate_config(broken))
        )

    def test_rejects_out_of_order_fourth_edition_chapters(self) -> None:
        broken = LITERATE_TOML.read_text().replace(
            '  "CLRSLean.FourthEdition.Chapter_01",\n'
            '  "CLRSLean.FourthEdition.Chapter_02",',
            '  "CLRSLean.FourthEdition.Chapter_02",\n'
            '  "CLRSLean.FourthEdition.Chapter_01",',
            1,
        )

        self.assertTrue(
            any(
                "fourth-edition chapter order" in error
                for error in self._validate_config(broken)
            )
        )

    def test_rejects_mistitled_fourth_edition_chapter(self) -> None:
        broken = LITERATE_TOML.read_text().replace(
            'title = "Chapter 19. Data Structures for Disjoint Sets"',
            'title = "Chapter 19. Fibonacci Heaps"',
            1,
        )

        self.assertTrue(
            any(
                "CLRSLean.FourthEdition.Chapter_19 title" in error
                for error in self._validate_config(broken)
            )
        )


if __name__ == "__main__":
    unittest.main()
