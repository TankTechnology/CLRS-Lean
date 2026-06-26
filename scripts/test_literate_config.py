import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LITERATE_TOML = ROOT / "literate.toml"


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


class LiterateConfigTest(unittest.TestCase):
    def test_landing_page_imports_are_ordered_and_titled(self) -> None:
        text = LITERATE_TOML.read_text()
        order_children = _parse_order_children(text)
        titled_modules = _parse_module_titles(text)

        imported_modules = re.findall(
            r"^import\s+(CLRSLean\.[^\s]+)",
            (ROOT / "CLRSLean.lean").read_text(),
            re.MULTILINE,
        )

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

            ordered_sections = order_children[chapter_module]
            with self.subTest(chapter=chapter_module):
                self.assertEqual(imported_sections, ordered_sections)

            missing_titles = [module for module in imported_sections if module not in titled_modules]
            with self.subTest(chapter=f"{chapter_module} titles"):
                self.assertEqual([], missing_titles)


if __name__ == "__main__":
    unittest.main()
