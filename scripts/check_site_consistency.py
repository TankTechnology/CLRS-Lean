#!/usr/bin/env python3
"""
Check that the CLRS-Lean website structure is consistent.

This script verifies:
- every represented chapter and section has a module doc;
- literate.toml lists every chapter/section in [order_children];
- every [order_children] relationship matches the Lean module hierarchy;
- literate.toml has a [modules] title entry for every chapter/section;
- literate.toml does not list files that do not exist;
- CLRSLean.lean imports every represented chapter guide.
- docs/index.md lists every represented section source path.

Run from the repository root:
    python3 scripts/check_site_consistency.py
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLRSLEAN = ROOT / "CLRSLean"
LITERATE = ROOT / "literate.toml"
LANDING = ROOT / "CLRSLean.lean"
DOCS_INDEX = ROOT / "docs" / "index.md"


def parse_literate(path: Path):
    """Return (order_children, modules) from literate.toml."""
    text = path.read_text(encoding="utf-8")
    # Strip comments (safe for this file: strings do not contain #).
    text = re.sub(r"#.*", "", text)

    order_children = {}
    oc_match = re.search(
        r"\[order_children\]\s*(.*?)(?=^\[|\Z)",
        text,
        re.MULTILINE | re.DOTALL,
    )
    if oc_match:
        block = oc_match.group(1)
        for m in re.finditer(
            r'"([^"]+)"\s*=\s*\[(.*?)\]', block, re.DOTALL
        ):
            key = m.group(1)
            values = [
                v.strip().strip('"')
                for v in m.group(2).split(",")
                if v.strip()
            ]
            order_children[key] = values

    modules = {}
    for m in re.finditer(
        r'\[modules\."([^"]+)"\]\s*title\s*=\s*"([^"]+)"',
        text,
        re.DOTALL,
    ):
        modules[m.group(1)] = m.group(2)

    return order_children, modules


def module_doc_present(path: Path) -> bool:
    return "/-!" in path.read_text(encoding="utf-8")


def module_file_exists(module: str) -> bool:
    if not module.startswith("CLRSLean."):
        return False
    rel = module[len("CLRSLean."):].replace(".", "/") + ".lean"
    return (CLRSLEAN / rel).is_file()


def ordered_descendants(order_children: dict[str, list[str]], parent: str) -> list[str]:
    """Flatten the navigation subtree rooted at parent in reading order."""
    descendants = []
    expanded = set()

    def visit(current: str) -> None:
        for child in order_children.get(current, []):
            if child in expanded:
                continue
            expanded.add(child)
            descendants.append(child)
            visit(child)

    visit(parent)
    return descendants


def main() -> int:
    errors = []
    warnings = []

    order_children, modules = parse_literate(LITERATE)
    docs_index_text = DOCS_INDEX.read_text(encoding="utf-8")

    # ---- discover chapter guides and represented sections ----
    chapter_guides = sorted(CLRSLEAN.glob("Chapter_[0-9][0-9].lean"))
    chapter_dirs = sorted(
        d for d in CLRSLEAN.iterdir()
        if d.is_dir() and re.match(r"Chapter_\d+", d.name)
    )

    represented_chapters = []
    for ch_dir in chapter_dirs:
        guide = CLRSLEAN / (ch_dir.name + ".lean")
        if not guide.is_file():
            errors.append(f"Chapter directory {ch_dir.name} has no guide file {guide.name}")
            continue
        represented_chapters.append(ch_dir.name)

    # ---- check landing page imports ----
    landing_text = LANDING.read_text(encoding="utf-8")
    for guide in chapter_guides:
        ch_name = guide.stem
        import_name = f"import CLRSLean.{ch_name}"
        if import_name not in landing_text:
            errors.append(f"CLRSLean.lean is missing import for {ch_name}")

    # ---- check chapter guides ----
    for guide in chapter_guides:
        ch_name = guide.stem
        if not module_doc_present(guide):
            errors.append(f"Chapter guide {guide} has no module doc")

        module = f"CLRSLean.{ch_name}"
        if module not in order_children.get("CLRSLean", []):
            errors.append(f"literate.toml [order_children] 'CLRSLean' does not list {module}")
        if module not in modules:
            errors.append(f"literate.toml has no [modules.\"{module}\"] title entry")

    # ---- check section files ----
    for ch_dir in chapter_dirs:
        guide = CLRSLEAN / (ch_dir.name + ".lean")
        if not guide.is_file():
            continue

        chapter_module = f"CLRSLean.{ch_dir.name}"
        expected_sections = ordered_descendants(order_children, chapter_module)

        section_files = sorted(ch_dir.rglob("*.lean"))

        for sec_file in section_files:
            sec_rel = sec_file.relative_to(ch_dir).with_suffix("")
            sec_module = f"CLRSLean.{ch_dir.name}." + ".".join(sec_rel.parts)
            sec_path = sec_file.relative_to(ROOT).as_posix()

            if not module_doc_present(sec_file):
                errors.append(f"Section file {sec_file} has no module doc")

            if sec_module not in expected_sections:
                errors.append(
                    f"literate.toml navigation tree under '{chapter_module}' does not list "
                    f"{sec_module}"
                )
            if sec_module not in modules:
                errors.append(
                    f"literate.toml has no [modules.\"{sec_module}\"] title entry"
                )
            if sec_path not in docs_index_text:
                errors.append(f"docs/index.md does not list section source: {sec_path}")

    # ---- check that every ordered module actually exists ----
    for parent, children in order_children.items():
        for child in children:
            child_parent, _, _ = child.rpartition(".")
            if child_parent != parent:
                errors.append(
                    f"literate.toml lists {child} under {parent}, but its module parent is "
                    f"{child_parent or '<root>'}"
                )
            if not module_file_exists(child):
                errors.append(f"literate.toml lists non-existent module: {child}")

    # ---- check that every module title has a corresponding file ----
    for mod in modules:
        if not module_file_exists(mod):
            # Top-level CLRSLean itself is not a file under CLRSLean/, that's fine.
            if mod != "CLRSLean":
                errors.append(f"literate.toml [modules.\"{mod}\"] has no file")

    # ---- docs/chapters markdown consistency (advisory) ----
    # These are optional supplementary notes; Lean chapter guides are canonical.
    docs_chapters = ROOT / "docs" / "chapters"
    if docs_chapters.is_dir():
        md_pages = {
            p.stem for p in docs_chapters.iterdir()
            if p.suffix == ".md" and p.name != "README.md"
        }
        expected_md = {f"chapter-{int(ch.name.split('_')[1]):02d}" for ch in chapter_dirs}
        for page in sorted(md_pages - expected_md):
            warnings.append(
                f"docs/chapters/{page}.md has no matching represented chapter"
            )

    # ---- report ----
    if warnings:
        print("Warnings:")
        for w in warnings:
            print(f"  - {w}")
    if errors:
        print("Errors:")
        for e in errors:
            print(f"  - {e}")
        return 1

    print("Site structure is consistent.")
    print(f"  Chapter guide pages: {len(chapter_guides)}")
    print(f"  Chapters with section files: {len(represented_chapters)}")
    print(f"  Section files: {sum(1 for d in chapter_dirs for _ in d.rglob('*.lean'))}")
    print(f"  literate.toml modules: {len(modules)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
