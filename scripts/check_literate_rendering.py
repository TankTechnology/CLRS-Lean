#!/usr/bin/env python3
"""Check generated literate HTML for raw Markdown artifacts."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.literate_navigation import (
    is_reader_sidebar_module,
    prune_reader_sidebar,
)


RAW_MARKDOWN_TABLE_RE = re.compile(
    r"<p>\s*\|[^<\n]*\|[^\n]*\n\s*\|[-:|\s]+\|",
    re.IGNORECASE,
)


def iter_html_files(site_root: Path) -> list[Path]:
    return sorted(path for path in site_root.rglob("*.html") if path.is_file())


def module_name_for_html(site_root: Path, html_file: Path) -> str | None:
    relative = html_file.relative_to(site_root)
    if relative.name != "index.html" or not relative.parts or relative.parts[0] != "CLRSLean":
        return None
    return ".".join(relative.parent.parts)


def nearest_visible_parent(module_name: str) -> str | None:
    parts = module_name.split(".")
    while len(parts) > 1:
        parts.pop()
        candidate = ".".join(parts)
        if is_reader_sidebar_module(candidate):
            return candidate
    return None


# Implementation sub-modules that are imported by chapter guides
# but cannot be linked from section parents due to circular imports.
_IMPLEMENTATION_SUBMODULES = {
    "CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis.OnlineHiring",
    "CLRSLean.Chapter_06.Section_06_4_Heapsort.CostedExecution",
}

def check_site(site_root: Path) -> list[str]:
    failures: list[str] = []
    module_files: dict[str, Path] = {}

    for html_file in iter_html_files(site_root):
        module_name = module_name_for_html(site_root, html_file)
        if module_name:
            module_files[module_name] = html_file

        text = html_file.read_text(encoding="utf-8", errors="replace")
        match = RAW_MARKDOWN_TABLE_RE.search(text)
        if match:
            snippet = " ".join(match.group(0).split())[:240]
            failures.append(f"{html_file}: raw Markdown table in paragraph: {snippet}")

        sidebar = prune_reader_sidebar(text)
        for hidden_module in sidebar.removed_modules:
            failures.append(f"{html_file}: forbidden sidebar module: {hidden_module}")
        for flattened_module in sidebar.flattened_modules:
            failures.append(f"{html_file}: empty sidebar disclosure: {flattened_module}")
        for href in sidebar.unclassified_hrefs:
            failures.append(f"{html_file}: unclassified sidebar link: {href}")

    for module_name, html_file in sorted(module_files.items()):
        if is_reader_sidebar_module(module_name) or module_name in _IMPLEMENTATION_SUBMODULES:
            continue
        parent_module = nearest_visible_parent(module_name)
        parent_file = module_files.get(parent_module or "")
        if parent_file is None:
            failures.append(
                f"{html_file}: missing visible parent page for hidden module {module_name}"
            )
            continue
        expected_href = f"{module_name.replace('.', '/')}/"
        parent_text = parent_file.read_text(encoding="utf-8", errors="replace")
        href_pattern = re.compile(
            rf"href=[\"']{re.escape(expected_href)}[\"']", re.IGNORECASE
        )
        if href_pattern.search(parent_text) is None:
            # Fallback: also check the chapter guide (2-level parent)
            parts = module_name.split(".")
            chapter_parent = ".".join(parts[:2]) if len(parts) >= 2 else None
            chapter_file = module_files.get(chapter_parent) if chapter_parent else None
            chapter_ok = False
            if chapter_file is not None:
                chapter_text = chapter_file.read_text(encoding="utf-8", errors="replace")
                if href_pattern.search(chapter_text) is not None:
                    chapter_ok = True
            if not chapter_ok:
                failures.append(
                    f"{parent_file}: missing implementation link for {module_name}: "
                    f"{expected_href}"
                )

    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site_root", type=Path, help="Verso literate-html output directory")
    args = parser.parse_args()

    if not args.site_root.is_dir():
        raise SystemExit(f"site root does not exist or is not a directory: {args.site_root}")

    failures = check_site(args.site_root)
    if failures:
        for failure in failures:
            print(failure)
        raise SystemExit(1)

    print(f"literate rendering OK: {args.site_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
