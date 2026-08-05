#!/usr/bin/env python3
"""Check generated literate HTML for raw Markdown artifacts."""

from __future__ import annotations

import argparse
import html
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.literate_navigation import (
    is_reader_sidebar_module,
    load_reader_parent_routes,
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


def nearest_visible_parent(
    module_name: str, reader_parent_routes: dict[str, str] | None = None
) -> str | None:
    routes = (
        load_reader_parent_routes()
        if reader_parent_routes is None
        else reader_parent_routes
    )
    matching_prefixes = [
        prefix
        for prefix in routes
        if module_name == prefix or module_name.startswith(f"{prefix}.")
    ]
    if matching_prefixes:
        return routes[max(matching_prefixes, key=len)]

    parts = module_name.split(".")
    while len(parts) > 1:
        parts.pop()
        candidate = ".".join(parts)
        if is_reader_sidebar_module(candidate):
            return candidate
    return None


# Hidden modules that intentionally have no reader-page link: two are imported
# directly by chapter guides to avoid circular imports, and the Chapter 19
# entries are compatibility-only URLs rather than canonical reading pages.
_IMPLEMENTATION_SUBMODULES = {
    "CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis.OnlineHiring",
    "CLRSLean.Chapter_06.Section_06_4_Heapsort.CostedExecution",
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap",
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts",
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts",
}

HREF_RE = re.compile(r"href=[\"']([^\"']+)[\"']", re.IGNORECASE)


def module_name_for_href(href: str) -> str | None:
    """Convert a root-relative Verso module URL, including fragments, to a name."""
    target = html.unescape(href).split("#", 1)[0].split("?", 1)[0].strip("/")
    if target != "CLRSLean" and not target.startswith("CLRSLean/"):
        return None
    return target.replace("/", ".")

def check_site(site_root: Path) -> list[str]:
    failures: list[str] = []
    module_files: dict[str, Path] = {}
    reader_parent_routes = load_reader_parent_routes()

    for html_file in iter_html_files(site_root):
        module_name = module_name_for_html(site_root, html_file)
        if module_name:
            module_files[module_name] = html_file

        text = html_file.read_text(encoding="utf-8", errors="replace")
        match = RAW_MARKDOWN_TABLE_RE.search(text)
        if match:
            snippet = " ".join(match.group(0).split())[:240]
            failures.append(f"{html_file}: raw Markdown table in paragraph: {snippet}")

        sidebar = prune_reader_sidebar(text, reader_parent_routes)
        for hidden_module in sidebar.removed_modules:
            failures.append(f"{html_file}: forbidden sidebar module: {hidden_module}")
        for flattened_module in sidebar.flattened_modules:
            failures.append(f"{html_file}: empty sidebar disclosure: {flattened_module}")
        for href in sidebar.unclassified_hrefs:
            failures.append(f"{html_file}: unclassified sidebar link: {href}")

    page_links: dict[str, set[str]] = {}
    for module_name, html_file in module_files.items():
        text = html_file.read_text(encoding="utf-8", errors="replace")
        page_links[module_name] = {
            target
            for href in HREF_RE.findall(text)
            if (target := module_name_for_href(href)) in module_files
        }

    reachable_from: dict[str, set[str]] = {}

    def reachable(start: str) -> set[str]:
        if start in reachable_from:
            return reachable_from[start]
        seen = {start}
        todo = [start]
        while todo:
            current = todo.pop()
            for target in page_links.get(current, set()):
                if target not in seen:
                    seen.add(target)
                    todo.append(target)
        reachable_from[start] = seen
        return seen

    for module_name, html_file in sorted(module_files.items()):
        if is_reader_sidebar_module(module_name) or module_name in _IMPLEMENTATION_SUBMODULES:
            continue
        parent_module = nearest_visible_parent(module_name, reader_parent_routes)
        parent_file = module_files.get(parent_module or "")
        if parent_file is None:
            failures.append(
                f"{html_file}: missing visible parent page for hidden module {module_name}"
            )
            continue
        if module_name not in reachable(parent_module):
            failures.append(
                f"{parent_file}: missing implementation link for {module_name} "
                f"(no path to {module_name.replace('.', '/')}/)"
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
