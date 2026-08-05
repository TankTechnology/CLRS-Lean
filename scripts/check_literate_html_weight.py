#!/usr/bin/env python3
"""Reject oversized raw Verso pages and inline tactic-state markup."""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path


DEFAULT_MAX_PAGE_BYTES = 25 * 1024 * 1024
READ_CHUNK_BYTES = 64 * 1024
TACTIC_CLASSES = {"tactic-state", "tactic-toggle"}


@dataclass(frozen=True, order=True)
class Violation:
    """One deterministic raw-page policy violation."""

    path: Path
    message: str


class TacticMarkupDetector(HTMLParser):
    """Collect tactic widget classes without matching CSS or JavaScript text."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self.found: set[str] = set()

    def handle_starttag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        self._inspect(attrs)

    def handle_startendtag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        self._inspect(attrs)

    def _inspect(self, attrs: list[tuple[str, str | None]]) -> None:
        for name, value in attrs:
            if name.lower() == "class" and value:
                self.found.update(TACTIC_CLASSES.intersection(value.split()))


def inspect_page(path: Path, max_page_bytes: int) -> list[str]:
    """Return all applicable violations for one generated page."""
    size = path.stat().st_size
    if size > max_page_bytes:
        return [f"size {size} exceeds {max_page_bytes} bytes"]

    parser = TacticMarkupDetector()
    with path.open("r", encoding="utf-8", errors="replace") as stream:
        while chunk := stream.read(READ_CHUNK_BYTES):
            parser.feed(chunk)
    parser.close()
    return [f"inline {class_name} markup" for class_name in sorted(parser.found)]


def check_site(root: Path, max_page_bytes: int) -> tuple[int, list[Violation]]:
    """Check generated module index pages in stable path order."""
    pages = sorted(root.rglob("index.html"))
    violations = [
        Violation(page.relative_to(root), message)
        for page in pages
        for message in inspect_page(page, max_page_bytes)
    ]
    if not pages:
        violations.append(Violation(Path("."), "no index.html pages found"))
    return len(pages), sorted(violations)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument(
        "--max-page-bytes",
        type=int,
        default=DEFAULT_MAX_PAGE_BYTES,
        help="Maximum allowed raw index.html size (default: 25 MiB).",
    )
    args = parser.parse_args()

    if not args.site.is_dir():
        print(f"error: site directory does not exist: {args.site}", file=sys.stderr)
        return 1
    if args.max_page_bytes < 1:
        print("error: --max-page-bytes must be positive", file=sys.stderr)
        return 1

    pages, violations = check_site(args.site.resolve(), args.max_page_bytes)
    if violations:
        for violation in violations:
            print(f"{violation.path}: {violation.message}", file=sys.stderr)
        return 1

    print(f"checked {pages} raw HTML pages; max page size {args.max_page_bytes} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
