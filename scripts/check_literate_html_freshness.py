#!/usr/bin/env python3
"""Fail when generated Verso pages no longer correspond to source modules."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def expected_source(root: Path, rel_parts: tuple[str, ...]) -> Path | None:
    if not rel_parts:
        return root / "CLRSLean.lean"

    if len(rel_parts) == 1:
        return root / "CLRSLean" / f"{rel_parts[0]}.lean"

    return root / "CLRSLean" / Path(*rel_parts[:-1]) / f"{rel_parts[-1]}.lean"


def stale_pages(root: Path, site_root: Path) -> list[tuple[Path, Path]]:
    clrs_root = site_root / "CLRSLean"
    if not clrs_root.exists():
        return []

    stale: list[tuple[Path, Path]] = []
    for index in sorted(clrs_root.rglob("index.html")):
        rel_dir = index.parent.relative_to(clrs_root)
        rel_parts = () if str(rel_dir) == "." else rel_dir.parts
        source = expected_source(root, rel_parts)
        if source is not None and not source.exists():
            stale.append((index, source))
    return stale


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check that generated CLRSLean HTML pages have matching .lean sources.",
    )
    parser.add_argument("site_root", type=Path, help="Verso literate-html output directory")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    site_root = args.site_root.resolve()
    stale = stale_pages(root, site_root)
    if stale:
        print("stale generated literate HTML pages found:", file=sys.stderr)
        for html, source in stale:
            print(f"- {html.relative_to(root)} -> missing {source.relative_to(root)}", file=sys.stderr)
        return 1

    print(f"literate HTML freshness OK: {site_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
