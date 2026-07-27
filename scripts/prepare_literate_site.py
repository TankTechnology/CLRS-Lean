#!/usr/bin/env python3
"""Assemble the optimized static site used by local previews and GitHub Pages."""

from __future__ import annotations

import argparse
import datetime as dt
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_literate_rendering import check_site
from scripts.generate_sitemap import iter_html_pages, page_url, render_sitemap
from scripts.optimize_literate_html import iter_html_files, optimize_file


DEFAULT_BASE_URL = "https://tanktechnology.github.io/CLRS-Lean/"
DEFAULT_STYLESHEET = ROOT / "docs/literate/clrs-literate.css"


@dataclass(frozen=True)
class SitePreparationResult:
    html_pages: int
    optimized_pages: int
    sitemap_urls: int


def prepare_site(
    source: Path,
    destination: Path,
    *,
    stylesheet: Path = DEFAULT_STYLESHEET,
    base_url: str = DEFAULT_BASE_URL,
    lastmod: str | None = None,
    strip_attrs_min_bytes: int = 1_000_000,
) -> SitePreparationResult:
    """Copy, optimize, validate, and index one Verso output directory."""
    source = source.resolve()
    destination = destination.resolve()
    stylesheet = stylesheet.resolve()

    if not source.is_dir():
        raise ValueError(f"Verso output does not exist or is not a directory: {source}")
    if not stylesheet.is_file():
        raise ValueError(f"stylesheet does not exist or is not a file: {stylesheet}")
    if (
        destination == source
        or source in destination.parents
        or destination in source.parents
    ):
        raise ValueError("source and destination must not overlap")

    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination)
    shutil.copy2(stylesheet, destination / "clrs-literate.css")

    html_files = list(iter_html_files([destination]))
    optimized_pages = 0
    for html_file in html_files:
        if optimize_file(html_file, strip_attrs_min_bytes).changed:
            optimized_pages += 1

    failures = check_site(destination)
    if failures:
        details = "\n  ".join(failures)
        raise ValueError(f"literate rendering checks failed:\n  {details}")

    sitemap_pages = iter_html_pages(destination)
    if not sitemap_pages:
        raise ValueError(f"no HTML pages found under {destination}")
    sitemap_urls = [page_url(destination, page, base_url) for page in sitemap_pages]
    sitemap_lastmod = lastmod or dt.datetime.now(dt.timezone.utc).date().isoformat()
    (destination / "sitemap.xml").write_text(
        render_sitemap(sitemap_urls, sitemap_lastmod),
        encoding="utf-8",
        newline="",
    )

    return SitePreparationResult(
        html_pages=len(html_files),
        optimized_pages=optimized_pages,
        sitemap_urls=len(sitemap_urls),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "source", type=Path, help="Raw Verso literate-html output directory."
    )
    parser.add_argument(
        "destination", type=Path, help="Deployable static-site directory."
    )
    parser.add_argument(
        "--stylesheet",
        type=Path,
        default=DEFAULT_STYLESHEET,
        help="Stylesheet copied to clrs-literate.css in the destination.",
    )
    parser.add_argument(
        "--base-url",
        default=DEFAULT_BASE_URL,
        help="Canonical public base URL used in sitemap.xml.",
    )
    parser.add_argument(
        "--lastmod",
        help="ISO date written into sitemap.xml (defaults to the current UTC date).",
    )
    args = parser.parse_args()

    result = prepare_site(
        args.source,
        args.destination,
        stylesheet=args.stylesheet,
        base_url=args.base_url,
        lastmod=args.lastmod,
    )
    print(
        f"prepared {args.destination}: {result.html_pages} HTML pages, "
        f"{result.optimized_pages} changed, {result.sitemap_urls} sitemap URLs"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
