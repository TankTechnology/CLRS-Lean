#!/usr/bin/env python3
"""Generate a sitemap.xml file for the built CLRS-Lean static site."""

from __future__ import annotations

import argparse
import datetime as dt
from pathlib import Path
from xml.sax.saxutils import escape


def normalize_base_url(base_url: str) -> str:
    return base_url.rstrip("/") + "/"


def page_url(site_root: Path, html_file: Path, base_url: str) -> str:
    rel = html_file.relative_to(site_root).as_posix()
    if rel == "index.html":
        path = ""
    elif rel.endswith("/index.html"):
        path = rel[: -len("index.html")]
    else:
        path = rel
    return normalize_base_url(base_url) + path


def iter_html_pages(site_root: Path) -> list[Path]:
    return sorted(
        path
        for path in site_root.rglob("*.html")
        if path.is_file() and path.name != "404.html"
    )


def render_sitemap(urls: list[str], lastmod: str) -> str:
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
    ]
    for url in urls:
        lines.extend(
            [
                "  <url>",
                f"    <loc>{escape(url)}</loc>",
                f"    <lastmod>{lastmod}</lastmod>",
                "  </url>",
            ]
        )
    lines.append("</urlset>")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site_root", type=Path, help="Built static-site directory.")
    parser.add_argument(
        "--base-url",
        default="https://tanktechnology.github.io/CLRS-Lean/",
        help="Canonical public base URL for the deployed site.",
    )
    parser.add_argument(
        "--lastmod",
        default=dt.datetime.now(dt.timezone.utc).date().isoformat(),
        help="ISO date to write into each sitemap entry.",
    )
    args = parser.parse_args()

    site_root = args.site_root
    if not site_root.is_dir():
        raise SystemExit(f"site root does not exist or is not a directory: {site_root}")

    urls = [page_url(site_root, html_file, args.base_url) for html_file in iter_html_pages(site_root)]
    if not urls:
        raise SystemExit(f"no HTML pages found under {site_root}")

    sitemap = site_root / "sitemap.xml"
    sitemap.write_text(render_sitemap(urls, args.lastmod), encoding="utf-8", newline="")
    print(f"wrote {sitemap} with {len(urls)} URLs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
