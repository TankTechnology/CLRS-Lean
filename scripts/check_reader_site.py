#!/usr/bin/env python3
"""Check the published reading contract for every fourth-edition chapter."""
from __future__ import annotations

import argparse
import html
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urljoin, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.check_literate_config import parse_order_children, parse_module_titles
from scripts.reader_layout import plain_text
from scripts.inline_chapter_sections import section_anchor
from scripts.literate_navigation import MODULE_TREE_RE, canonical_sections


def check_reader_site(site: Path) -> list[str]:
    errors: list[str] = []
    orders = parse_order_children((ROOT / 'literate.toml').read_text())
    section_titles = parse_module_titles((ROOT / 'literate.toml').read_text())
    chapters = [f'CLRSLean.FourthEdition.Chapter_{n:02d}' for n in range(1, 36)]
    expected_nav = set(chapters) | canonical_sections()
    for module in chapters:
        path = site.joinpath(*module.split('.'), 'index.html')
        if not path.is_file():
            errors.append(f'{module}: missing chapter page')
            continue
        text = path.read_text()
        nav = MODULE_TREE_RE.search(text)
        if not nav:
            errors.append(f'{module}: missing sidebar')
            continue
        titles = set(re.findall(r'title="(CLRSLean\.FourthEdition\.Chapter_[^"]+)"', nav.group()))
        if titles != expected_nav:
            errors.append(f'{module}: sidebar differs from the canonical chapter/section inventory: {sorted(titles ^ expected_nav)}')
        if 'clrs-nav-pending' in text:
            errors.append(f'{module}: navigation waits for JavaScript')
        ids = re.findall(r'\bid="([^"]+)"', text)
        id_set = set(ids)
        if len(ids) != len(id_set):
            errors.append(f'{module}: duplicate HTML IDs')
        sections = [child for child in orders.get(module, []) if child in canonical_sections()]
        for child in sections:
            section_path = site.joinpath(*child.split('.'), 'index.html')
            section_text = section_path.read_text() if section_path.is_file() else ''
            heading = re.search(r'<main\b.*?<h1\b[^>]*>(.*?)</h1>', section_text, re.S)
            expected = section_titles[child]
            if heading is None or plain_text(heading.group(1)) != expected:
                errors.append(f'{child}: section heading differs from its navigation title')
            anchor = section_anchor(child)
            if anchor not in id_set:
                errors.append(f'{module}: section is not embedded: {child}')
            if f'href="{module.replace(".", "/")}/#{anchor}"' not in text:
                errors.append(f'{module}: missing section anchor link: {child}')
        if sections:
            toc = re.search(r'<nav\b[^>]*class="page-toc"[^>]*>.*?</nav>', text, re.S)
            if toc is None or any(section_anchor(child) not in toc.group() for child in sections):
                errors.append(f'{module}: page TOC omits section bodies')
            if len(re.findall(r'<h1\b', text)) != 1:
                errors.append(f'{module}: expected one chapter h1')
        # Verso's base element resolves module links relative to the site root.
        for raw in re.findall(r'href="([^"]*)"', text):
            url = urlsplit(urljoin('https://reader.test/', html.unescape(raw)))
            if url.netloc != 'reader.test':
                continue
            target = site / unquote(url.path).lstrip('/')
            if url.path.endswith('/'):
                target = target / 'index.html'
            if not target.is_file():
                errors.append(f'{module}: broken local link: {raw}')
            if target == path and url.fragment and unquote(url.fragment) not in id_set:
                errors.append(f'{module}: broken same-page anchor: {raw}')
    return errors


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('site', type=Path)
    args = parser.parse_args()
    failures = check_reader_site(args.site)
    for failure in failures:
        print(failure)
    if failures:
        sys.exit(1)
    print('Reader site OK: all 35 chapters, canonical navigation, inline sections, TOCs and local links')
