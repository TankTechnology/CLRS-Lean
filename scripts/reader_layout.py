"""Static chapter reading order and contents; no client-side content assembly."""
from __future__ import annotations

import html
import re

HEADING_RE = re.compile(r'<h([1-6])\b([^>]*)>(.*?)</h\1>', re.S | re.I)
TOC_RE = re.compile(r'<nav\b[^>]*class="page-toc"[^>]*>.*?</nav>', re.S)


def plain_text(markup: str) -> str:
    return ' '.join(html.unescape(re.sub(r'<[^>]*>', '', markup)).split())


def section_heading(content: str, fallback: str) -> str:
    match = HEADING_RE.search(content)
    return plain_text(match.group(3)) if match else fallback


def canonical_section_title(document: str, title: str) -> str:
    """Use the navigation title in the body and TOC without changing link targets."""
    main = re.search(r'<main\b[^>]*>', document)
    if main is None:
        return document
    heading = HEADING_RE.search(document, main.end())
    if heading is None or heading.group(1) != '1':
        return document
    label = html.escape(title)
    original = plain_text(heading.group(3))
    document = document[:heading.start(3)] + label + document[heading.end(3):]

    def update_toc(match: re.Match[str]) -> str:
        return re.sub(
            r'(<a\b[^>]*>)(.*?)(</a>)',
            lambda link: link.group(1) + label + link.group(3)
            if plain_text(link.group(2)) == original else link.group(),
            match.group(), flags=re.S,
        )

    return TOC_RE.sub(update_toc, document)


def nest_headings(content: str) -> str:
    def replace(match: re.Match[str]) -> str:
        level = min(int(match.group(1)) + 1, 6)
        return f'<h{level}{match.group(2)}>{match.group(3)}</h{level}>'
    return HEADING_RE.sub(replace, content)


def chapter_layout(guide: str, sections: str, entries: list[tuple[str, str]], route: str) -> str:
    heading = HEADING_RE.search(guide)
    if heading is None:
        # Small fixtures and generated pages without a guide retain their content.
        return guide + sections
    title = heading.group(0)
    notes = guide[:heading.start()] + guide[heading.end():]
    notes = re.sub(
        r'<p>\s*This is the canonical CLRS fourth-edition chapter guide during the migration\s+period\.\s*</p>',
        '', notes,
    )
    links = ''.join(
        f'<li><a href="{route}#{html.escape(anchor, quote=True)}">{html.escape(label)}</a></li>'
        for anchor, label in entries
    )
    return (
        f'<header class="clrs-chapter-header">{title}'
        '<p>CLRS, fourth edition · Lean 4 formalization</p></header>'
        '<nav class="clrs-chapter-contents" aria-label="Chapter sections">'
        f'<h2>In this chapter</h2><ol>{links}</ol></nav>'
        '<p class="clrs-scope-note">The proofs below use the models and assumptions '
        f'described in the <a href="{route}#clrs-chapter-notes">scope and implementation notes</a>.</p>'
        f'{sections}<section class="clrs-chapter-notes" id="clrs-chapter-notes">'
        f'<h2>Scope and implementation notes</h2>{notes}</section>'
    )


def chapter_toc(document: str, entries: list[tuple[str, str]], route: str) -> str:
    links = ''.join(
        f'<li><a href="{route}#{html.escape(anchor, quote=True)}">{html.escape(label)}</a></li>'
        for anchor, label in entries
    )
    toc = (
        '<nav class="page-toc" aria-label="Page table of contents">'
        '<div class="page-toc-title">In this chapter</div>'
        f'<ul>{links}<li><a href="{route}#clrs-chapter-notes">Scope and implementation notes</a></li></ul></nav>'
    )
    return TOC_RE.sub(lambda _: toc, document, count=1)


def reader_chrome(document: str, route: str) -> str:
    """Reserve search space and add a base-URL-safe skip link before first paint."""
    if 'data-search-host' not in document:
        document = re.sub(
            r'(<script\b[^>]*src=")-verso-search/searchIndex\.js("[^>]*>)',
            r'\1clrs-search.js\2', document,
        )
    if 'class="clrs-skip-link"' not in document and '<main' in document:
        match = re.search(r'<main\b([^>]*)>', document)
        assert match is not None
        id_match = re.search(r'\bid="([^"]+)"', match.group(1))
        target = id_match.group(1) if id_match else 'clrs-main'
        if id_match is None:
            document = document[:match.end()-1] + ' id="clrs-main" tabindex="-1">' + document[match.end():]
        skip = f'<a class="clrs-skip-link" href="{route}#{target}">Skip to content</a>'
        document = re.sub(r'(<body\b[^>]*>)', lambda m: m.group(1) + skip, document, count=1)
    if 'class="clrs-search-fallback"' not in document:
        document = re.sub(
            r'(<header\b[^>]*class="title-bar"[^>]*>.*?)(</header>)',
            lambda m: m.group(1) + '<a class="clrs-search-fallback" href="CLRSLean/FourthEdition/">Browse chapters</a>' + m.group(2),
            document, count=1, flags=re.S,
        )
    return document
