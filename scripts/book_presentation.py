"""Static front matter, sequential reading and colophon for the online book."""
from __future__ import annotations

import html
import re
from pathlib import Path

from scripts.check_literate_config import FOURTH_EDITION_CHAPTER_TITLES
from scripts.inline_chapter_sections import _code_content_bounds

CONTENTS = 'CLRSLean/FourthEdition/'


def book_metadata(document: str, base_url: str) -> str:
    if 'name="clrs-book-presentation"' in document:
        return document
    document = document.replace('<link rel="icon" href="data:,">', '')
    image = html.escape(base_url.rstrip('/') + '/assets/clrs-lean-social.jpg', quote=True)
    title_match = re.search(r'<title>(.*?)</title>', document, re.S)
    title = html.escape(html.unescape(title_match.group(1)), quote=True) if title_match else 'CLRS-Lean'
    meta = (
        '<meta name="clrs-book-presentation" content="1">'
        '<link rel="stylesheet" href="clrs-book.css">'
        '<link rel="icon" href="assets/favicon.ico" sizes="16x16 32x32 48x48">'
        '<link rel="icon" type="image/png" href="assets/clrs-lean-icon.png" sizes="192x192">'
        '<link rel="apple-touch-icon" href="assets/apple-touch-icon.png" sizes="180x180">'
        '<meta property="og:type" content="website">'
        '<meta property="og:title" content="' + title + '">'
        '<meta property="og:image" content="' + image + '">'
        '<meta property="og:image:width" content="1200">'
        '<meta property="og:image:height" content="800">'
        '<meta property="og:image:alt" content="CLRS-Lean: Machine-checked algorithms, chapter by chapter.">'
        '<meta name="twitter:card" content="summary_large_image">'
        '<meta name="twitter:image" content="' + image + '">'
    )
    return document.replace('</head>', meta + '</head>', 1)


def cover_art() -> str:
    return (
        '<figure class="clrs-cover-art">'
        '<img src="assets/clrs-lean-cover.webp" width="1536" height="1024" fetchpriority="high" '
        'alt="CLRS-Lean: Machine-checked algorithms, chapter by chapter. '
        'An open book unfolds into algorithm trees, sorting bars, graphs and a proof tree.">'
        '</figure>'
    )


def cover(heading: str) -> str:
    return (
        '<header class="clrs-book-cover"><div class="clrs-cover-copy">'
        '<p class="clrs-book-eyebrow">An open formalization · CLRS, fourth edition</p>'
        f'{heading}<p class="clrs-cover-deck">Algorithms you can read.<br>Proofs Lean can check.</p>'
        '<p class="clrs-cover-description">Explore selected algorithms, their definitions '
        'and machine-checked proofs, chapter by chapter.</p>'
        '<div class="clrs-book-actions">'
        f'<a class="clrs-book-primary" href="{CONTENTS}">Open the book <span aria-hidden="true">↗</span></a>'
        '<a href="CLRSLean/Status/">Explore proof coverage</a></div>'
        '<p class="clrs-cover-edition">35 chapter guides <span aria-hidden="true">/</span> Lean 4</p>'
        '</div>' + cover_art() + '</header>'
    )


def colophon() -> str:
    return (
        '<section class="clrs-book-colophon" id="clrs-book-colophon">'
        '<img src="assets/book-closing.svg" width="720" height="200" loading="lazy" '
        'alt="Branching paths converge into a single node, echoing the cover drawing.">'
        '<p class="clrs-book-eyebrow">The book continues with you</p>'
        '<h2>Keep asking. Keep proving.</h2>'
        '<p>Every theorem begins with a question. Explore a proof, examine its assumptions, '
        'or help make the next chapter clearer.</p>'
        '<div class="clrs-book-actions"><a href="CLRSLean/Workflow/">Contribute to the book</a>'
        '<a href="https://github.com/TankTechnology/CLRS-Lean">Browse the source</a></div>'
        '<p class="clrs-book-credits">A project by TankTechnology and contributors. '
        'Built with Lean, Mathlib and Verso. With thanks to the authors of '
        '<cite>Introduction to Algorithms</cite> and the formalization community.</p>'
        '<p class="clrs-book-credits">This independent companion covers a selected proof inventory. '
        '<a href="CLRSLean/Status/">Read the scope and verification notes.</a></p></section>'
    )


def chapter_navigation(number: int) -> str:
    def link(n: int, relation: str, label: str) -> str:
        title = html.escape(FOURTH_EDITION_CHAPTER_TITLES[n - 1])
        return (f'<a rel="{relation}" href="{CONTENTS}Chapter_{n:02d}/">'
                f'<span>{label}</span><strong>{n}. {title}</strong></a>')
    previous = link(number - 1, 'prev', 'Previous chapter') if number > 1 else (
        f'<a href="{CONTENTS}"><span>Begin here</span><strong>Table of contents</strong></a>')
    following = link(number + 1, 'next', 'Next chapter') if number < 35 else (
        f'<a href="{CONTENTS}"><span>Explore again</span><strong>Return to contents</strong></a>')
    return (f'<nav class="clrs-book-pagination" aria-label="Chapter navigation">{previous}'
            f'{following}</nav><p class="clrs-book-folio">CLRS, fourth edition · Chapter {number} of 35</p>')


def present_book_page(document: str, module: str) -> str:
    if 'data-clrs-book=' in document:
        return document
    chapter = re.fullmatch(r'CLRSLean\.FourthEdition\.Chapter_(\d{2})', module)
    if module not in ('CLRSLean', 'CLRSLean.FourthEdition') and not chapter:
        return document
    main = re.search(r'<main\b[^>]*>', document)
    if main is None or 'class="code-content"' not in document:
        return document
    kind = 'cover' if module == 'CLRSLean' else 'contents' if module == 'CLRSLean.FourthEdition' else 'chapter'
    document = document[:main.end()-1] + f' data-clrs-book="{kind}">' + document[main.end():]
    if kind in ('cover', 'contents'):
        heading = re.search(r'<h1\b[^>]*>.*?</h1>', document[main.start():], re.S)
        if heading:
            start = main.start() + heading.start()
            end = main.start() + heading.end()
            opening = cover(heading.group()) if kind == 'cover' else cover_art() + heading.group()
            document = document[:start] + opening + document[end:]
    ending = colophon() if kind == 'cover' else ''
    if chapter:
        number = int(chapter.group(1))
        if not 1 <= number <= 35:
            raise ValueError(f'Chapter out of range: {number}')
        ending = (colophon() if number == 35 else '') + chapter_navigation(number)
    if ending:
        _, _, end, _ = _code_content_bounds(document, module)
        document = document[:end] + ending + document[end:]
    return document


def present_book(site: Path) -> None:
    pages = [('index.html', 'CLRSLean'), ('CLRSLean/index.html', 'CLRSLean'),
             ('CLRSLean/FourthEdition/index.html', 'CLRSLean.FourthEdition')]
    pages += [(f'{CONTENTS}Chapter_{n:02d}/index.html', f'CLRSLean.FourthEdition.Chapter_{n:02d}')
              for n in range(1, 36)]
    for route, module in pages:
        path = site / route
        if path.is_file():
            source = path.read_text(encoding='utf-8')
            updated = present_book_page(source, module)
            if updated != source:
                path.write_text(updated, encoding='utf-8')
