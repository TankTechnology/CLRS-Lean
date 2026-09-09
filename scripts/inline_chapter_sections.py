#!/usr/bin/env python3
"""Compose direct fourth-edition section pages into their chapter pages."""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


CHAPTER_RE = re.compile(r"CLRSLean\.FourthEdition\.Chapter_[0-9][0-9]")
SECTION_TAG_RE = re.compile(r"</?section\b[^>]*>", re.IGNORECASE)
SECTION_START_RE = re.compile(r"<section\b[^>]*>", re.IGNORECASE)
MAIN_END_RE = re.compile(r"</main\s*>", re.IGNORECASE)
INLINE_MARKER = 'data-clrs-inline-chapter="true"'
ID_ATTR_RE = re.compile(
    r'(?P<prefix>\bid\s*=\s*)(?P<quote>["\'])(?P<value>[^"\']+)(?P=quote)',
    re.IGNORECASE,
)
LOCAL_HREF_RE = re.compile(
    r'(?P<prefix>\bhref\s*=\s*)(?P<quote>["\'])#(?P<value>[^"\']+)(?P=quote)',
    re.IGNORECASE,
)


@dataclass(frozen=True)
class ChapterCompositionResult:
    chapters: int
    sections: int


def section_anchor(module: str) -> str:
    """Return the stable same-page anchor for an embedded section module."""
    return "clrs-inline-" + module.replace(".", "___")


def module_page(site_root: Path, module: str) -> Path:
    return site_root.joinpath(*module.split("."), "index.html")


def _has_class(tag: str, class_name: str) -> bool:
    match = re.search(r'\bclass\s*=\s*(["\'])(.*?)\1', tag, re.IGNORECASE)
    return bool(match and class_name in match.group(2).split())


def _code_content_bounds(page_html: str, module: str) -> tuple[int, int, int, int]:
    """Locate one balanced outer ``section.code-content`` element."""
    start_match = next(
        (
            match
            for match in SECTION_START_RE.finditer(page_html)
            if _has_class(match.group(0), "code-content")
        ),
        None,
    )
    if start_match is None:
        raise ValueError(f"section page has no code-content element: {module}")

    depth = 0
    for match in SECTION_TAG_RE.finditer(page_html, start_match.start()):
        if match.group(0).lstrip().startswith("</"):
            depth -= 1
            if depth == 0:
                return (
                    start_match.start(),
                    start_match.end(),
                    match.start(),
                    match.end(),
                )
        else:
            depth += 1
    raise ValueError(f"section page has unbalanced code-content HTML: {module}")


def extract_code_content(page_html: str, module: str) -> str:
    """Extract the contents of one balanced ``section.code-content`` element."""
    _, inner_start, inner_end, _ = _code_content_bounds(page_html, module)
    return page_html[inner_start:inner_end]


def _direct_sections(parent: str, children: list[str]) -> list[str]:
    prefix = f"{parent}.Section_"
    sections = [child for child in children if child.startswith(prefix)]
    return [child for child in sections if child.count(".") == parent.count(".") + 1]


def _namespaced_id(module: str, value: str) -> str:
    return f"{section_anchor(module)}--{value}"


def _fragment_targets(content: str, outer_tag: str, module: str) -> dict[str, str]:
    targets = {
        match.group("value"): _namespaced_id(module, match.group("value"))
        for match in ID_ATTR_RE.finditer(content)
    }
    outer_id = ID_ATTR_RE.search(outer_tag)
    if outer_id is not None:
        targets[outer_id.group("value")] = section_anchor(module)
    return targets


def _namespace_section_content(
    content: str,
    module: str,
    chapter_route: str,
    fragment_targets: dict[str, str],
) -> str:
    """Keep IDs and local fragment links unique within a combined chapter page."""

    def replace_id(match: re.Match[str]) -> str:
        value = _namespaced_id(module, match.group("value"))
        return (
            f'{match.group("prefix")}{match.group("quote")}{value}'
            f'{match.group("quote")}'
        )

    def replace_href(match: re.Match[str]) -> str:
        value = fragment_targets.get(match.group("value"))
        if value is None:
            return match.group(0)
        return (
            f'{match.group("prefix")}{match.group("quote")}{chapter_route}#{value}'
            f'{match.group("quote")}'
        )

    return LOCAL_HREF_RE.sub(replace_href, ID_ATTR_RE.sub(replace_id, content))


def _rewrite_section_links(
    page_html: str,
    parent: str,
    modules: list[str],
    fragment_targets: dict[str, dict[str, str]],
) -> str:
    chapter_route = parent.replace(".", "/") + "/"
    for module in modules:
        href = module.replace(".", "/") + "/"
        anchor = section_anchor(module)
        pattern = re.compile(
            rf'href=(["\']){re.escape(href)}(?P<fragment>#[^"\']*)?\1'
        )

        def replacement(match: re.Match[str]) -> str:
            fragment = match.group("fragment")
            if fragment:
                fragment_target = fragment_targets[module].get(fragment[1:])
                if fragment_target is None:
                    return match.group(0)
                target = f"{chapter_route}#{fragment_target}"
            else:
                target = f"{chapter_route}#{anchor}"
            return f'href={match.group(1)}{target}{match.group(1)}'

        page_html = pattern.sub(replacement, page_html)
    return page_html


def compose_chapter_pages(
    site_root: Path, order_children: dict[str, list[str]]
) -> ChapterCompositionResult:
    """Embed configured direct sections in every generated fourth-edition chapter."""
    site_root = site_root.resolve()
    chapters = 0
    section_count = 0

    for parent, configured_children in order_children.items():
        if CHAPTER_RE.fullmatch(parent) is None:
            continue
        children = _direct_sections(parent, configured_children)
        if not children:
            continue

        parent_path = module_page(site_root, parent)
        if not parent_path.is_file():
            continue
        parent_html = parent_path.read_text(encoding="utf-8")
        if INLINE_MARKER in parent_html:
            continue

        chapter_route = parent.replace(".", "/") + "/"
        embedded: list[str] = []
        chapter_fragment_targets: dict[str, dict[str, str]] = {}
        for child in children:
            child_path = module_page(site_root, child)
            if not child_path.is_file():
                raise ValueError(f"section page is missing: {child_path}")
            child_html = child_path.read_text(encoding="utf-8")
            outer_start, inner_start, inner_end, _ = _code_content_bounds(
                child_html, child
            )
            content = child_html[inner_start:inner_end]
            targets = _fragment_targets(
                content, child_html[outer_start:inner_start], child
            )
            chapter_fragment_targets[child] = targets
            content = _namespace_section_content(
                content, child, chapter_route, targets
            )
            embedded.append(
                f'<section class="clrs-inline-section code-content" '
                f'id="{section_anchor(child)}" '
                f'data-module="{child}">\n{content}\n</section>'
            )

        main_ends = list(MAIN_END_RE.finditer(parent_html))
        if len(main_ends) != 1:
            raise ValueError(
                f"chapter page must contain exactly one main element: {parent_path}"
            )
        insertion = (
            f'\n<section class="clrs-inline-chapter" {INLINE_MARKER}>\n'
            + "\n".join(embedded)
            + "\n</section>\n"
        )
        _, _, parent_content_end, _ = _code_content_bounds(parent_html, parent)
        combined = (
            parent_html[:parent_content_end]
            + insertion
            + parent_html[parent_content_end:]
        )
        combined = _rewrite_section_links(
            combined, parent, children, chapter_fragment_targets
        )
        temporary = parent_path.with_name(parent_path.name + ".tmp")
        temporary.write_text(combined, encoding="utf-8", newline="")
        temporary.replace(parent_path)
        chapters += 1
        section_count += len(children)

    return ChapterCompositionResult(chapters=chapters, sections=section_count)
