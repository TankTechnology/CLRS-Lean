"""Reader-facing navigation policy for generated Verso pages."""

from __future__ import annotations

import html
import re
from dataclasses import dataclass
from html.parser import HTMLParser


CHAPTER_MODULE_RE = re.compile(r"Chapter_[0-9][0-9]")
MODULE_TREE_RE = re.compile(
    r"<nav\b[^>]*\bclass=(?:\"[^\"]*\bmodule-tree\b[^\"]*\"|'[^']*\bmodule-tree\b[^']*')[^>]*>.*?</nav>",
    re.IGNORECASE | re.DOTALL,
)
VOID_ELEMENTS = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}


def is_reader_sidebar_module(module_name: str) -> bool:
    """Return whether a Lean module belongs in the reader-facing sidebar."""
    parts = module_name.split(".")
    if parts == ["CLRSLean"]:
        return True
    if len(parts) == 2 and parts[0] == "CLRSLean":
        return True
    return (
        len(parts) == 3
        and parts[0] == "CLRSLean"
        and CHAPTER_MODULE_RE.fullmatch(parts[1]) is not None
        and parts[2].startswith("Section_")
    )


@dataclass(frozen=True)
class SidebarRewrite:
    """The rewritten page and an audit trail of navigation changes."""

    html: str
    removed_modules: tuple[str, ...]
    flattened_modules: tuple[str, ...]
    unclassified_hrefs: tuple[str, ...]


@dataclass
class _Text:
    value: str
    raw: bool = False


@dataclass
class _Element:
    tag: str
    attrs: list[tuple[str, str | None]]
    children: list[_Element | _Text]
    self_closing: bool = False


class _ModuleTreeParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self.root = _Element("", [], [])
        self.stack = [self.root]

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        element = _Element(tag, attrs, [])
        self.stack[-1].children.append(element)
        if tag.lower() not in VOID_ELEMENTS:
            self.stack.append(element)

    def handle_startendtag(
        self, tag: str, attrs: list[tuple[str, str | None]]
    ) -> None:
        self.stack[-1].children.append(_Element(tag, attrs, [], self_closing=True))

    def handle_endtag(self, tag: str) -> None:
        if len(self.stack) == 1 or self.stack[-1].tag.lower() != tag.lower():
            raise ValueError(f"unbalanced module-tree HTML at </{tag}>")
        self.stack.pop()

    def handle_data(self, data: str) -> None:
        self.stack[-1].children.append(_Text(data))

    def handle_entityref(self, name: str) -> None:
        self.stack[-1].children.append(_Text(f"&{name};", raw=True))

    def handle_charref(self, name: str) -> None:
        self.stack[-1].children.append(_Text(f"&#{name};", raw=True))

    def handle_comment(self, data: str) -> None:
        self.stack[-1].children.append(_Text(f"<!--{data}-->", raw=True))

    def close(self) -> None:
        super().close()
        if len(self.stack) != 1:
            raise ValueError(f"unclosed module-tree element: <{self.stack[-1].tag}>")


def _attr(element: _Element, name: str) -> str | None:
    for attr_name, value in element.attrs:
        if attr_name.lower() == name.lower():
            return value
    return None


def _classes(element: _Element) -> list[str]:
    value = _attr(element, "class")
    return value.split() if value else []


def _is_nav_owner(element: _Element) -> bool:
    return element.tag.lower() == "details" or (
        element.tag.lower() == "div" and "leaf" in _classes(element)
    )


def _direct_child(element: _Element, tag: str) -> _Element | None:
    for child in element.children:
        if isinstance(child, _Element) and child.tag.lower() == tag.lower():
            return child
    return None


def _owner_anchor(element: _Element) -> tuple[_Element | None, _Element | None]:
    if element.tag.lower() == "details":
        summary = _direct_child(element, "summary")
        return summary, _direct_child(summary, "a") if summary else None
    return None, _direct_child(element, "a")


def _render(node: _Element | _Text) -> str:
    if isinstance(node, _Text):
        return node.value if node.raw else html.escape(node.value, quote=False)
    if not node.tag:
        return "".join(_render(child) for child in node.children)
    attrs = []
    for name, value in node.attrs:
        if value is None:
            attrs.append(f" {name}")
        else:
            attrs.append(f' {name}="{html.escape(value, quote=True)}"')
    close = " /" if node.self_closing else ""
    start = f"<{node.tag}{''.join(attrs)}{close}>"
    if node.self_closing or node.tag.lower() in VOID_ELEMENTS:
        return start
    return f"{start}{''.join(_render(child) for child in node.children)}</{node.tag}>"


class _SidebarPruner:
    def __init__(self) -> None:
        self.removed_modules: list[str] = []
        self.flattened_modules: list[str] = []
        self.unclassified_hrefs: list[str] = []

    def rewrite_container(self, element: _Element) -> None:
        rewritten: list[_Element | _Text] = []
        for child in element.children:
            if not isinstance(child, _Element):
                rewritten.append(child)
                continue
            if _is_nav_owner(child):
                replacement = self.rewrite_owner(child)
                if replacement is not None:
                    rewritten.append(replacement)
            else:
                self.rewrite_container(child)
                rewritten.append(child)
        element.children = rewritten

    def rewrite_owner(self, element: _Element) -> _Element | None:
        summary, anchor = _owner_anchor(element)
        module_name = _attr(anchor, "title") if anchor else None
        if not module_name:
            href = _attr(anchor, "href") if anchor else None
            if href:
                self.unclassified_hrefs.append(href)
            self.rewrite_container(element)
            return element
        if not is_reader_sidebar_module(module_name):
            self.removed_modules.append(module_name)
            return None

        self.rewrite_container(element)
        if element.tag.lower() != "details":
            return element
        if any(
            isinstance(child, _Element) and _is_nav_owner(child)
            for child in element.children
        ):
            return element

        assert summary is not None and anchor is not None
        leaf_classes = ["leaf"]
        if "current" in _classes(summary):
            leaf_classes.append("current")
        self.flattened_modules.append(module_name)
        return _Element("div", [("class", " ".join(leaf_classes))], [anchor])


def prune_reader_sidebar(document: str) -> SidebarRewrite:
    """Prune one generated `.module-tree` without changing other page markup."""
    match = MODULE_TREE_RE.search(document)
    if match is None:
        return SidebarRewrite(document, (), (), ())

    parser = _ModuleTreeParser()
    parser.feed(match.group(0))
    parser.close()
    nav = next(
        (
            child
            for child in parser.root.children
            if isinstance(child, _Element) and child.tag.lower() == "nav"
        ),
        None,
    )
    if nav is None:
        return SidebarRewrite(document, (), (), ())

    pruner = _SidebarPruner()
    pruner.rewrite_container(nav)
    changed = bool(pruner.removed_modules or pruner.flattened_modules)
    if changed:
        fragment = _render(nav)
        document = f"{document[:match.start()]}{fragment}{document[match.end():]}"
    return SidebarRewrite(
        document,
        tuple(pruner.removed_modules),
        tuple(pruner.flattened_modules),
        tuple(pruner.unclassified_hrefs),
    )
