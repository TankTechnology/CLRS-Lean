#!/usr/bin/env python3
"""Trim generated Verso HTML for fast static-page delivery.

Verso's literate pages contain editor-grade metadata: hover bindings for many
tokens and full tactic states after proof steps. That is useful in small files,
but long proof chapters can become too large for browsers to parse smoothly.
This post-processing step keeps the rendered Lean code and anchors, while
removing heavyweight proof-state DOM and editor attributes from large pages.
"""

from __future__ import annotations

import argparse
import html
import os
import re
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path
from typing import Iterable, TextIO


VOID_ELEMENTS = {
    "area",
    "base",
    "br",
    "col",
    "embed",
    "hr",
    "img",
    "input",
    "link",
    "meta",
    "param",
    "source",
    "track",
    "wbr",
}

EDITOR_ATTRS = {"data-verso-hover", "data-binding"}
HOVER_SCRIPT_SRCS = {"popper.js", "tippy.js", "marked.js"}
HOVER_STYLESHEET_HREFS = {"tippy-border.css"}
RAW_TEXT_ELEMENTS = {"script", "style"}
VERSO_HOVER_SCRIPT_RE = re.compile(
    r"\s*<script>\s*window\.onload = async \(\) => \{.*?</script>",
    re.DOTALL,
)
BODY_END_RE = re.compile(r"</body\s*>", re.IGNORECASE)
NAV_STATE_SCRIPT_ID = "clrs-nav-state-script"
NAV_STATE_SCRIPT = r"""
<script id="clrs-nav-state-script">
(() => {
  const STATE_KEY = "clrs.nav.state.v1";
  const SCROLL_KEY = "clrs.nav.scroll.v1";

  function readJson(key, fallback) {
    try {
      const raw = sessionStorage.getItem(key);
      return raw ? JSON.parse(raw) : fallback;
    } catch (_err) {
      return fallback;
    }
  }

  function writeJson(key, value) {
    try {
      sessionStorage.setItem(key, JSON.stringify(value));
    } catch (_err) {
      /* Storage can be unavailable in private or locked-down contexts. */
    }
  }

  function navKey(details, index) {
    const link = details.querySelector(":scope > summary a");
    return link?.getAttribute("title") || link?.getAttribute("href") || `nav-${index}`;
  }

  document.addEventListener("DOMContentLoaded", () => {
    const nav = document.querySelector(".module-tree");
    if (!nav) return;

    const detailsList = Array.from(nav.querySelectorAll("details"));
    const savedState = readJson(STATE_KEY, null);

    detailsList.forEach((details, index) => {
      const key = navKey(details, index);
      details.dataset.clrsNavKey = key;
      if (savedState && Object.prototype.hasOwnProperty.call(savedState, key)) {
        details.open = Boolean(savedState[key]);
      } else {
        details.open = true;
      }
    });

    const current = nav.querySelector(".current");
    let parent = current?.closest("details");
    while (parent) {
      parent.open = true;
      parent = parent.parentElement?.closest("details");
    }

    function saveState() {
      const state = {};
      for (const details of detailsList) {
        state[details.dataset.clrsNavKey] = details.open;
      }
      writeJson(STATE_KEY, state);
    }

    for (const details of detailsList) {
      details.addEventListener("toggle", saveState);
    }

    const scrollCandidates = [
      document.querySelector(".sidebar"),
      document.querySelector(".sidebar-content"),
      nav.parentElement,
    ].filter(Boolean);
    const scrollHost =
      scrollCandidates.find((el) => el.scrollHeight > el.clientHeight) ||
      scrollCandidates[0];

    if (!scrollHost) return;

    const savedScroll = readJson(SCROLL_KEY, null);
    if (typeof savedScroll === "number") {
      scrollHost.scrollTop = savedScroll;
    } else if (current) {
      current.scrollIntoView({ block: "nearest" });
    }

    let scrollQueued = false;
    function saveScroll() {
      scrollQueued = false;
      writeJson(SCROLL_KEY, scrollHost.scrollTop);
    }

    scrollHost.addEventListener(
      "scroll",
      () => {
        if (scrollQueued) return;
        scrollQueued = true;
        requestAnimationFrame(saveScroll);
      },
      { passive: true },
    );
    window.addEventListener("pagehide", saveScroll);
  });
})();
</script>
""".strip()


@dataclass
class PageStats:
    before_bytes: int
    after_bytes: int
    tactic_states: int
    tactic_toggles: int
    tactic_classes: int
    stripped_attrs: int
    deferred_scripts: int
    removed_hover_scripts: int
    removed_hover_stylesheets: int
    removed_inline_hover_scripts: int
    injected_nav_scripts: int
    opened_nav_details: int

    @property
    def changed(self) -> bool:
        return (
            self.tactic_states > 0
            or self.tactic_toggles > 0
            or self.tactic_classes > 0
            or self.stripped_attrs > 0
            or self.deferred_scripts > 0
            or self.removed_hover_scripts > 0
            or self.removed_hover_stylesheets > 0
            or self.removed_inline_hover_scripts > 0
            or self.injected_nav_scripts > 0
            or self.opened_nav_details > 0
        )


def attr_value(attrs: list[tuple[str, str | None]], attr_name: str) -> str | None:
    attr_name = attr_name.lower()
    for name, value in attrs:
        if name.lower() == attr_name:
            return value
    return None


def has_attr(attrs: list[tuple[str, str | None]], attr_name: str) -> bool:
    attr_name = attr_name.lower()
    return any(name.lower() == attr_name for name, _ in attrs)


def asset_name(value: str | None) -> str | None:
    if not value:
        return None
    return value.split("?", 1)[0].split("#", 1)[0].rstrip("/").rsplit("/", 1)[-1]


def has_class(attrs: list[tuple[str, str | None]], class_name: str) -> bool:
    for name, value in attrs:
        if name.lower() == "class" and value:
            return class_name in value.split()
    return False


class VersoHtmlOptimizer(HTMLParser):
    def __init__(self, out: TextIO, strip_editor_attrs: bool, disable_hover_features: bool) -> None:
        super().__init__(convert_charrefs=False)
        self.out = out
        self.strip_editor_attrs = strip_editor_attrs
        self.disable_hover_features = disable_hover_features
        self.skip_depth = 0
        self.raw_text_depth = 0
        self.tactic_states = 0
        self.tactic_toggles = 0
        self.tactic_classes = 0
        self.stripped_attrs = 0
        self.deferred_scripts = 0
        self.removed_hover_scripts = 0
        self.removed_hover_stylesheets = 0
        self.opened_nav_details = 0
        self.module_tree_depth = 0

    def _attrs(self, tag: str, attrs: list[tuple[str, str | None]]) -> str:
        script_src = attr_value(attrs, "src")
        if tag.lower() == "script" and script_src and not has_attr(attrs, "defer"):
            if (
                attr_value(attrs, "type") != "module"
                and not has_attr(attrs, "async")
                and asset_name(script_src) not in HOVER_SCRIPT_SRCS
            ):
                attrs = [*attrs, ("defer", "defer")]
                self.deferred_scripts += 1

        rendered: list[str] = []
        for name, value in attrs:
            lname = name.lower()
            if lname == "class" and value:
                classes = value.split()
                if "tactic" in classes:
                    self.tactic_classes += 1
                    classes = [cls for cls in classes if cls != "tactic"]
                    if not classes:
                        continue
                    value = " ".join(classes)
            if self.strip_editor_attrs and lname in EDITOR_ATTRS:
                self.stripped_attrs += 1
                continue
            if lname == "for" and value and value.startswith("tactic-state-"):
                self.stripped_attrs += 1
                continue
            if value is None:
                rendered.append(f" {name}")
            else:
                rendered.append(f' {name}="{html.escape(value, quote=True)}"')
        return "".join(rendered)

    def _start(self, tag: str, attrs: list[tuple[str, str | None]], closed: bool) -> None:
        close = " /" if closed else ""
        self.out.write(f"<{tag}{self._attrs(tag, attrs)}{close}>")

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        ltag = tag.lower()
        if self.skip_depth:
            if ltag not in VOID_ELEMENTS:
                self.skip_depth += 1
            return
        entering_module_tree = ltag == "nav" and has_class(attrs, "module-tree")
        if self.module_tree_depth and ltag == "details" and not has_attr(attrs, "open"):
            attrs = [*attrs, ("open", None)]
            self.opened_nav_details += 1
        if self.disable_hover_features:
            if ltag == "script" and asset_name(attr_value(attrs, "src")) in HOVER_SCRIPT_SRCS:
                self.removed_hover_scripts += 1
                self.skip_depth = 1
                return
            if ltag == "link" and asset_name(attr_value(attrs, "href")) in HOVER_STYLESHEET_HREFS:
                self.removed_hover_stylesheets += 1
                return
        if ltag == "span" and has_class(attrs, "tactic-state"):
            self.tactic_states += 1
            self.skip_depth = 1
            return
        if ltag == "input" and has_class(attrs, "tactic-toggle"):
            self.tactic_toggles += 1
            return
        self._start(tag, attrs, closed=False)
        if entering_module_tree:
            self.module_tree_depth = 1
        elif self.module_tree_depth and ltag not in VOID_ELEMENTS:
            self.module_tree_depth += 1
        if ltag in RAW_TEXT_ELEMENTS:
            self.raw_text_depth += 1

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        ltag = tag.lower()
        if self.skip_depth:
            return
        if self.disable_hover_features:
            if ltag == "script" and asset_name(attr_value(attrs, "src")) in HOVER_SCRIPT_SRCS:
                self.removed_hover_scripts += 1
                return
            if ltag == "link" and asset_name(attr_value(attrs, "href")) in HOVER_STYLESHEET_HREFS:
                self.removed_hover_stylesheets += 1
                return
        if ltag == "span" and has_class(attrs, "tactic-state"):
            self.tactic_states += 1
            return
        if ltag == "input" and has_class(attrs, "tactic-toggle"):
            self.tactic_toggles += 1
            return
        self._start(tag, attrs, closed=True)

    def handle_endtag(self, tag: str) -> None:
        ltag = tag.lower()
        if self.skip_depth:
            self.skip_depth -= 1
            return
        self.out.write(f"</{tag}>")
        if self.module_tree_depth:
            self.module_tree_depth -= 1
        if ltag in RAW_TEXT_ELEMENTS and self.raw_text_depth:
            self.raw_text_depth -= 1

    def handle_data(self, data: str) -> None:
        if self.skip_depth:
            return
        if self.raw_text_depth:
            self.out.write(data)
        else:
            self.out.write(html.escape(data, quote=False))

    def handle_entityref(self, name: str) -> None:
        if not self.skip_depth:
            self.out.write(f"&{name};")

    def handle_charref(self, name: str) -> None:
        if not self.skip_depth:
            self.out.write(f"&#{name};")

    def handle_comment(self, data: str) -> None:
        if not self.skip_depth:
            self.out.write(f"<!--{data}-->")

    def handle_decl(self, decl: str) -> None:
        if not self.skip_depth:
            self.out.write(f"<!{decl}>")

    def handle_pi(self, data: str) -> None:
        if not self.skip_depth:
            self.out.write(f"<?{data}>")

    def unknown_decl(self, data: str) -> None:
        if not self.skip_depth:
            self.out.write(f"<![{data}]>")


def iter_html_files(paths: Iterable[Path]) -> Iterable[Path]:
    for path in paths:
        if path.is_file() and path.suffix == ".html":
            yield path
        elif path.is_dir():
            yield from sorted(path.rglob("*.html"))


def inject_nav_state_script(text: str) -> tuple[str, int]:
    if "module-tree" not in text or NAV_STATE_SCRIPT_ID in text:
        return text, 0
    next_text, count = BODY_END_RE.subn(f"{NAV_STATE_SCRIPT}\n</body>", text, count=1)
    return next_text, min(count, 1)


def optimize_file(path: Path, strip_attrs_min_bytes: int) -> PageStats:
    before = path.stat().st_size
    strip_editor_attrs = before >= strip_attrs_min_bytes
    disable_hover_features = strip_editor_attrs
    tmp = path.with_name(path.name + ".tmp")

    with path.open("r", encoding="utf-8", errors="replace") as src, tmp.open(
        "w", encoding="utf-8", newline=""
    ) as out:
        parser = VersoHtmlOptimizer(
            out,
            strip_editor_attrs=strip_editor_attrs,
            disable_hover_features=disable_hover_features,
        )
        while True:
            chunk = src.read(1024 * 1024)
            if not chunk:
                break
            parser.feed(chunk)
        parser.close()

    removed_inline_hover_scripts = 0
    if disable_hover_features:
        text = tmp.read_text(encoding="utf-8", errors="replace")
        text, removed_inline_hover_scripts = VERSO_HOVER_SCRIPT_RE.subn("", text, count=1)
        if removed_inline_hover_scripts:
            tmp.write_text(text, encoding="utf-8", newline="")

    text = tmp.read_text(encoding="utf-8", errors="replace")
    text, injected_nav_scripts = inject_nav_state_script(text)
    if injected_nav_scripts:
        tmp.write_text(text, encoding="utf-8", newline="")

    after = tmp.stat().st_size
    stats = PageStats(
        before_bytes=before,
        after_bytes=after,
        tactic_states=parser.tactic_states,
        tactic_toggles=parser.tactic_toggles,
        tactic_classes=parser.tactic_classes,
        stripped_attrs=parser.stripped_attrs,
        deferred_scripts=parser.deferred_scripts,
        removed_hover_scripts=parser.removed_hover_scripts,
        removed_hover_stylesheets=parser.removed_hover_stylesheets,
        removed_inline_hover_scripts=removed_inline_hover_scripts,
        injected_nav_scripts=injected_nav_scripts,
        opened_nav_details=parser.opened_nav_details,
    )

    if stats.changed:
        os.replace(tmp, path)
    else:
        tmp.unlink()
        stats.after_bytes = before
    return stats


def fmt_size(size: int) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if size < 1024 or unit == "GB":
            return f"{size:.1f} {unit}" if unit != "B" else f"{size} B"
        size /= 1024
    return f"{size} B"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="+",
        type=Path,
        help="HTML file or directory to optimize in place.",
    )
    parser.add_argument(
        "--strip-attrs-min-bytes",
        type=int,
        default=1_000_000,
        help="Strip editor hover/binding attributes only from pages at least this large.",
    )
    args = parser.parse_args()

    total_before = 0
    total_after = 0
    changed = 0
    files = 0
    for file in iter_html_files(args.paths):
        files += 1
        stats = optimize_file(file, args.strip_attrs_min_bytes)
        total_before += stats.before_bytes
        total_after += stats.after_bytes
        if stats.changed:
            changed += 1
            print(
                f"optimized {file}: {fmt_size(stats.before_bytes)} -> "
                f"{fmt_size(stats.after_bytes)} "
                f"(tactic states: {stats.tactic_states}, "
                f"toggles: {stats.tactic_toggles}, "
                f"tactic classes: {stats.tactic_classes}, "
                f"attrs: {stats.stripped_attrs}, "
                f"deferred scripts: {stats.deferred_scripts}, "
                f"hover scripts: {stats.removed_hover_scripts}, "
                f"hover stylesheets: {stats.removed_hover_stylesheets}, "
                f"inline hover scripts: {stats.removed_inline_hover_scripts}, "
                f"nav scripts: {stats.injected_nav_scripts}, "
                f"opened nav details: {stats.opened_nav_details})"
            )

    print(
        f"Processed {files} HTML files; changed {changed}; "
        f"saved {fmt_size(total_before - total_after)}."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
