#!/usr/bin/env python3
"""Run fast repository-wide metadata, documentation, and policy checks."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

CHECK_SCRIPTS = [
    "scripts/check_progress_csv.py",
    "scripts/check_site_consistency.py",
    "scripts/test_literate_config.py",
    "scripts/test_optimize_literate_html.py",
]


def run_script(path: str) -> None:
    print(f"==> {path}", flush=True)
    subprocess.run([sys.executable, path], cwd=ROOT, check=True)


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace Lean comments and string contents while preserving token spacing."""
    output: list[str] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False

    while i < len(text):
        pair = text[i : i + 2]

        if in_line_comment:
            if text[i] == "\n":
                in_line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            i += 1
            continue

        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                i += 2
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                output.extend("  ")
                i += 2
            elif text[i] == '"':
                in_string = False
                output.append(" ")
                i += 1
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        if pair == "--":
            in_line_comment = True
            output.extend("  ")
            i += 2
        elif pair == "/-":
            block_depth = 1
            output.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            output.append(" ")
            i += 1
        else:
            output.append(text[i])
            i += 1

    if block_depth:
        raise SystemExit("Unclosed Lean block comment encountered during placeholder scan")
    return "".join(output)


def check_lean_placeholders() -> None:
    print("==> Lean placeholder policy", flush=True)
    pattern = re.compile(r"\b(sorry|admit|axiom)\b")
    errors: list[str] = []
    for source_root in (ROOT / "CLRSLean", ROOT / "Tests"):
        for path in sorted(source_root.rglob("*.lean")):
            code = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
            for match in pattern.finditer(code):
                line = code.count("\n", 0, match.start()) + 1
                errors.append(f"{path.relative_to(ROOT)}:{line}: {match.group(1)}")
    if errors:
        raise SystemExit("Lean placeholders found:\n  " + "\n  ".join(errors))
    print("Lean placeholder policy OK")


def check_markdown_links() -> None:
    print("==> Markdown local links", flush=True)
    link_pattern = re.compile(r"(?<!!)\[[^\]]+\]\(([^)]+)\)")
    markdown_files = [ROOT / "README.md", *sorted((ROOT / "docs").rglob("*.md"))]
    errors: list[str] = []

    for path in markdown_files:
        text = path.read_text(encoding="utf-8")
        for match in link_pattern.finditer(text):
            target = match.group(1).strip()
            if target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            target_path = target.split("#", 1)[0]
            if not target_path:
                continue
            resolved = (path.parent / target_path).resolve()
            if not resolved.exists():
                line = text.count("\n", 0, match.start()) + 1
                errors.append(f"{path.relative_to(ROOT)}:{line}: {target}")

    if errors:
        raise SystemExit("Broken Markdown links found:\n  " + "\n  ".join(errors))
    print("Markdown local links OK")


def main() -> int:
    for script in CHECK_SCRIPTS:
        run_script(script)
    check_lean_placeholders()
    check_markdown_links()
    print("Repository checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
