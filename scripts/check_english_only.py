#!/usr/bin/env python3
"""Enforce English-only text in repository-controlled artifacts."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Sequence


CJK_PATTERN = re.compile("[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff]")


def run_git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=repo)


def tracked_paths(repo: Path) -> Iterable[Path]:
    output = run_git(repo, "ls-files", "-z")
    for raw_path in output.split(b"\0"):
        if raw_path:
            yield Path(raw_path.decode("utf-8"))


def scan_tracked_files(repo: Path) -> list[str]:
    violations: list[str] = []
    for relative_path in tracked_paths(repo):
        path = repo / relative_path
        if not path.exists():
            continue
        data = path.read_bytes()
        if b"\0" in data:
            continue
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            continue
        for line_number, line in enumerate(text.splitlines(), start=1):
            if CJK_PATTERN.search(line):
                violations.append(
                    f"{relative_path}:{line_number}: tracked text contains CJK characters"
                )
    return violations


def scan_branch_names(repo: Path) -> list[str]:
    output = run_git(
        repo, "for-each-ref", "--format=%(refname:short)", "refs/heads"
    ).decode("utf-8")
    return [
        f"branch {name}: branch name must be ASCII"
        for name in output.splitlines()
        if not name.isascii()
    ]


def scan_commit_messages(repo: Path, refs: Sequence[str] | None = None) -> list[str]:
    history_refs = list(refs) if refs else ["--all"]
    output = run_git(repo, "log", *history_refs, "--format=%H%x00%B%x00").decode(
        "utf-8", errors="replace"
    )
    fields = output.split("\0")
    violations: list[str] = []
    for index in range(0, len(fields) - 1, 2):
        commit = fields[index].strip()
        message = fields[index + 1]
        if commit and CJK_PATTERN.search(message):
            subject = message.splitlines()[0] if message.splitlines() else "<empty>"
            violations.append(
                f"commit {commit}: commit message contains CJK characters: {subject}"
            )
    return violations


def collect_violations(
    repo: Path,
    *,
    include_files: bool = True,
    include_history: bool = True,
    refs: Sequence[str] | None = None,
) -> list[str]:
    """Return deterministic English-only policy violations for ``repo``."""
    violations = scan_branch_names(repo)
    if include_files:
        violations.extend(scan_tracked_files(repo))
    if include_history:
        violations.extend(scan_commit_messages(repo, refs))
    return violations


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--ref", action="append", dest="refs")
    parser.add_argument("--skip-files", action="store_true")
    parser.add_argument("--skip-history", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    violations = collect_violations(
        args.repo.resolve(),
        include_files=not args.skip_files,
        include_history=not args.skip_history,
        refs=args.refs,
    )
    if violations:
        print("English-only repository policy violations:", file=sys.stderr)
        for violation in violations:
            print(f"  {violation}", file=sys.stderr)
        return 1
    print("English-only repository policy OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
