#!/usr/bin/env python3
"""Elaborate the per-chapter v1 flagship trust surfaces.

The default invocation is the release gate and requires Chapter 1 through 35.
During staged development, ``--chapters LOW-HIGH`` checks one contiguous band.
"""

from __future__ import annotations

import argparse
import re
import shlex
import subprocess
import sys
from collections.abc import Callable, Sequence
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TRUST_DIR = Path("tests") / "Trust"
CHAPTER_NAME_RE = re.compile(r"Chapter_(\d{2})\.lean")
CHAPTER_RANGE_RE = re.compile(r"(\d+)-(\d+)")

CommandRunner = Callable[[list[str], Path], int]


class TrustGateError(RuntimeError):
    """A structural or Lean elaboration failure in the trust gate."""


def parse_chapter_range(raw: str) -> tuple[int, int]:
    """Parse and validate an inclusive chapter range."""
    match = CHAPTER_RANGE_RE.fullmatch(raw)
    if match is None:
        raise TrustGateError(f"invalid chapter range {raw!r}; expected LOW-HIGH")
    low, high = (int(part) for part in match.groups())
    if not 1 <= low <= high <= 35:
        raise TrustGateError(
            f"invalid chapter range {raw!r}; require 1 <= LOW <= HIGH <= 35"
        )
    return low, high


def validate_chapter_files(root: Path, low: int, high: int) -> list[Path]:
    """Require exactly named files for ``low..high`` and return numeric order."""
    if not 1 <= low <= high <= 35:
        raise TrustGateError("chapter bounds must satisfy 1 <= low <= high <= 35")

    trust_dir = root / TRUST_DIR
    if not trust_dir.is_dir():
        raise TrustGateError(f"missing trust directory: {TRUST_DIR}")

    for path in sorted(trust_dir.glob("Chapter_*.lean")):
        match = CHAPTER_NAME_RE.fullmatch(path.name)
        if match is None or not 1 <= int(match.group(1)) <= 35:
            raise TrustGateError(f"unexpected chapter filename: {path.name}")

    expected = [trust_dir / f"Chapter_{chapter:02d}.lean" for chapter in range(low, high + 1)]
    missing = [path.name for path in expected if not path.is_file()]
    if missing:
        raise TrustGateError(f"missing chapter trust files: {', '.join(missing)}")
    return expected


def _run_command(command: list[str], root: Path) -> int:
    return subprocess.run(command, cwd=root, check=False).returncode


def run_audits(
    root: Path,
    chapter_files: Sequence[Path],
    *,
    command_runner: CommandRunner = _run_command,
) -> None:
    """Build the audit command, test it, and elaborate each chapter file."""
    axiom_audit = root / TRUST_DIR / "AxiomAudit.lean"
    if not axiom_audit.is_file():
        raise TrustGateError(f"missing command audit: {axiom_audit.relative_to(root)}")

    relative_chapters = [path.relative_to(root) for path in chapter_files]
    commands = [
        ["lake", "build", "CLRSLean.Audit.Axioms"],
        ["lake", "env", "lean", str(axiom_audit.relative_to(root))],
        *[["lake", "env", "lean", str(path)] for path in relative_chapters],
    ]
    for command in commands:
        print(f"==> {shlex.join(command)}", flush=True)
        returncode = command_runner(command, root)
        if returncode != 0:
            target = command[-1]
            raise TrustGateError(f"trust command failed for {target} with exit {returncode}")


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--chapters",
        default="1-35",
        metavar="LOW-HIGH",
        help="inclusive chapter band to check (default: 1-35)",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        low, high = parse_chapter_range(args.chapters)
        chapter_files = validate_chapter_files(ROOT, low, high)
        run_audits(ROOT, chapter_files)
    except TrustGateError as error:
        print(f"v1 trust gate failed: {error}", file=sys.stderr)
        return 1
    print(f"V1 trust gate passed for Chapters {low:02d}-{high:02d}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
