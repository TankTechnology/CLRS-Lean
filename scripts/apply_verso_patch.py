#!/usr/bin/env python3
"""Apply the pinned CLRS-Lean compatibility patch to a Verso checkout."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_VERSO_DIR = ROOT / ".lake" / "packages" / "verso"
DEFAULT_PATCH = ROOT / "patches" / "verso" / "disable-inline-proof-states.patch"


class PatchError(RuntimeError):
    """The compatibility patch cannot be applied safely."""


def git_apply_check(verso_dir: Path, patch: Path, *, reverse: bool = False) -> bool:
    """Return whether Git can apply the patch in the requested direction."""
    command = ["git", "-C", str(verso_dir), "apply"]
    if reverse:
        command.append("--reverse")
    command.extend(["--check", str(patch)])
    result = subprocess.run(command, capture_output=True, text=True, check=False)
    return result.returncode == 0


def revision(verso_dir: Path) -> str:
    """Return the dependency revision when available for an actionable error."""
    result = subprocess.run(
        ["git", "-C", str(verso_dir), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def apply_verso_patch(verso_dir: Path, patch: Path) -> str:
    """Apply the patch once, returning ``applied`` or ``already-applied``."""
    if not verso_dir.is_dir():
        raise PatchError(f"Verso checkout does not exist: {verso_dir}")
    if not patch.is_file():
        raise PatchError(f"Verso patch does not exist: {patch}")

    if git_apply_check(verso_dir, patch):
        subprocess.run(
            ["git", "-C", str(verso_dir), "apply", str(patch)],
            check=True,
        )
        return "applied"

    if git_apply_check(verso_dir, patch, reverse=True):
        return "already-applied"

    raise PatchError(
        "incompatible Verso source at revision "
        f"{revision(verso_dir)}; review {patch} against the pinned dependency"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verso-dir", type=Path, default=DEFAULT_VERSO_DIR)
    parser.add_argument("--patch", type=Path, default=DEFAULT_PATCH)
    args = parser.parse_args()
    try:
        print(apply_verso_patch(args.verso_dir.resolve(), args.patch.resolve()))
    except (PatchError, subprocess.CalledProcessError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
