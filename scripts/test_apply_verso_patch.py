#!/usr/bin/env python3
"""Tests for the pinned Verso compatibility-patch applicator."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "apply_verso_patch.py"
PATCHES = (
    ROOT / "patches" / "verso" / "disable-inline-proof-states.patch",
    ROOT / "patches" / "verso" / "sharded-literate-html.patch",
)
TARGET = Path("src/verso-literate-html/LiterateHtmlMain.lean")


def upstream_source() -> str:
    checkout = ROOT / ".lake" / "packages" / "verso"
    result = subprocess.run(
        ["git", "-C", str(checkout), "show", f"HEAD:{TARGET.as_posix()}"],
        text=True,
        capture_output=True,
        check=True,
    )
    return result.stdout


def initialize_verso_checkout(root: Path, source: str | None = None) -> Path:
    verso = root / "verso"
    target = verso / TARGET
    target.parent.mkdir(parents=True)
    target.write_text(source if source is not None else upstream_source(), encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=verso, check=True)
    subprocess.run(["git", "add", str(TARGET)], cwd=verso, check=True)
    subprocess.run(
        [
            "git",
            "-c",
            "user.name=CLRS-Lean Tests",
            "-c",
            "user.email=tests@example.invalid",
            "commit",
            "--quiet",
            "-m",
            "fixture",
        ],
        cwd=verso,
        check=True,
    )
    return verso


def run_script(
    verso_dir: Path, patches: tuple[Path, ...] | None = None
) -> subprocess.CompletedProcess[str]:
    patch_args = [] if patches is None else [arg for patch in patches for arg in ("--patch", str(patch))]
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--verso-dir",
            str(verso_dir),
            *patch_args,
        ],
        text=True,
        capture_output=True,
        check=False,
    )


class ApplyVersoPatchTests(unittest.TestCase):
    def test_applies_both_patches_in_order(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            verso = initialize_verso_checkout(Path(tmp))
            result = run_script(verso)
            rendered = (verso / TARGET).read_text(encoding="utf-8")

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(
            [f"{patch.name}: applied" for patch in PATCHES],
            result.stdout.splitlines(),
        )
        self.assertIn("codeOptions := { inlineProofStates := false }", rendered)
        self.assertIn('"--emit-list" :: path :: rest', rendered)
        self.assertIn("config.emitsSharedOutput", rendered)

    def test_second_application_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            verso = initialize_verso_checkout(Path(tmp))
            first = run_script(verso)
            first_text = (verso / TARGET).read_text(encoding="utf-8")
            second = run_script(verso)
            second_text = (verso / TARGET).read_text(encoding="utf-8")

        self.assertEqual(0, first.returncode, first.stderr)
        self.assertEqual(0, second.returncode, second.stderr)
        self.assertEqual(
            [f"{patch.name}: already-applied" for patch in PATCHES],
            second.stdout.splitlines(),
        )
        self.assertEqual(first_text, second_text)

    def test_reports_the_incompatible_patch(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            source = upstream_source().replace(
                "def emitDir (outDir : System.FilePath) (dir : Dir)",
                "def emitEveryDir (outDir : System.FilePath) (dir : Dir)",
            )
            verso = initialize_verso_checkout(
                Path(tmp),
                source,
            )
            result = run_script(verso)

        self.assertEqual(1, result.returncode)
        self.assertIn("sharded-literate-html.patch", result.stderr)
        self.assertIn("incompatible Verso source", result.stderr)

    def test_explicit_patch_list_is_supported(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            verso = initialize_verso_checkout(Path(tmp))
            result = run_script(verso, (PATCHES[0],))

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(
            [f"{PATCHES[0].name}: applied"],
            result.stdout.splitlines(),
        )

    def test_reports_missing_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            missing = Path(tmp) / "missing-verso"
            result = run_script(missing)

        self.assertEqual(1, result.returncode)
        self.assertIn("Verso checkout does not exist", result.stderr)


if __name__ == "__main__":
    unittest.main()
