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
PATCH = ROOT / "patches" / "verso" / "disable-inline-proof-states.patch"
TARGET = Path("src/verso-literate-html/LiterateHtmlMain.lean")

UNPATCHED_SOURCE = """private def renderModBody := do
  let emitCtx := { ctx with
    options := {}
    traverseContext := { currentModule := mod.name }
    codeOptions := {}
  }
  let hlCtx : HighlightHtmlM.Context Literate := { emitCtx with options := emitCtx.codeOptions }
"""


def initialize_verso_checkout(root: Path, source: str = UNPATCHED_SOURCE) -> Path:
    verso = root / "verso"
    target = verso / TARGET
    target.parent.mkdir(parents=True)
    target.write_text(source, encoding="utf-8")
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


def run_script(verso_dir: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--verso-dir",
            str(verso_dir),
            "--patch",
            str(PATCH),
        ],
        text=True,
        capture_output=True,
        check=False,
    )


class ApplyVersoPatchTests(unittest.TestCase):
    def test_applies_patch_to_expected_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            verso = initialize_verso_checkout(Path(tmp))
            result = run_script(verso)
            rendered = (verso / TARGET).read_text(encoding="utf-8")

        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual("applied", result.stdout.strip())
        self.assertIn("codeOptions := { inlineProofStates := false }", rendered)

    def test_second_application_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            verso = initialize_verso_checkout(Path(tmp))
            first = run_script(verso)
            first_text = (verso / TARGET).read_text(encoding="utf-8")
            second = run_script(verso)
            second_text = (verso / TARGET).read_text(encoding="utf-8")

        self.assertEqual(0, first.returncode, first.stderr)
        self.assertEqual(0, second.returncode, second.stderr)
        self.assertEqual("already-applied", second.stdout.strip())
        self.assertEqual(first_text, second_text)

    def test_rejects_incompatible_upstream_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            verso = initialize_verso_checkout(
                Path(tmp),
                UNPATCHED_SOURCE.replace("codeOptions := {}", "codeOptions := customOptions"),
            )
            result = run_script(verso)

        self.assertEqual(1, result.returncode)
        self.assertIn("incompatible Verso source", result.stderr)

    def test_reports_missing_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            missing = Path(tmp) / "missing-verso"
            result = run_script(missing)

        self.assertEqual(1, result.returncode)
        self.assertIn("Verso checkout does not exist", result.stderr)


if __name__ == "__main__":
    unittest.main()
