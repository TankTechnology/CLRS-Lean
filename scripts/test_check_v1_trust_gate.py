#!/usr/bin/env python3
"""Unit tests for the v1 flagship trust-gate runner."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from check_v1_trust_gate import TrustGateError, run_audits, validate_chapter_files


def write_chapter(root: Path, chapter: int) -> Path:
    trust_dir = root / "tests" / "Trust"
    trust_dir.mkdir(parents=True, exist_ok=True)
    path = trust_dir / f"Chapter_{chapter:02d}.lean"
    path.write_text("example : True := by trivial\n", encoding="utf-8")
    return path


class ChapterFileValidationTest(unittest.TestCase):
    def test_rejects_missing_chapter_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_chapter(root, 1)

            with self.assertRaisesRegex(TrustGateError, r"Chapter_02\.lean"):
                validate_chapter_files(root, 1, 2)

    def test_rejects_unexpected_chapter_filename(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_chapter(root, 1)
            bad = root / "tests" / "Trust" / "Chapter_1.lean"
            bad.write_text("example : True := by trivial\n", encoding="utf-8")

            with self.assertRaisesRegex(TrustGateError, r"Chapter_1\.lean"):
                validate_chapter_files(root, 1, 1)

    def test_returns_chapters_in_deterministic_numeric_order(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for chapter in (3, 1, 2):
                write_chapter(root, chapter)

            files = validate_chapter_files(root, 1, 3)

            self.assertEqual(
                [path.name for path in files],
                ["Chapter_01.lean", "Chapter_02.lean", "Chapter_03.lean"],
            )


class LeanInvocationTest(unittest.TestCase):
    def test_propagates_lean_failure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            chapter = write_chapter(root, 1)
            (root / "tests" / "Trust" / "AxiomAudit.lean").write_text(
                "example : True := by trivial\n", encoding="utf-8"
            )
            calls: list[tuple[str, ...]] = []

            def fail_chapter(command: list[str], _root: Path) -> int:
                calls.append(tuple(command))
                return 9 if command[-1] == str(chapter.relative_to(root)) else 0

            with self.assertRaisesRegex(TrustGateError, r"Chapter_01\.lean.*exit 9"):
                run_audits(root, [chapter], command_runner=fail_chapter)

            self.assertEqual(calls[-1][-1], "tests/Trust/Chapter_01.lean")


if __name__ == "__main__":
    unittest.main()
