import tempfile
import unittest
from pathlib import Path
from unittest import mock

import check_status_claims


def write(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


def make_map(rows: list[str]) -> str:
    header = (
        "chapter_no,section_no,chapter_title,section_title,migration_state,"
        "source_modules,legacy_location,coverage_note\n"
    )
    return header + "\n".join(rows) + "\n"


class ParseChapterRangesTest(unittest.TestCase):
    def test_single_chapter_with_title(self) -> None:
        self.assertEqual(check_status_claims.parse_chapter_ranges("Chapter 27, Online Algorithms"), [27])

    def test_closed_range(self) -> None:
        self.assertEqual(check_status_claims.parse_chapter_ranges("Chapters 28--32"), [28, 29, 30, 31, 32])

    def test_range_with_title(self) -> None:
        self.assertEqual(check_status_claims.parse_chapter_ranges("Chapters 34--35, foo"), [34, 35])

    def test_non_matching(self) -> None:
        self.assertEqual(check_status_claims.parse_chapter_ranges("Fourth-edition guide"), [])


class MigrationNoneChaptersTest(unittest.TestCase):
    def test_extracts_none_and_coverage(self) -> None:
        text = """## Chapter mapping during the facade period

| Fourth-edition guide | Current theorem-bearing source | Migration note |
| --- | --- | --- |
| Chapter 1, One | `CLRSLean.Chapter_01` | Same chapter number. |
| Chapters 2--3 | none | Not started. |
"""
        none_chapters, covered = check_status_claims.migration_none_chapters(text)
        self.assertEqual(none_chapters, {2, 3})
        self.assertEqual(covered, {1, 2, 3})


def full_map(states: dict[int, str], default: str = "native") -> list[dict[str, str]]:
    return [
        {"chapter_no": str(i), "migration_state": states.get(i, default)}
        for i in range(1, 36)
    ]


def full_migration(none_chapters: set[int]) -> str:
    lines = [
        "## Chapter mapping during the facade period",
        "",
        "| Fourth-edition guide | Current theorem-bearing source | Migration note |",
        "| --- | --- | --- |",
    ]
    for i in range(1, 36):
        source = "none" if i in none_chapters else f"`CLRSLean.Chapter_{i:02d}`"
        lines.append(f"| Chapter {i}, X | {source} | Note. |")
    return "\n".join(lines) + "\n"


class MigrationNotesCheckTest(unittest.TestCase):
    def test_flags_none_that_should_be_started(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            migrations = Path(tmp) / "clrs4.md"
            write(migrations, full_migration({1}))
            with mock.patch.object(check_status_claims, "MIGRATIONS_PATH", migrations):
                errors: list[str] = []
                check_status_claims.check_migration_notes(errors, full_map({}))
            self.assertIn(
                "migrations/clrs4.md lists chapter 1 as 'none' but the edition map has started sections for it",
                errors,
            )

    def test_accepts_consistent_none(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            migrations = Path(tmp) / "clrs4.md"
            write(migrations, full_migration({1}))
            with mock.patch.object(check_status_claims, "MIGRATIONS_PATH", migrations):
                errors: list[str] = []
                check_status_claims.check_migration_notes(errors, full_map({1: "not-started"}))
            self.assertEqual(errors, [])


class GapCountsCheckTest(unittest.TestCase):
    def test_flags_mismatched_gap_units(self) -> None:
        map_rows = [
            {"chapter_no": "1", "migration_state": "partial"},
            {"chapter_no": "1", "migration_state": "not-started"},
        ]
        progress_rows = [{"chapter_no": "1", "edition_gap_units": "0"}]
        errors: list[str] = []
        check_status_claims.check_gap_counts(errors, map_rows, progress_rows)
        self.assertIn(
            "chapter 1: edition_gap_units=0 but the edition map has 2 partial/not-started sections",
            errors,
        )


if __name__ == "__main__":
    unittest.main()
