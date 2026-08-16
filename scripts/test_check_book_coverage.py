#!/usr/bin/env python3
"""Tests for the formalization-to-book coverage checker."""

from __future__ import annotations

import csv
import tempfile
import unittest
from pathlib import Path

import check_book_coverage
from check_book_coverage import (
    MAP_HEADER,
    PROGRESS_HEADER,
    check_gap_integrity,
    check_section_coverage,
    check_status_consistency,
    check_theorem_accounting,
    closure_declared,
    collect_errors,
    extract_section_refs,
    split_source_modules,
)


def map_row(
    chapter: str,
    section: str,
    state: str = "native",
    source: str = "none",
    note: str = "coverage note",
    title: str = "Chapter",
) -> dict[str, str]:
    return {
        "chapter_no": chapter,
        "section_no": section,
        "chapter_title": title,
        "section_title": f"Section {section}",
        "migration_state": state,
        "source_modules": source,
        "legacy_location": "legacy",
        "coverage_note": note,
    }


def progress_row(
    chapter: str,
    status: str = "main-proof-complete",
    tracked: str = "1",
    proved: str = "1",
    gaps: str = "0",
    remaining: str = "None",
    title: str = "Chapter",
) -> dict[str, str]:
    return {
        "chapter_no": chapter,
        "chapter_title": title,
        "repo_status": status,
        "represented_sections": f"{chapter}.1",
        "tracked_key_theorems": tracked,
        "proved_tracked_theorems": proved,
        "edition_gap_units": gaps,
        "completion_read": "completion",
        "proved_key_theorem_groups": "groups",
        "remaining_edition_gaps": remaining,
        "evidence_source": "CLRSLean file tree",
        "notes": "notes",
    }


def write_csv(path: Path, header: list[str], rows: list[dict[str, str]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=header)
        writer.writeheader()
        writer.writerows(rows)


class SplitSourceModulesTest(unittest.TestCase):
    def test_drops_none_and_blank(self) -> None:
        self.assertEqual(
            split_source_modules("CLRSLean.Foo; none; ; CLRSLean.Bar"),
            ["CLRSLean.Foo", "CLRSLean.Bar"],
        )


class SectionRefTest(unittest.TestCase):
    def test_extracts_section_numbers(self) -> None:
        self.assertEqual(
            extract_section_refs("pending are Section 34.5 and 3.2, see 34.4"),
            {(34, 5), (3, 2), (34, 4)},
        )

    def test_ignores_out_of_range_chapters(self) -> None:
        self.assertEqual(extract_section_refs("version 99.1 and 0.3"), set())


class ClosureDeclaredTest(unittest.TestCase):
    def test_follows_imports_once(self) -> None:
        index = {
            "CLRSLean.A": (2, frozenset({"CLRSLean.B"})),
            "CLRSLean.B": (3, frozenset({"CLRSLean.C"})),
            "CLRSLean.C": (5, frozenset()),
        }
        self.assertEqual(closure_declared(index, {"CLRSLean.A"}), 10)

    def test_ignores_missing_and_non_clrs_imports(self) -> None:
        index = {"CLRSLean.A": (2, frozenset({"CLRSLean.Missing"}))}
        self.assertEqual(closure_declared(index, {"CLRSLean.A"}), 2)


class SectionCoverageTest(unittest.TestCase):
    def test_flags_missing_mapped_source(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "CLRSLean" / "FourthEdition").mkdir(parents=True)
            rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Missing")]
            errors = check_section_coverage(root, rows, {})
            self.assertTrue(any("mapped source module does not exist" in e for e in errors))

    def test_flags_orphan_top_level_section_module(self) -> None:
        index = {
            "CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort": (3, frozenset())
        }
        # Map has no row naming that section module.
        errors = check_section_coverage(Path("."), [], index)
        self.assertIn(
            "orphan FourthEdition section module has no edition-map row: "
            "CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort",
            errors,
        )

    def test_does_not_flag_nested_or_non_section_modules(self) -> None:
        index = {
            "CLRSLean.FourthEdition.Chapter_13.WellFormed": (1, frozenset()),
            "CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge": (
                1,
                frozenset(),
            ),
        }
        self.assertEqual(check_section_coverage(Path("."), [], index), [])


class TheoremAccountingTest(unittest.TestCase):
    def test_flags_tracked_without_declared_heads(self) -> None:
        index = {"CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort": (0, frozenset())}
        rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort")]
        progress = [progress_row("2", tracked="7", proved="7")]
        errors, _ = check_theorem_accounting(rows, progress, index)
        self.assertTrue(any("declare no theorem/lemma heads" in e for e in errors))

    def test_flags_declared_heads_without_tracking(self) -> None:
        index = {"CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort": (9, frozenset())}
        rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort")]
        progress = [progress_row("2", tracked="0", proved="0")]
        errors, _ = check_theorem_accounting(rows, progress, index)
        self.assertTrue(any("tracked_key_theorems is 0" in e for e in errors))

    def test_flags_proved_exceeding_tracked(self) -> None:
        index = {"CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort": (9, frozenset())}
        rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort")]
        progress = [progress_row("2", tracked="5", proved="6")]
        errors, _ = check_theorem_accounting(rows, progress, index)
        self.assertTrue(any("exceeds tracked_key_theorems" in e for e in errors))

    def test_expository_zero_theorems_not_flagged(self) -> None:
        index = {}
        rows = [map_row("1", "1.1", source="CLRSLean.FourthEdition.Chapter_01")]
        progress = [progress_row("1", status="expository", tracked="0", proved="0")]
        errors, _ = check_theorem_accounting(rows, progress, index)
        self.assertEqual(errors, [])


class GapIntegrityTest(unittest.TestCase):
    def test_flags_not_started_section_with_source(self) -> None:
        index = {"CLRSLean.Chapter_34": (3, frozenset())}
        rows = [map_row("34", "34.5", state="not-started", source="CLRSLean.Chapter_34")]
        progress = [progress_row("34", status="partial", tracked="0", proved="0", gaps="2")]
        errors = check_gap_integrity(rows, progress, index)
        self.assertTrue(any("not-started section 34.5 has a theorem-bearing source" in e for e in errors))

    def test_flags_stale_gap_reference_to_complete_section(self) -> None:
        rows = [
            map_row("34", "34.4", state="partial", source="CLRSLean.Chapter_34", note="remaining work"),
            map_row("34", "34.5", state="not-started", source="none", note="no source"),
        ]
        progress = [progress_row("34", status="partial", tracked="0", proved="0", gaps="2", remaining="Section 34.1 pending")]
        errors = check_gap_integrity(rows, progress, {})
        self.assertTrue(any("gap prose references section 34.1 which is not a gap" in e for e in errors))

    def test_flags_missing_record_for_not_started_section(self) -> None:
        rows = [map_row("34", "34.5", state="not-started", source="none", note="no source")]
        progress = [progress_row("34", status="partial", tracked="0", proved="0", gaps="1", remaining="some other work")]
        errors = check_gap_integrity(rows, progress, {})
        self.assertTrue(any("not-started section 34.5 has no gap record" in e for e in errors))

    def test_accepts_consistent_gap_records(self) -> None:
        rows = [
            map_row("34", "34.4", state="partial", source="CLRSLean.Chapter_34", note="Section 34.5 pending"),
            map_row("34", "34.5", state="not-started", source="none", note="no source yet"),
        ]
        progress = [progress_row("34", status="partial", tracked="20", proved="20", gaps="2", remaining="Section 34.5 not represented")]
        self.assertEqual(check_gap_integrity(rows, progress, {}), [])


class StatusConsistencyTest(unittest.TestCase):
    def test_complete_requires_proved_equal_tracked(self) -> None:
        rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort")]
        progress = [progress_row("2", tracked="7", proved="6")]
        errors = check_status_consistency(rows, progress, {2: 20})
        self.assertTrue(any("main-proof-complete but proved" in e for e in errors))

    def test_complete_requires_zero_gaps(self) -> None:
        rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort")]
        progress = [progress_row("2", tracked="7", proved="7", gaps="1")]
        errors = check_status_consistency(rows, progress, {2: 20})
        self.assertTrue(any("edition_gap_units = 1" in e for e in errors))

    def test_expository_must_declare_no_theorems(self) -> None:
        rows = [map_row("1", "1.1", source="CLRSLean.FourthEdition.Chapter_01")]
        progress = [progress_row("1", status="expository", tracked="0", proved="0")]
        errors = check_status_consistency(rows, progress, {1: 3})
        self.assertTrue(any("expository chapter declares 3" in e for e in errors))

    def test_partial_requires_a_map_gap(self) -> None:
        rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort")]
        progress = [progress_row("2", status="partial", tracked="7", proved="7", gaps="1")]
        errors = check_status_consistency(rows, progress, {2: 20})
        self.assertTrue(any("partial but the edition map has no" in e for e in errors))

    def test_consistent_complete_chapter_is_clean(self) -> None:
        rows = [map_row("2", "2.1", source="CLRSLean.FourthEdition.Chapter_02.Section_02_1_Insertion_Sort")]
        progress = [progress_row("2", tracked="7", proved="7", gaps="0")]
        self.assertEqual(check_status_consistency(rows, progress, {2: 20}), [])


class CollectErrorsIntegrationTest(unittest.TestCase):
    def test_collect_errors_runs_on_live_repo(self) -> None:
        # The checker must run end-to-end on the real checkout without raising.
        errors, declared, map_rows, progress_rows = collect_errors(
            check_book_coverage.ROOT
        )
        self.assertEqual(len(declared), 35)
        self.assertTrue(map_rows)
        self.assertTrue(progress_rows)
        self.assertIsInstance(errors, list)


if __name__ == "__main__":
    unittest.main()
