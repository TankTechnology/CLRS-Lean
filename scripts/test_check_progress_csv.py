import tempfile
import unittest
from pathlib import Path

import check_progress_csv
from check_progress_csv import (
    check_dashboard_freshness,
    load_rows,
    render_dashboard,
    validate,
)


class FourthEditionContractTest(unittest.TestCase):
    def test_builds_chapter_contracts_from_fourth_edition_map(self) -> None:
        self.assertTrue(hasattr(check_progress_csv, "chapter_contracts"))

        contracts = check_progress_csv.chapter_contracts()

        self.assertEqual(len(contracts), 35)
        self.assertEqual(contracts[1]["title"], "The Role of Algorithms in Computing")
        self.assertEqual(
            contracts[14]["represented_sections"],
            ("14.1", "14.2", "14.3", "14.4", "14.5"),
        )
        self.assertIsNone(contracts[14]["required_status"])
        self.assertEqual(
            contracts[25]["represented_sections"], ("25.1", "25.2", "25.3")
        )
        self.assertIsNone(contracts[25]["required_status"])
        self.assertEqual(
            contracts[25]["guide"],
            Path("CLRSLean/FourthEdition/Chapter_25.lean"),
        )

    def test_contract_counts_unresolved_sections_for_represented_chapter(self) -> None:
        contracts = check_progress_csv.chapter_contracts()

        self.assertEqual(
            contracts[3]["required_edition_gap_units"],
            sum(
                row["migration_state"] in {"partial", "not-started"}
                for row in check_progress_csv.load_map_rows()
                if row["chapter_no"] == "3"
            ),
        )

    def test_contract_records_closed_chapter_34(self) -> None:
        contracts = check_progress_csv.chapter_contracts()

        self.assertEqual(
            contracts[34]["represented_sections"],
            ("34.1", "34.2", "34.3", "34.4", "34.5"),
        )
        self.assertIsNone(contracts[34]["required_status"])
        self.assertEqual(contracts[34]["required_edition_gap_units"], 0)

    def test_contract_rejects_unknown_or_padded_migration_state(self) -> None:
        for invalid_state in ("parital", " facade "):
            with self.subTest(invalid_state=invalid_state):
                map_rows = [row.copy() for row in check_progress_csv.load_map_rows()]
                map_rows[0]["migration_state"] = invalid_state

                with self.assertRaisesRegex(SystemExit, "unknown migration_state"):
                    check_progress_csv.chapter_contracts(map_rows)

    def test_rejects_title_that_disagrees_with_fourth_edition_map(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[0]["chapter_title"] = "The Role of Algorithms"

        with self.assertRaisesRegex(SystemExit, "fourth-edition title"):
            validate(rows)

    def test_no_chapter_is_currently_not_started(self) -> None:
        # Every fourth-edition chapter 1-35 is represented on main, so the
        # validator's whole-chapter not-started branch is not exercised by the
        # live CSV (it remains defensive for future section additions).
        rows = load_rows()
        self.assertTrue(
            all(row["repo_status"] != "not-started" for row in rows)
        )

    def test_partial_chapter_must_have_positive_gap_units(self) -> None:
        # Exercise the defensive partial-row contract with a synthetic status;
        # the live ledger currently has no partial chapters.
        rows = [row.copy() for row in load_rows()]
        partial = rows[1]
        partial["repo_status"] = "partial"
        partial["edition_gap_units"] = "0"

        with self.assertRaisesRegex(SystemExit, "positive edition_gap_units"):
            validate(rows)

    def test_partial_chapter_count_must_match_edition_map(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[2]["edition_gap_units"] = "99"

        with self.assertRaisesRegex(SystemExit, "edition-map coverage-gap units"):
            validate(rows)

    def test_zero_gap_chapter_must_not_name_an_edition_gap(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[1]["remaining_edition_gaps"] = "Optional implementation refinement"

        with self.assertRaisesRegex(SystemExit, "remaining_edition_gaps=None"):
            validate(rows)

    def test_current_csv_validates_against_fourth_edition_contract(self) -> None:
        validate(load_rows())

    def test_rejects_completion_read_tracked_count_drift(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[30]["completion_read"] = (
            "The fourth-edition native source proves 17 tracked theorem groups"
        )

        with self.assertRaisesRegex(
            SystemExit, "claims tracked counts.*totaling 17"
        ):
            validate(rows)

    def test_accepts_completion_read_without_numeric_tracked_claim(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[30]["completion_read"] = "Native proof boundary documented in source"

        validate(rows)

    def test_accepts_section_breakdown_that_sums_to_chapter_total(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[30]["completion_read"] = (
            "Section 31.1 proves 7 tracked entries; "
            "Section 31.2 proves 11 tracked theorem groups"
        )

        validate(rows)

    def test_rejects_fully_proved_range_outside_represented_sections(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[30]["notes"] = "Sections 31.1-31.9 fully proved."

        with self.assertRaisesRegex(SystemExit, "fully proved section 31.9"):
            validate(rows)


class FourthEditionDashboardTest(unittest.TestCase):
    def test_opens_with_reader_facts_before_maintainer_commands(self) -> None:
        rows = load_rows()
        dashboard = render_dashboard(rows)
        opening = dashboard.split("## Fourth-Edition Snapshot", 1)[0]
        total_tracked = f"{sum(int(r['tracked_key_theorems']) for r in rows):,}"

        self.assertIn("35 fourth-edition chapters", opening)
        self.assertIn(total_tracked, opening)
        self.assertNotIn("--write-dashboard", opening)

    def test_renders_fourth_edition_snapshot_from_csv(self) -> None:
        rows = load_rows()
        dashboard = render_dashboard(rows)
        normalized = " ".join(dashboard.split())
        total_tracked = f"{sum(int(r['tracked_key_theorems']) for r in rows):,}"

        self.assertIn("## Fourth-Edition Snapshot", dashboard)
        self.assertIn("canonical CLRS fourth-edition chapter ledger", dashboard)
        self.assertIn(total_tracked, dashboard)
        self.assertIn("selected proof inventory", normalized)
        self.assertIn("does not by itself mean that every fourth-edition section obligation is covered", normalized)
        self.assertIn("{lit}`main-proof-complete`: 34 chapters", dashboard)
        self.assertNotIn("* {lit}`partial`:", dashboard)
        self.assertIn("Remaining edition-coverage units", dashboard)
        self.assertIn("Remaining edition-coverage units: 0", dashboard)
        self.assertIn("34\t34. NP-Completeness\tmain-proof-complete\t", dashboard)
        self.assertIn(
            "one unresolved section in a represented chapter", normalized
        )
        self.assertIn(
            f"{check_progress_csv.ONLINE_MATERIAL_TRACKED_THEOREMS:,}", dashboard
        )
        self.assertIn("disjoint canonical and online-material ledgers", dashboard)
        self.assertNotIn("pending declaration-level remapping", dashboard)
        self.assertNotIn("{lit}`not-started`", dashboard)
        self.assertNotIn("Chapters 1--29 Milestone", dashboard)
        self.assertNotIn("advertised proof scopes of Chapters 1--29 are complete", dashboard)

    def test_renders_chapter_matrix_as_structured_literate_input(self) -> None:
        dashboard = render_dashboard(load_rows())

        self.assertIn("CLRS-PROGRESS-MATRIX", dashboard)
        self.assertIn("Ch\tChapter\tStatus\tSections\tTracked\tGap units", dashboard)
        self.assertIn(
            "34\t34. NP-Completeness\tmain-proof-complete\t",
            dashboard,
        )
        self.assertNotIn(
            "Ch  Chapter                                                     Status",
            dashboard,
        )


class DashboardFreshnessTest(unittest.TestCase):
    def test_rejects_stale_generated_dashboard(self) -> None:
        rows = load_rows()
        with tempfile.TemporaryDirectory() as tmp:
            dashboard = Path(tmp) / "Progress.lean"
            dashboard.write_text("stale", encoding="utf-8")

            with self.assertRaisesRegex(ValueError, "out of date"):
                check_dashboard_freshness(rows, dashboard)

    def test_accepts_current_generated_dashboard(self) -> None:
        rows = load_rows()
        with tempfile.TemporaryDirectory() as tmp:
            dashboard = Path(tmp) / "Progress.lean"
            dashboard.write_text(render_dashboard(rows), encoding="utf-8")

            check_dashboard_freshness(rows, dashboard)


if __name__ == "__main__":
    unittest.main()
