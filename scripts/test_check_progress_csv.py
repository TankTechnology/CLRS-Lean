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
        self.assertEqual(contracts[14]["required_status"], "partial")
        self.assertEqual(contracts[25]["represented_sections"], ())
        self.assertEqual(contracts[25]["required_status"], "not-started")
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

    def test_contract_collapses_wholly_unrepresented_chapter_to_one_unit(self) -> None:
        contracts = check_progress_csv.chapter_contracts()

        self.assertEqual(contracts[25]["required_edition_gap_units"], 1)

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

    def test_not_started_chapter_must_have_zero_canonical_theorems(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[34]["tracked_key_theorems"] = "1"
        rows[34]["proved_tracked_theorems"] = "1"

        with self.assertRaisesRegex(SystemExit, "zero tracked theorem"):
            validate(rows)

    def test_partial_chapter_must_have_positive_gap_units(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[2]["edition_gap_units"] = "0"

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


class FourthEditionDashboardTest(unittest.TestCase):
    def test_renders_fourth_edition_snapshot_from_csv(self) -> None:
        dashboard = render_dashboard(load_rows())
        normalized = " ".join(dashboard.split())

        self.assertIn("## Fourth-Edition Snapshot", dashboard)
        self.assertIn("canonical CLRS fourth-edition chapter ledger", dashboard)
        self.assertIn("1,331", dashboard)
        self.assertIn("selected proof inventory", normalized)
        self.assertIn("does not by itself mean that every fourth-edition section obligation is covered", normalized)
        self.assertIn("partial (edition coverage)", dashboard)
        self.assertIn("Remaining edition-coverage units", dashboard)
        self.assertIn(
            "one unresolved section in a represented chapter", normalized
        )
        self.assertIn("467", dashboard)
        self.assertIn("disjoint canonical and online-material ledgers", dashboard)
        self.assertNotIn("pending declaration-level remapping", dashboard)
        self.assertIn("{lit}`not-started`: 4 chapters", dashboard)
        self.assertNotIn("Chapters 1--29 Milestone", dashboard)
        self.assertNotIn("advertised proof scopes of Chapters 1--29 are complete", dashboard)


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
