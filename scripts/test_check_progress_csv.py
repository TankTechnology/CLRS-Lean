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

    def test_rejects_title_that_disagrees_with_fourth_edition_map(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[0]["chapter_title"] = "The Role of Algorithms"

        with self.assertRaisesRegex(SystemExit, "fourth-edition title"):
            validate(rows)

    def test_not_started_chapter_must_have_zero_canonical_theorems(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[33]["tracked_key_theorems"] = "1"
        rows[33]["proved_tracked_theorems"] = "1"

        with self.assertRaisesRegex(SystemExit, "zero tracked theorem"):
            validate(rows)

    def test_partial_chapter_must_name_a_missing_core_group(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[2]["missing_core_groups"] = "0"

        with self.assertRaisesRegex(SystemExit, "positive missing_core_groups"):
            validate(rows)

    def test_current_csv_validates_against_fourth_edition_contract(self) -> None:
        validate(load_rows())


class FourthEditionDashboardTest(unittest.TestCase):
    def test_renders_fourth_edition_snapshot_from_csv(self) -> None:
        dashboard = render_dashboard(load_rows())

        self.assertIn("## Fourth-Edition Snapshot", dashboard)
        self.assertIn("canonical CLRS fourth-edition chapter ledger", dashboard)
        self.assertIn("1,326", dashboard)
        self.assertIn("467", dashboard)
        self.assertIn("disjoint canonical and online-material ledgers", dashboard)
        self.assertNotIn("pending declaration-level remapping", dashboard)
        self.assertIn("{lit}`not-started`: 5 chapters", dashboard)
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
