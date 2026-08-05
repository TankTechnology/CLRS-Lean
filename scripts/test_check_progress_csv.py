import tempfile
import unittest
from pathlib import Path

from check_progress_csv import (
    check_dashboard_freshness,
    completed_prefix,
    load_rows,
    render_dashboard,
    sections_from_filename,
)


class SectionsFromFilenameTest(unittest.TestCase):
    def test_expands_section_range_filename(self) -> None:
        sections = sections_from_filename("Section_05_1_4_Probabilistic_Analysis.lean")

        self.assertEqual(sections, {"5.1", "5.2", "5.3", "5.4"})

    def test_compatibility_aggregator_excludes_unadvertised_section(self) -> None:
        sections = sections_from_filename("Section_27_2_4_Algorithms.lean")

        self.assertEqual(sections, {"27.2", "27.3"})


class MilestoneDashboardTest(unittest.TestCase):
    def test_renders_chapters_1_29_milestone_from_csv(self) -> None:
        dashboard = render_dashboard(load_rows())

        self.assertIn("## Chapters 1--29 Milestone", dashboard)
        self.assertIn("1,705", dashboard)
        self.assertIn("11 chapters are {lit}`main-proof-complete`", dashboard)
        self.assertIn("11 are {lit}`main-proof-complete-for-correctness`", dashboard)
        self.assertIn("6 are {lit}`selected-section-complete`", dashboard)
        self.assertIn("Chapter 1 is {lit}`expository`", dashboard)
        self.assertIn("does not mean every textbook section", dashboard)

    def test_rejects_prefix_with_unproved_tracked_entries(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[28]["proved_tracked_theorems"] = "16"

        with self.assertRaisesRegex(ValueError, "not yet proved"):
            render_dashboard(rows)

    def test_rejects_prefix_with_missing_core_groups(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[28]["missing_core_groups"] = "1"

        with self.assertRaisesRegex(ValueError, "missing core"):
            render_dashboard(rows)

    def test_rejects_prefix_with_non_completion_status(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[1]["repo_status"] = "partial"

        with self.assertRaisesRegex(ValueError, "non-complete status"):
            render_dashboard(rows)

    def test_rejects_expository_status_after_chapter_one(self) -> None:
        rows = [row.copy() for row in load_rows()]
        rows[1]["repo_status"] = "expository"

        with self.assertRaisesRegex(ValueError, "Chapter 1 alone"):
            render_dashboard(rows)

    def test_rejects_prefix_with_missing_chapter(self) -> None:
        rows = [row for row in load_rows() if row["chapter_no"] != "29"]

        with self.assertRaisesRegex(ValueError, "must cover Chapters 1–29"):
            completed_prefix(rows)


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
