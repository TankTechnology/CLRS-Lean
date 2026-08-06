import unittest

import gen_readme_table


class FourthEditionSummaryTest(unittest.TestCase):
    def test_renders_snapshot_without_requiring_a_completed_prefix(self) -> None:
        rows = [
            {
                "chapter_no": "1",
                "repo_status": "expository",
                "represented_sections": "Chapter_01",
                "tracked_key_theorems": "0",
                "proved_tracked_theorems": "0",
                "edition_gap_units": "0",
            },
            {
                "chapter_no": "2",
                "repo_status": "partial",
                "represented_sections": "2.1",
                "tracked_key_theorems": "7",
                "proved_tracked_theorems": "6",
                "edition_gap_units": "1",
            },
            {
                "chapter_no": "3",
                "repo_status": "not-started",
                "represented_sections": "None",
                "tracked_key_theorems": "0",
                "proved_tracked_theorems": "0",
                "edition_gap_units": "1",
            },
        ]

        self.assertTrue(hasattr(gen_readme_table, "build_snapshot_block"))
        block = gen_readme_table.build_snapshot_block(
            rows, online_material_theorems=467
        )

        self.assertIn("fourth-edition", block)
        self.assertIn("2 of 3 chapters", block)
        self.assertIn("6 / 7 selected source-inventory entries are proved", block)
        self.assertIn("selected inventory", block)
        self.assertIn("not a claim of complete fourth-edition section coverage", block)
        self.assertIn("467 additional", block)
        self.assertIn("disjoint from the canonical chapter counts", block)
        self.assertNotIn("pending declaration-level remapping", block)
        self.assertNotIn("Milestone", block)

    def test_progress_table_keeps_not_started_rows_visible(self) -> None:
        rows = [
            {
                "chapter_no": "35",
                "chapter_title": "Approximation Algorithms",
                "repo_status": "not-started",
                "represented_sections": "None",
                "tracked_key_theorems": "0",
                "proved_tracked_theorems": "0",
                "edition_gap_units": "1",
                "remaining_edition_gaps": "Whole chapter pending",
            },
        ]

        self.assertTrue(hasattr(gen_readme_table, "build_block_from_rows"))
        block = gen_readme_table.build_block_from_rows(rows)

        self.assertIn("| 35 | Approximation Algorithms | ⬜ not started |", block)

    def test_progress_table_labels_partial_as_edition_coverage(self) -> None:
        rows = [
            {
                "chapter_no": "3",
                "chapter_title": "Characterizing Running Times",
                "repo_status": "partial",
                "represented_sections": "3.1; 3.2; 3.3",
                "tracked_key_theorems": "47",
                "proved_tracked_theorems": "46",
                "edition_gap_units": "1",
                "remaining_edition_gaps": "One fourth-edition obligation remains",
            },
        ]

        block = gen_readme_table.build_block_from_rows(rows)

        self.assertIn("| Proved / tracked |", block)
        self.assertIn("🟠 partial coverage | 46 / 47 |", block)
        self.assertIn("46 of 47 selected theorem entries have kernel-checked proofs", block)
        self.assertIn("does not by itself claim complete fourth-edition coverage", block)


if __name__ == "__main__":
    unittest.main()
