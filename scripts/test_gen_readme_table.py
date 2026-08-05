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
                "missing_core_groups": "0",
            },
            {
                "chapter_no": "2",
                "repo_status": "partial",
                "represented_sections": "2.1",
                "tracked_key_theorems": "7",
                "proved_tracked_theorems": "6",
                "missing_core_groups": "1",
            },
            {
                "chapter_no": "3",
                "repo_status": "not-started",
                "represented_sections": "None",
                "tracked_key_theorems": "0",
                "proved_tracked_theorems": "0",
                "missing_core_groups": "1",
            },
        ]

        self.assertTrue(hasattr(gen_readme_table, "build_snapshot_block"))
        block = gen_readme_table.build_snapshot_block(
            rows, online_material_theorems=421
        )

        self.assertIn("fourth-edition", block)
        self.assertIn("2 of 3 chapters", block)
        self.assertIn("6 proved source-inventory entries", block)
        self.assertIn("421 additional", block)
        self.assertIn("facade-level counts are not", block)
        self.assertIn("a count of distinct fourth-edition", block)
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
                "missing_core_groups": "1",
                "remaining_core_groups": "Whole chapter pending",
            },
        ]

        self.assertTrue(hasattr(gen_readme_table, "build_block_from_rows"))
        block = gen_readme_table.build_block_from_rows(rows)

        self.assertIn("| 35 | Approximation Algorithms | ⬜ not started |", block)


if __name__ == "__main__":
    unittest.main()
