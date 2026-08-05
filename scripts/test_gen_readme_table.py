import unittest

import gen_readme_table


class MilestoneSummaryTest(unittest.TestCase):
    def test_renders_complete_prefix_without_claiming_full_textbook_coverage(self) -> None:
        rows = [
            {
                "chapter_no": "1",
                "repo_status": "expository",
                "tracked_key_theorems": "0",
                "proved_tracked_theorems": "0",
                "missing_core_groups": "0",
            },
            {
                "chapter_no": "2",
                "repo_status": "selected-section-complete",
                "tracked_key_theorems": "7",
                "proved_tracked_theorems": "7",
                "missing_core_groups": "0",
            },
        ]

        self.assertTrue(hasattr(gen_readme_table, "build_milestone_block"))
        block = gen_readme_table.build_milestone_block(rows, last_chapter=2)

        self.assertIn("Chapters 1–2", block)
        self.assertIn("7 tracked theorem entries", block)
        self.assertIn("zero remaining core theorem groups", block)
        self.assertIn("does not claim every textbook section", block)

    def test_rejects_prefix_with_unproved_tracked_entries(self) -> None:
        rows = [
            {
                "chapter_no": "1",
                "repo_status": "expository",
                "tracked_key_theorems": "0",
                "proved_tracked_theorems": "0",
                "missing_core_groups": "0",
            },
            {
                "chapter_no": "2",
                "repo_status": "main-proof-complete",
                "tracked_key_theorems": "1",
                "proved_tracked_theorems": "0",
                "missing_core_groups": "0",
            }
        ]

        with self.assertRaisesRegex(ValueError, "not yet proved"):
            gen_readme_table.build_milestone_block(rows, last_chapter=2)


if __name__ == "__main__":
    unittest.main()
