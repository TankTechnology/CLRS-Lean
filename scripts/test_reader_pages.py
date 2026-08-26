"""Reader-facing source contracts for the landing and status pages."""

from __future__ import annotations

import csv
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def selected_theorem_total() -> str:
    with (ROOT / "docs" / "clrs-proof-progress.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        total = sum(int(row["tracked_key_theorems"]) for row in csv.DictReader(handle))
    return f"{total:,}"


class ReaderPageSourceTests(unittest.TestCase):
    def test_landing_page_states_the_qualified_whole_book_snapshot(self) -> None:
        landing = (ROOT / "CLRSLean.lean").read_text(encoding="utf-8")

        self.assertIn("## Whole-Book Snapshot", landing)
        self.assertIn("35 fourth-edition chapters", landing)
        self.assertIn(selected_theorem_total(), landing)
        self.assertIn("selected theorem", landing)
        self.assertIn("Lean-native trust gate", landing)

    def test_status_leads_with_the_book_before_chapter_34_detail(self) -> None:
        status = (ROOT / "CLRSLean" / "Status.lean").read_text(encoding="utf-8")

        snapshot = status.index("## Whole-Book Snapshot")
        flagship = status.index("## Chapter 34 Flagship")
        self.assertLess(snapshot, flagship)
        self.assertIn("34 chapters", status[snapshot:flagship])
        self.assertIn("Chapter 1", status[snapshot:flagship])


if __name__ == "__main__":
    unittest.main()
