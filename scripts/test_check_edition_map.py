#!/usr/bin/env python3
"""Tests for the CLRS fourth-edition map contract."""

from __future__ import annotations

import csv
import tempfile
import unittest
from pathlib import Path

from check_edition_map import MAP_HEADER, ONLINE_HEADER, validate_repository


TITLES = {
    1: "The Role of Algorithms in Computing",
    2: "Getting Started",
}


class EditionMapTests(unittest.TestCase):
    def read_rows(self, path: Path) -> list[dict[str, str]]:
        with path.open(encoding="utf-8") as handle:
            return list(csv.DictReader(handle))

    def make_repo(self) -> Path:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        (root / "docs").mkdir()
        (root / "CLRSLean" / "FourthEdition").mkdir(parents=True)
        (root / "CLRSLean" / "Legacy.lean").write_text(
            "/-! Legacy online material. -/\n", encoding="utf-8"
        )
        (root / "CLRSLean" / "OnlineMaterial.lean").write_text(
            "import CLRSLean.Legacy\n", encoding="utf-8"
        )

        with (root / "docs" / "clrs-fourth-edition-map.csv").open(
            "w", newline="", encoding="utf-8"
        ) as handle:
            writer = csv.DictWriter(handle, fieldnames=MAP_HEADER)
            writer.writeheader()
            for chapter in range(1, 36):
                title = TITLES.get(chapter, f"Chapter {chapter}")
                writer.writerow(
                    {
                        "chapter_no": chapter,
                        "section_no": "none",
                        "chapter_title": title,
                        "section_title": "Chapter guide",
                        "migration_state": "not-started",
                        "source_modules": "none",
                        "legacy_location": "none",
                        "coverage_note": "No canonical theorem module yet.",
                    }
                )
                (root / "CLRSLean" / "FourthEdition" / f"Chapter_{chapter:02d}.lean").write_text(
                    f"/-! # Chapter {chapter} — {title}\n-/\n", encoding="utf-8"
                )
            writer.writerow(
                {
                    "chapter_no": 0,
                    "section_no": "online:legacy",
                    "chapter_title": "Online and Supplementary Material",
                    "section_title": "Legacy topic",
                    "migration_state": "online-material",
                    "source_modules": "CLRSLean.Legacy",
                    "legacy_location": "CLRS third edition online material",
                    "coverage_note": "Retained outside the fourth-edition main text.",
                }
            )

        with (root / "docs" / "clrs-online-material.csv").open(
            "w", newline="", encoding="utf-8"
        ) as handle:
            writer = csv.DictWriter(handle, fieldnames=ONLINE_HEADER)
            writer.writeheader()
            writer.writerow(
                {
                    "topic_id": "legacy",
                    "title": "Legacy topic",
                    "source_modules": "CLRSLean.Legacy",
                    "legacy_location": "CLRS third edition online material",
                    "tracked_key_theorems": 1,
                    "coverage_note": "Retained outside the fourth-edition main text.",
                }
            )

        progress_header = ["chapter_no", "chapter_title", "tracked_key_theorems"]
        with (root / "docs" / "clrs-proof-progress.csv").open(
            "w", newline="", encoding="utf-8"
        ) as handle:
            writer = csv.DictWriter(handle, fieldnames=progress_header)
            writer.writeheader()
            for chapter in range(1, 36):
                writer.writerow(
                    {
                        "chapter_no": chapter,
                        "chapter_title": TITLES.get(chapter, f"Chapter {chapter}"),
                        "tracked_key_theorems": 0,
                    }
                )
        return root

    def test_valid_repository_has_no_errors(self) -> None:
        self.assertEqual([], validate_repository(self.make_repo()))

    def test_requires_all_35_chapters(self) -> None:
        root = self.make_repo()
        path = root / "docs" / "clrs-fourth-edition-map.csv"
        rows = [row for row in self.read_rows(path) if row["chapter_no"] != "35"]
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=MAP_HEADER)
            writer.writeheader()
            writer.writerows(rows)
        self.assertIn("map chapters must be exactly 1..35", "\n".join(validate_repository(root)))

    def test_rejects_duplicate_chapter_section(self) -> None:
        root = self.make_repo()
        path = root / "docs" / "clrs-fourth-edition-map.csv"
        rows = self.read_rows(path)
        rows.append(rows[0])
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=MAP_HEADER)
            writer.writeheader()
            writer.writerows(rows)
        self.assertIn("duplicate map key 1/none", "\n".join(validate_repository(root)))

    def test_mapped_source_must_exist(self) -> None:
        root = self.make_repo()
        path = root / "docs" / "clrs-fourth-edition-map.csv"
        rows = self.read_rows(path)
        rows[0]["migration_state"] = "facade"
        rows[0]["source_modules"] = "CLRSLean.Missing"
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=MAP_HEADER)
            writer.writeheader()
            writer.writerows(rows)
        self.assertIn("source module does not exist: CLRSLean.Missing", "\n".join(validate_repository(root)))

    def test_not_started_progress_must_have_zero_theorems(self) -> None:
        root = self.make_repo()
        path = root / "docs" / "clrs-proof-progress.csv"
        rows = self.read_rows(path)
        rows[24]["tracked_key_theorems"] = "1"
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)
        self.assertIn(
            "chapter 25 is not-started but tracks 1 theorems",
            "\n".join(validate_repository(root)),
        )

    def test_titles_must_match_map_progress_and_guide(self) -> None:
        root = self.make_repo()
        progress = root / "docs" / "clrs-proof-progress.csv"
        rows = self.read_rows(progress)
        rows[0]["chapter_title"] = "Wrong"
        with progress.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)
        errors = "\n".join(validate_repository(root))
        self.assertIn("chapter 1 title differs between map and progress", errors)

    def test_online_material_import_must_be_machine_cataloged(self) -> None:
        root = self.make_repo()
        (root / "CLRSLean" / "Extra.lean").write_text(
            "/-! Extra material. -/\n", encoding="utf-8"
        )
        (root / "CLRSLean" / "OnlineMaterial.lean").write_text(
            "import CLRSLean.Legacy\nimport CLRSLean.Extra\n", encoding="utf-8"
        )

        errors = "\n".join(validate_repository(root))

        self.assertIn("online-material import is not cataloged: CLRSLean.Extra", errors)

    def test_online_ledger_must_match_online_map_rows(self) -> None:
        root = self.make_repo()
        path = root / "docs" / "clrs-fourth-edition-map.csv"
        rows = self.read_rows(path)
        rows = [row for row in rows if row["migration_state"] != "online-material"]
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=MAP_HEADER)
            writer.writeheader()
            writer.writerows(rows)

        errors = "\n".join(validate_repository(root))

        self.assertIn("online ledger source is absent from edition map: CLRSLean.Legacy", errors)


if __name__ == "__main__":
    unittest.main()
