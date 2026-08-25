#!/usr/bin/env python3
"""Cross-validate chapter metadata against the canonical ledgers.

The single source of truth for chapter completion is the pair

  - ``docs/clrs-proof-progress.csv``   (chapter status, tracked/proved counts, gaps)
  - ``docs/clrs-fourth-edition-map.csv`` (section migration states and coverage)

When a chapter is completed or a gap is closed, these ledgers are updated and
the generated views are refreshed by
``check_progress_csv.py --write-dashboard`` and ``gen_readme_table.py``.

Checks
  1. ``docs/migrations/clrs4.md`` chapter-mapping table: a chapter whose
     theorem-bearing source is listed as ``none`` must be exactly the set of
     chapters whose edition-map sections are all ``not-started``.
  2. Gap counts: per chapter, the number of ``partial``/``not-started`` edition
     map sections must equal the CSV ``edition_gap_units`` field (defence in
     depth; also asserted by ``check_progress_csv.py``).

Run from the repository root:
    python3 scripts/check_status_claims.py
"""

from __future__ import annotations

import csv
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

MAP_PATH = ROOT / "docs" / "clrs-fourth-edition-map.csv"
PROGRESS_PATH = ROOT / "docs" / "clrs-proof-progress.csv"
MIGRATIONS_PATH = ROOT / "docs" / "migrations" / "clrs4.md"

STARTED_STATES = {"native", "facade", "partial"}


def load_map() -> list[dict[str, str]]:
    if not MAP_PATH.is_file():
        raise SystemExit("missing file: docs/clrs-fourth-edition-map.csv")
    with MAP_PATH.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def load_progress() -> list[dict[str, str]]:
    if not PROGRESS_PATH.is_file():
        raise SystemExit("missing file: docs/clrs-proof-progress.csv")
    with PROGRESS_PATH.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def map_started_chapters(map_rows: list[dict[str, str]]) -> set[int]:
    """Chapters with at least one native/facade/partial section."""
    started: set[int] = set()
    for row in map_rows:
        chapter = int(row["chapter_no"])
        if chapter == 0:
            continue
        if row["migration_state"].strip() in STARTED_STATES:
            started.add(chapter)
    return started


def parse_chapter_ranges(cell: str) -> list[int]:
    """Extract chapter numbers from a migration-table leading cell.

    Accepts ``Chapter N, Title`` and ``Chapters N--M`` (and plain ``Chapters
    N--M, Title``).  Returns the inclusive list of chapter numbers.
    """
    numbers: list[int] = []
    match = re.match(r"^Chapters?\s+(\d+)\s*(?:--\s*(\d+))?", cell.strip())
    if match is None:
        return numbers
    low = int(match.group(1))
    high = int(match.group(2)) if match.group(2) else low
    return list(range(low, high + 1))


def migration_none_chapters(text: str) -> set[int]:
    """Chapters whose theorem-bearing source is ``none`` in the mapping table."""
    none_chapters: set[int] = set()
    covered: set[int] = set()
    in_mapping_table = False
    for line in text.splitlines():
        if re.match(r"^## Chapter mapping", line):
            in_mapping_table = True
            continue
        if in_mapping_table and re.match(r"^## ", line):
            break
        if not in_mapping_table:
            continue
        if not line.strip().startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2:
            continue
        if cells[0].startswith("---") or cells[0] == "Fourth-edition guide":
            continue
        chapters = parse_chapter_ranges(cells[0])
        if not chapters:
            continue
        covered.update(chapters)
        if cells[1] == "none":
            none_chapters.update(chapters)
    return none_chapters, covered


def check_migration_notes(errors: list[str], map_rows: list[dict[str, str]]) -> None:
    text = MIGRATIONS_PATH.read_text(encoding="utf-8")
    none_chapters, covered = migration_none_chapters(text)
    started = map_started_chapters(map_rows)
    expected_none = set(range(1, 36)) - started
    if covered != set(range(1, 36)):
        missing = sorted(set(range(1, 36)) - covered)
        errors.append(
            "migrations/clrs4.md chapter-mapping table does not cover chapters: "
            + ", ".join(map(str, missing))
        )
    if none_chapters != expected_none:
        wrong_none = sorted(none_chapters - expected_none)
        for chapter in wrong_none:
            errors.append(
                f"migrations/clrs4.md lists chapter {chapter} as 'none' but the "
                "edition map has started sections for it"
            )
        missing_none = sorted(expected_none - none_chapters)
        for chapter in missing_none:
            errors.append(
                f"migrations/clrs4.md does not list chapter {chapter} as 'none' "
                "but the edition map has no started sections for it"
            )


def check_gap_counts(errors: list[str], map_rows: list[dict[str, str]], progress_rows: list[dict[str, str]]) -> None:
    by_chapter: dict[int, list[dict[str, str]]] = {}
    for row in map_rows:
        chapter = int(row["chapter_no"])
        if chapter == 0:
            continue
        by_chapter.setdefault(chapter, []).append(row)
    progress_by_chapter = {int(r["chapter_no"]): r for r in progress_rows}
    for chapter, rows in by_chapter.items():
        gap_sections = [
            r for r in rows if r["migration_state"].strip() in {"partial", "not-started"}
        ]
        expected = len(gap_sections)
        progress = progress_by_chapter.get(chapter)
        if progress is None:
            continue
        try:
            actual = int(progress["edition_gap_units"])
        except ValueError:
            errors.append(f"progress CSV chapter {chapter} has non-integer edition_gap_units")
            continue
        if actual != expected:
            errors.append(
                f"chapter {chapter}: edition_gap_units={actual} but the edition "
                f"map has {expected} partial/not-started sections"
            )


def main() -> int:
    errors: list[str] = []
    map_rows = load_map()
    progress_rows = load_progress()
    check_migration_notes(errors, map_rows)
    check_gap_counts(errors, map_rows, progress_rows)
    if errors:
        print("Status-claim errors:", file=sys.stderr)
        for error in sorted(set(errors)):
            print(f"  - {error}", file=sys.stderr)
        return 1
    print("Status claims are consistent.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
