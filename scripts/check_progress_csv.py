#!/usr/bin/env python3
"""Validate the CLRS proof-progress CSV and optionally render the site page."""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "docs" / "clrs-proof-progress.csv"
DASHBOARD_PATH = ROOT / "CLRSLean" / "Progress.lean"
CLRSLEAN_PATH = ROOT / "CLRSLean"

HEADER = [
    "chapter_no",
    "chapter_title",
    "repo_status",
    "represented_sections",
    "tracked_key_theorems",
    "proved_tracked_theorems",
    "missing_core_groups",
    "completion_read",
    "proved_key_theorem_groups",
    "remaining_core_groups",
    "evidence_source",
    "notes",
]

STATUS_ORDER = [
    "main-proof-complete",
    "main-proof-complete-for-correctness",
    "selected-section-complete",
    "partial",
    "not-started",
    "expository",
]


def load_rows() -> list[dict[str, str]]:
    with CSV_PATH.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != HEADER:
            raise SystemExit(
                "Unexpected CSV header.\n"
                f"expected: {HEADER}\n"
                f"actual:   {reader.fieldnames}"
            )
        return list(reader)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def int_field(row: dict[str, str], name: str) -> int:
    raw = row[name]
    try:
        value = int(raw)
    except ValueError as exc:
        raise SystemExit(f"Chapter {row['chapter_no']}: {name} is not an int: {raw}") from exc
    require(value >= 0, f"Chapter {row['chapter_no']}: {name} is negative")
    return value


def validate(rows: list[dict[str, str]]) -> None:
    require(len(rows) == 35, f"Expected 35 CLRS chapter rows, found {len(rows)}")
    seen: set[int] = set()

    for expected, row in enumerate(rows, start=1):
        chapter_no = int_field(row, "chapter_no")
        require(chapter_no == expected, f"Expected chapter {expected}, found {chapter_no}")
        require(chapter_no not in seen, f"Duplicate chapter row: {chapter_no}")
        seen.add(chapter_no)

        tracked = int_field(row, "tracked_key_theorems")
        proved = int_field(row, "proved_tracked_theorems")
        int_field(row, "missing_core_groups")
        require(proved <= tracked, f"Chapter {chapter_no}: proved theorem count exceeds tracked count")

        for key in ("chapter_title", "repo_status", "completion_read", "evidence_source"):
            require(row[key].strip(), f"Chapter {chapter_no}: {key} must be nonempty")

        require(
            row["repo_status"] in STATUS_ORDER,
            f"Chapter {chapter_no}: unknown repo_status {row['repo_status']}",
        )

        if row["repo_status"] == "not-started":
            require(
                row["represented_sections"].lower() == "none",
                f"Chapter {chapter_no}: not-started rows should use represented_sections=None",
            )
            chapter_dir = CLRSLEAN_PATH / f"Chapter_{chapter_no:02d}"
            section_files = list(chapter_dir.rglob("Section_*.lean")) if chapter_dir.is_dir() else []
            require(
                not section_files,
                f"Chapter {chapter_no}: marked not-started but section files exist",
            )
            continue

        guide = CLRSLEAN_PATH / f"Chapter_{chapter_no:02d}.lean"
        require(guide.is_file(), f"Chapter {chapter_no}: missing guide {guide.relative_to(ROOT)}")

        if row["repo_status"] == "expository":
            require(
                row["represented_sections"] == f"Chapter_{chapter_no:02d}",
                f"Chapter {chapter_no}: expository row should name its guide module",
            )
            continue

        expected_sections = {part.strip() for part in row["represented_sections"].split(";")}
        require(
            all(re.fullmatch(rf"{chapter_no}\.\d+", part) for part in expected_sections),
            f"Chapter {chapter_no}: represented_sections must be semicolon-separated section numbers",
        )

        chapter_dir = CLRSLEAN_PATH / f"Chapter_{chapter_no:02d}"
        require(chapter_dir.is_dir(), f"Chapter {chapter_no}: missing section directory")
        actual_sections: set[str] = set()
        for section_file in chapter_dir.rglob("Section_*.lean"):
            match = re.match(r"Section_(\d+)_(\d+)_", section_file.name)
            require(match is not None, f"Unexpected section filename: {section_file.name}")
            actual_sections.add(f"{int(match.group(1))}.{int(match.group(2))}")

        require(
            expected_sections == actual_sections,
            f"Chapter {chapter_no}: CSV sections {sorted(expected_sections)} "
            f"do not match source sections {sorted(actual_sections)}",
        )


def lit(text: str) -> str:
    return "{lit}`" + text + "`"


def clean_sections(raw: str) -> str:
    return "not represented" if raw.lower() == "none" else raw


def chapter_word(count: int) -> str:
    return "chapter" if count == 1 else "chapters"


def render_dashboard(rows: list[dict[str, str]]) -> str:
    status_counts = Counter(row["repo_status"] for row in rows)
    represented = sum(1 for row in rows if row["represented_sections"].lower() != "none")
    tracked = sum(int(row["tracked_key_theorems"]) for row in rows)
    proved = sum(int(row["proved_tracked_theorems"]) for row in rows)
    missing = sum(int(row["missing_core_groups"]) for row in rows)

    lines: list[str] = [
        "/-!",
        "# Progress Dashboard",
        "",
        "This page is the public, reader-facing progress dashboard for CLRS-Lean.",
        f"The machine-readable source of truth is {lit('docs/clrs-proof-progress.csv')}.",
        "When the CSV changes, regenerate this page with",
        f"{lit('uv run python scripts/check_progress_csv.py --write-dashboard')}.",
        "",
        "## Snapshot",
        "",
        f"* CLRS chapters tracked: {len(rows)}.",
        f"* Chapters represented in Lean: {represented}.",
        f"* Tracked reader-facing theorem entries: {tracked}.",
        f"* Proved tracked theorem entries: {proved}.",
        f"* Remaining core theorem groups: {missing}.",
        "",
        "Tracked theorem entries count the public theorem groups currently represented",
        "in Lean.  Remaining core theorem groups count textbook-facing targets that",
        "are not yet represented or not yet complete.",
        "",
        "## Status Counts",
        "",
    ]

    for status in STATUS_ORDER:
        if status in status_counts:
            count = status_counts[status]
            lines.append(f"* {lit(status)}: {count} {chapter_word(count)}.")

    lines.extend(
        [
            "",
            "## Chapter Matrix",
            "",
            "```",
            "Ch  Chapter                                                     Status                               Sections                      Tracked  Missing",
            "--  ----------------------------------------------------------  -----------------------------------  ----------------------------  -------  -------",
        ]
    )

    for row in rows:
        chapter = f"{row['chapter_no']}. {row['chapter_title']}"[:58]
        status = row["repo_status"][:35]
        sections = clean_sections(row["represented_sections"])[:28]
        tracked_count = row["tracked_key_theorems"]
        missing_count = row["missing_core_groups"]
        lines.append(
            f"{int(row['chapter_no']):>2}  "
            f"{chapter:<58}  "
            f"{status:<35}  "
            f"{sections:<28}  "
            f"{tracked_count:>7}  "
            f"{missing_count:>7}"
        )

    lines.extend(
        [
            "```",
            "",
            "## Agent Update Rule",
            "",
            "Every theorem-producing agent should treat this table as part of the proof",
            "artifact, not as a separate report.  If a contribution adds, removes,",
            "renames, strengthens, or finishes a reader-facing theorem group, update",
            f"{lit('docs/clrs-proof-progress.csv')} in the same commit.  If the change",
            "alters the public snapshot or chapter rows, regenerate this page before",
            "building the site.",
            "",
            "Minimum maintenance loop:",
            "",
            f"1. Update the relevant chapter/section Lean files and {lit('docs/clrs-proof-progress.csv')}.",
            f"2. Run {lit('uv run python scripts/check_progress_csv.py --write-dashboard')}.",
            f"3. Run {lit('lake build CLRSLean')} and, for website changes, {lit('lake build :literateHtml')}.",
            "-/",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write-dashboard",
        action="store_true",
        help="regenerate CLRSLean/Progress.lean from the CSV after validation",
    )
    args = parser.parse_args()

    rows = load_rows()
    validate(rows)

    if args.write_dashboard:
        DASHBOARD_PATH.write_text(render_dashboard(rows), encoding="utf-8")

    tracked = sum(int(row["tracked_key_theorems"]) for row in rows)
    proved = sum(int(row["proved_tracked_theorems"]) for row in rows)
    print(f"progress CSV OK: {len(rows)} chapters, {tracked} tracked theorem entries, {proved} proved")
    if args.write_dashboard:
        print(f"wrote {DASHBOARD_PATH.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
