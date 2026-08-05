#!/usr/bin/env python3
"""Validate the CLRS proof-progress CSV and optionally render the site page."""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from pathlib import Path
import sys

from online_material import online_tracked_total


ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "docs" / "clrs-proof-progress.csv"
MAP_PATH = ROOT / "docs" / "clrs-fourth-edition-map.csv"
DASHBOARD_PATH = ROOT / "CLRSLean" / "Progress.lean"
ONLINE_MATERIAL_TRACKED_THEOREMS = online_tracked_total()

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


def load_map_rows() -> list[dict[str, str]]:
    with MAP_PATH.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def chapter_contracts(
    map_rows: list[dict[str, str]] | None = None,
) -> dict[int, dict[str, object]]:
    """Build the chapter-level progress contract from the fourth-edition map."""
    grouped: dict[int, list[dict[str, str]]] = {}
    for map_row in load_map_rows() if map_rows is None else map_rows:
        if map_row.get("migration_state") == "online-material":
            continue
        try:
            chapter_no = int(map_row["chapter_no"])
        except (KeyError, ValueError) as exc:
            raise SystemExit(f"Invalid fourth-edition map chapter: {map_row}") from exc
        grouped.setdefault(chapter_no, []).append(map_row)

    require(
        sorted(grouped) == list(range(1, 36)),
        "Fourth-edition map must define Chapters 1--35 exactly",
    )

    contracts: dict[int, dict[str, object]] = {}
    for chapter_no, chapter_rows in grouped.items():
        titles = {row["chapter_title"].strip() for row in chapter_rows}
        require(
            len(titles) == 1 and "" not in titles,
            f"Chapter {chapter_no}: fourth-edition map titles disagree",
        )
        states = {row["migration_state"] for row in chapter_rows}
        represented_sections = tuple(
            row["section_no"]
            for row in chapter_rows
            if row["migration_state"] not in {"not-started", "online-material"}
            and row["source_modules"].strip().lower() != "none"
        )
        source_modules = tuple(
            sorted(
                {
                    source.strip()
                    for row in chapter_rows
                    for source in row["source_modules"].split(";")
                    if source.strip().lower() != "none"
                }
            )
        )
        if not represented_sections:
            required_status = "not-started"
        elif states.intersection({"partial", "not-started"}):
            required_status = "partial"
        else:
            required_status = None
        contracts[chapter_no] = {
            "title": titles.pop(),
            "represented_sections": represented_sections,
            "required_status": required_status,
            "guide": Path(f"CLRSLean/FourthEdition/Chapter_{chapter_no:02d}.lean"),
            "source_modules": source_modules,
        }
    return contracts


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
    contracts = chapter_contracts()
    require(
        len(rows) == len(contracts),
        f"Expected {len(contracts)} CLRS fourth-edition chapter rows, found {len(rows)}",
    )
    seen: set[int] = set()

    for expected, row in enumerate(rows, start=1):
        chapter_no = int_field(row, "chapter_no")
        require(chapter_no == expected, f"Expected chapter {expected}, found {chapter_no}")
        require(chapter_no not in seen, f"Duplicate chapter row: {chapter_no}")
        seen.add(chapter_no)
        contract = contracts[chapter_no]

        require(
            row["chapter_title"] == contract["title"],
            f"Chapter {chapter_no}: fourth-edition title must be "
            f"{contract['title']!r}, found {row['chapter_title']!r}",
        )

        guide = ROOT / contract["guide"]
        require(
            guide.is_file(),
            f"Chapter {chapter_no}: missing fourth-edition guide "
            f"{guide.relative_to(ROOT)}",
        )

        for source_module in contract["source_modules"]:
            source_path = ROOT / (str(source_module).replace(".", "/") + ".lean")
            require(
                source_path.is_file(),
                f"Chapter {chapter_no}: mapped source module does not exist: "
                f"{source_module}",
            )

        tracked = int_field(row, "tracked_key_theorems")
        proved = int_field(row, "proved_tracked_theorems")
        missing_core_groups = int_field(row, "missing_core_groups")
        require(proved <= tracked, f"Chapter {chapter_no}: proved theorem count exceeds tracked count")

        for key in ("chapter_title", "repo_status", "completion_read", "evidence_source"):
            require(row[key].strip(), f"Chapter {chapter_no}: {key} must be nonempty")

        for source in (part.strip() for part in row["evidence_source"].split(";")):
            if source == "CLRSLean file tree":
                continue
            require(
                (ROOT / source).is_file(),
                f"Chapter {chapter_no}: evidence source does not exist: {source}",
            )

        require(
            row["repo_status"] in STATUS_ORDER,
            f"Chapter {chapter_no}: unknown repo_status {row['repo_status']}",
        )
        required_status = contract["required_status"]
        if required_status is not None:
            require(
                row["repo_status"] == required_status,
                f"Chapter {chapter_no}: fourth-edition map requires status "
                f"{required_status}, found {row['repo_status']}",
            )
        if row["repo_status"] in {"partial", "not-started"}:
            require(
                missing_core_groups > 0,
                f"Chapter {chapter_no}: {row['repo_status']} rows must have "
                "positive missing_core_groups",
            )

        if row["repo_status"] == "not-started":
            require(
                row["represented_sections"].lower() == "none",
                f"Chapter {chapter_no}: not-started rows should use represented_sections=None",
            )
            require(
                tracked == 0 and proved == 0,
                f"Chapter {chapter_no}: not-started rows must have zero tracked theorem entries",
            )
            continue

        if row["repo_status"] == "expository":
            require(
                row["represented_sections"] == f"Chapter_{chapter_no:02d}",
                f"Chapter {chapter_no}: expository row should name its guide module",
            )
            continue

        expected_sections = tuple(
            part.strip() for part in row["represented_sections"].split(";")
        )
        require(
            all(
                part.startswith(f"{chapter_no}.")
                and part.removeprefix(f"{chapter_no}.").isdigit()
                for part in expected_sections
            ),
            f"Chapter {chapter_no}: represented_sections must be semicolon-separated section numbers",
        )
        require(
            expected_sections == contract["represented_sections"],
            f"Chapter {chapter_no}: CSV sections {list(expected_sections)} "
            "do not match represented sections in docs/clrs-fourth-edition-map.csv "
            f"{list(contract['represented_sections'])}",
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
        "## Fourth-Edition Snapshot",
        "",
        "This is the canonical CLRS fourth-edition chapter ledger.  Reused",
        "third-edition theorem sources remain compatibility evidence, not an",
        "alternative chapter-numbering scheme.",
        "Legacy imports remain supported through all 1.x releases and for at",
        "least six months; removal is possible only in 2.0 or later.",
        "",
        f"* Fourth-edition chapters tracked: {len(rows)}.",
        f"* Chapters represented in Lean: {represented}.",
        f"* Tracked reader-facing theorem entries: {tracked:,}.",
        f"* Proved tracked theorem entries: {proved:,}.",
        f"* Online/supplementary theorem entries: {ONLINE_MATERIAL_TRACKED_THEOREMS:,}.",
        f"* Remaining core theorem groups: {missing}.",
        "",
        "Tracked theorem entries are reviewed groups mapped to represented fourth-edition",
        "sections.  Moved subsections and wholly excluded legacy chapters are counted only",
        "in the machine-readable online-material ledger.  This produces disjoint canonical and online-material ledgers;",
        "compatibility imports do not duplicate either count.",
        "Remaining core theorem groups count textbook-facing targets that are not yet",
        "represented or not yet complete.",
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
            f"1. Consult {lit('docs/clrs-fourth-edition-map.csv')}, then update the relevant Lean files and {lit('docs/clrs-proof-progress.csv')}.",
            f"2. Run {lit('uv run python scripts/check_progress_csv.py --write-dashboard')}.",
            f"3. Run {lit('lake build CLRSLean')}; for explicit website publishing, use the four-shard runbook in {lit('docs/site-architecture.md')}.  The serial {lit('lake build :literateHtml')} target is a diagnostic fallback.",
            "-/",
            "",
        ]
    )
    return "\n".join(lines)


def check_dashboard_freshness(
    rows: list[dict[str, str]], dashboard_path: Path = DASHBOARD_PATH
) -> None:
    """Reject a generated dashboard that no longer matches the CSV."""
    expected = render_dashboard(rows)
    actual = (
        dashboard_path.read_text(encoding="utf-8")
        if dashboard_path.is_file()
        else ""
    )
    if actual != expected:
        raise ValueError(
            f"{dashboard_path} is out of date; run "
            "`uv run python scripts/check_progress_csv.py --write-dashboard`"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    output_mode = parser.add_mutually_exclusive_group()
    output_mode.add_argument(
        "--write-dashboard",
        action="store_true",
        help="regenerate CLRSLean/Progress.lean from the CSV after validation",
    )
    output_mode.add_argument(
        "--check-dashboard",
        action="store_true",
        help="exit nonzero when CLRSLean/Progress.lean is stale",
    )
    args = parser.parse_args()

    rows = load_rows()
    validate(rows)

    if args.write_dashboard:
        DASHBOARD_PATH.write_text(render_dashboard(rows), encoding="utf-8")
    elif args.check_dashboard:
        check_dashboard_freshness(rows)

    tracked = sum(int(row["tracked_key_theorems"]) for row in rows)
    proved = sum(int(row["proved_tracked_theorems"]) for row in rows)
    print(f"progress CSV OK: {len(rows)} chapters, {tracked} tracked theorem entries, {proved} proved")
    if args.write_dashboard:
        print(f"wrote {DASHBOARD_PATH.relative_to(ROOT)}")
    elif args.check_dashboard:
        print(f"{DASHBOARD_PATH.relative_to(ROOT)} is up to date")
    return 0


if __name__ == "__main__":
    sys.exit(main())
