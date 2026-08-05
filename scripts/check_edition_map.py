#!/usr/bin/env python3
"""Validate the fourth-edition chapter map and transitional facade tree."""

from __future__ import annotations

import csv
import re
import sys
from collections import defaultdict
from pathlib import Path

from online_material import ONLINE_HEADER, load_online_rows, split_source_modules


ROOT = Path(__file__).resolve().parents[1]
MAP_HEADER = [
    "chapter_no",
    "section_no",
    "chapter_title",
    "section_title",
    "migration_state",
    "source_modules",
    "legacy_location",
    "coverage_note",
]
VALID_STATES = {"native", "facade", "partial", "not-started", "online-material"}


def module_source(root: Path, module: str) -> Path:
    """Translate a Lean module name to its source file under ``root``."""
    parts = module.split(".")
    if parts == ["CLRSLean"]:
        return root / "CLRSLean.lean"
    return root.joinpath(*parts[:-1], f"{parts[-1]}.lean")


def load_csv(path: Path, expected_header: list[str], errors: list[str]) -> list[dict[str, str]]:
    """Load one CSV while reporting a missing file or schema mismatch."""
    if not path.is_file():
        errors.append(f"missing file: {path.name}")
        return []
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != expected_header:
            errors.append(
                f"unexpected header in {path.name}: {reader.fieldnames}; expected {expected_header}"
            )
            return []
        return list(reader)


def validate_repository(root: Path) -> list[str]:
    """Return all fourth-edition map, facade, and progress contract errors."""
    errors: list[str] = []
    map_path = root / "docs" / "clrs-fourth-edition-map.csv"
    if not map_path.is_file():
        return ["missing file: clrs-fourth-edition-map.csv"]

    with map_path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != MAP_HEADER:
            return [
                f"unexpected header in clrs-fourth-edition-map.csv: {reader.fieldnames}; "
                f"expected {MAP_HEADER}"
            ]
        map_rows = list(reader)

    progress_path = root / "docs" / "clrs-proof-progress.csv"
    if not progress_path.is_file():
        errors.append("missing file: clrs-proof-progress.csv")
        progress_rows: list[dict[str, str]] = []
    else:
        with progress_path.open(newline="", encoding="utf-8") as handle:
            progress_reader = csv.DictReader(handle)
            required = {"chapter_no", "chapter_title", "tracked_key_theorems"}
            if not progress_reader.fieldnames or not required.issubset(progress_reader.fieldnames):
                errors.append("progress CSV lacks required fourth-edition fields")
                progress_rows = []
            else:
                progress_rows = list(progress_reader)

    by_chapter: dict[int, list[dict[str, str]]] = defaultdict(list)
    online_map_sources: set[str] = set()
    keys: set[tuple[int, str]] = set()
    for line, row in enumerate(map_rows, start=2):
        try:
            chapter = int(row["chapter_no"])
        except ValueError:
            errors.append(f"map line {line}: invalid chapter number {row['chapter_no']!r}")
            continue
        section = row["section_no"].strip()
        key = (chapter, section)
        if key in keys:
            errors.append(f"duplicate map key {chapter}/{section}")
        keys.add(key)
        if chapter == 0:
            if row["migration_state"].strip() != "online-material":
                errors.append(f"map line {line}: chapter 0 is reserved for online-material rows")
            if not section.startswith("online:"):
                errors.append(f"map line {line}: online section must start with 'online:'")
        elif 1 <= chapter <= 35:
            by_chapter[chapter].append(row)
            if row["migration_state"].strip() == "online-material":
                errors.append(
                    f"map line {line}: online-material rows must use reserved chapter 0"
                )
        else:
            errors.append(f"map line {line}: chapter number must be 0 or 1..35")

        state = row["migration_state"].strip()
        if state not in VALID_STATES:
            errors.append(f"map line {line}: invalid migration state {state!r}")
        if not row["chapter_title"].strip():
            errors.append(f"map line {line}: empty chapter title")
        if not row["section_title"].strip():
            errors.append(f"map line {line}: empty section title")
        if not row["coverage_note"].strip():
            errors.append(f"map line {line}: empty coverage note")

        sources = [part.strip() for part in row["source_modules"].split(";")]
        if state in {"native", "facade", "partial", "online-material"} and sources == ["none"]:
            errors.append(f"map line {line}: state {state} requires a source module")
        for source in sources:
            if source == "none":
                continue
            if not module_source(root, source).is_file():
                errors.append(f"source module does not exist: {source}")
            if chapter == 0:
                online_map_sources.add(source)

    if sorted(by_chapter) != list(range(1, 36)):
        errors.append("map chapters must be exactly 1..35")

    try:
        online_rows = load_online_rows(root)
    except ValueError as error:
        errors.append(str(error))
        online_rows = []

    online_ledger_sources: set[str] = set()
    topic_ids: set[str] = set()
    for line, row in enumerate(online_rows, start=2):
        topic_id = row["topic_id"].strip()
        if not topic_id:
            errors.append(f"online ledger line {line}: empty topic_id")
        elif topic_id in topic_ids:
            errors.append(f"duplicate online-material topic: {topic_id}")
        topic_ids.add(topic_id)
        for field in ("title", "legacy_location", "coverage_note"):
            if not row[field].strip():
                errors.append(f"online ledger line {line}: empty {field}")
        try:
            tracked = int(row["tracked_key_theorems"])
            if tracked <= 0:
                raise ValueError
        except ValueError:
            errors.append(
                f"online ledger line {line}: tracked_key_theorems must be positive"
            )
        sources = split_source_modules(row["source_modules"])
        if not sources:
            errors.append(f"online ledger line {line}: source_modules is empty")
        for source in sources:
            if source in online_ledger_sources:
                errors.append(f"duplicate online-material source: {source}")
            online_ledger_sources.add(source)
            if not module_source(root, source).is_file():
                errors.append(f"online source module does not exist: {source}")

    for source in sorted(online_ledger_sources - online_map_sources):
        errors.append(f"online ledger source is absent from edition map: {source}")
    for source in sorted(online_map_sources - online_ledger_sources):
        errors.append(f"edition-map online source is absent from online ledger: {source}")

    online_umbrella = root / "CLRSLean" / "OnlineMaterial.lean"
    if not online_umbrella.is_file():
        errors.append("missing file: CLRSLean/OnlineMaterial.lean")
    else:
        umbrella_imports = set(
            re.findall(
                r"^import\s+(CLRSLean\.[^\s]+)",
                online_umbrella.read_text(encoding="utf-8"),
                re.MULTILINE,
            )
        )
        for source in sorted(umbrella_imports - online_ledger_sources):
            errors.append(f"online-material import is not cataloged: {source}")
        for source in sorted(online_ledger_sources - umbrella_imports):
            errors.append(f"cataloged online source is not imported: {source}")

    progress_by_chapter: dict[int, dict[str, str]] = {}
    for row in progress_rows:
        try:
            chapter = int(row["chapter_no"])
        except ValueError:
            errors.append(f"progress row has invalid chapter number {row['chapter_no']!r}")
            continue
        if chapter in progress_by_chapter:
            errors.append(f"duplicate progress chapter {chapter}")
        progress_by_chapter[chapter] = row

    if progress_rows and sorted(progress_by_chapter) != list(range(1, 36)):
        errors.append("progress chapters must be exactly 1..35")

    for chapter in range(1, 36):
        chapter_rows = by_chapter.get(chapter, [])
        if not chapter_rows:
            continue
        titles = {row["chapter_title"].strip() for row in chapter_rows}
        if len(titles) != 1:
            errors.append(f"chapter {chapter} has inconsistent titles in the edition map")
            continue
        title = next(iter(titles))
        progress = progress_by_chapter.get(chapter)
        if progress is not None:
            if progress["chapter_title"].strip() != title:
                errors.append(f"chapter {chapter} title differs between map and progress")
            if all(row["migration_state"] == "not-started" for row in chapter_rows):
                try:
                    tracked = int(progress["tracked_key_theorems"])
                except ValueError:
                    errors.append(f"chapter {chapter} has invalid tracked theorem count")
                else:
                    if tracked != 0:
                        errors.append(
                            f"chapter {chapter} is not-started but tracks {tracked} theorems"
                        )

        guide = root / "CLRSLean" / "FourthEdition" / f"Chapter_{chapter:02d}.lean"
        if not guide.is_file():
            errors.append(f"missing fourth-edition guide: {guide.relative_to(root)}")
            continue
        guide_text = guide.read_text(encoding="utf-8")
        heading = re.search(
            rf"^(?:/-!\s*)?# Chapter {chapter}\s+[—-]\s+(.+)$",
            guide_text,
            re.MULTILINE,
        )
        if heading is None:
            errors.append(f"chapter {chapter} guide lacks its canonical heading")
        elif heading.group(1).strip() != title:
            errors.append(f"chapter {chapter} title differs between map and guide")

    return sorted(set(errors))


def main() -> int:
    """Validate this checkout and print a concise result."""
    errors = validate_repository(ROOT)
    if errors:
        print("Fourth-edition map errors:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    print("Fourth-edition map OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
