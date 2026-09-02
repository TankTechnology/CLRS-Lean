#!/usr/bin/env python3
"""Audit the formalization-to-book relationship for all 35 fourth-edition chapters.

CLRS-Lean keeps the CLRS book structure in two machine-readable ledgers:

  - ``docs/clrs-fourth-edition-map.csv``  (per-section migration state + sources)
  - ``docs/clrs-proof-progress.csv``      (per-chapter status + theorem counts)

The formalization itself lives in Lean files.  When the ledgers and the Lean
tree drift apart — a section file with no book row, a tracked theorem count that
no source file backs, a gap record that names an already-complete section — the
drift is invisible to the chapter-status validators but shows up as a wrong
reader-facing coverage claim.  This checker closes that gap by reconciling the
two ledgers against the actual ``CLRSLean`` source tree.

Checks (all chapters 1..35):

  1. Section coverage, bidirectional: every edition-map source module must exist
     on disk, and every top-level FourthEdition ``Section_*.lean`` module must be
     named by an edition-map row (orphans are drift).
  2. Theorem accounting: for each chapter, count ``theorem``/``lemma`` heads in
     the transitive import closure of its mapped sources and compare against
     ``tracked_key_theorems``/``proved_tracked_theorems``; flag zero-crossing
     drift (tracks > 0 with no declared heads, or declared > 0 with 0 tracked).
  3. Gap integrity: a ``not-started`` section must not carry a theorem-bearing
     source (stale gap), gap prose must not reference a section that is actually
     complete (stale reference), and every ``not-started`` section must be named
     in the chapter's gap prose (missing record).
  4. Status consistency: ``repo_status`` must agree with the edition-map states
     and the theorem accounting (``main-proof-complete`` implies proved ==
     tracked and zero gaps; ``expository`` implies zero theorems; ``partial``
     implies a real map gap).  This complements, and does not replace,
     ``check_status_claims.py``, which cross-validates the hand-written prose.
  5. Per-chapter human-readable report plus a nonzero exit on any failure.

Run from the repository root:
    python3 scripts/check_book_coverage.py [--report]
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Mirrors check_edition_map.MAP_HEADER and check_progress_csv.HEADER so this
# module stays self-contained while following the same parsing conventions.
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

PROGRESS_HEADER = [
    "chapter_no",
    "chapter_title",
    "repo_status",
    "represented_sections",
    "tracked_key_theorems",
    "proved_tracked_theorems",
    "edition_gap_units",
    "completion_read",
    "proved_key_theorem_groups",
    "remaining_edition_gaps",
    "evidence_source",
    "notes",
]

GAP_STATES = {"partial", "not-started"}
STARTED_STATES = {"native", "facade", "partial"}
COMPLETE_STATUSES = {"main-proof-complete", "main-proof-complete-for-correctness"}
ZERO_THEOREM_STATUSES = {"expository", "not-started"}

THEOREM_RE = re.compile(r"\b(?:theorem|lemma)\b")
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
TOP_LEVEL_SECTION_RE = re.compile(r"^CLRSLean\.FourthEdition\.Chapter_\d+\.Section_[^.]+$")
SECTION_REF_RE = re.compile(r"\b(\d{1,2})\.(\d{1,2})\b")


def module_source(root: Path, module: str) -> Path:
    """Translate a Lean module name to its source file under ``root``.

    The ``CLRSLean`` library lives under ``src/`` (``srcDir := "src"``).
    """
    parts = module.split(".")
    if parts == ["CLRSLean"]:
        return root / "src" / "CLRSLean.lean"
    return root.joinpath("src", *parts[:-1], f"{parts[-1]}.lean")


def strip_lean_comments_and_strings(text: str) -> str:
    """Replace Lean comments and string contents while preserving newlines.

    Mirrors ``check_repository.strip_lean_comments_and_strings`` so the theorem
    head count never sees prose inside ``/- ... -/`` blocks or strings.
    """
    output: list[str] = []
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False

    while i < len(text):
        pair = text[i : i + 2]

        if in_line_comment:
            if text[i] == "\n":
                in_line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            i += 1
            continue

        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                i += 2
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        if in_string:
            if text[i] == "\\" and i + 1 < len(text):
                output.extend("  ")
                i += 2
            elif text[i] == '"':
                in_string = False
                output.append(" ")
                i += 1
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        if pair == "--":
            in_line_comment = True
            output.extend("  ")
            i += 2
        elif pair == "/-":
            block_depth = 1
            output.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            output.append(" ")
            i += 1
        else:
            output.append(text[i])
            i += 1

    if block_depth:
        raise SystemExit("Unclosed Lean block comment encountered during coverage scan")
    return "".join(output)


def split_source_modules(raw: str) -> list[str]:
    """Return the non-``none`` source modules in a semicolon list."""
    return [
        part.strip()
        for part in raw.split(";")
        if part.strip() and part.strip().lower() != "none"
    ]


def _int(row: dict[str, str], field: str) -> int:
    try:
        return int(row[field])
    except (KeyError, ValueError):
        return 0


def load_csv(path: Path, expected_header: list[str]) -> list[dict[str, str]]:
    if not path.is_file():
        raise SystemExit(f"missing file: {path.name}")
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != expected_header:
            raise SystemExit(
                f"unexpected header in {path.name}: {reader.fieldnames}; "
                f"expected {expected_header}"
            )
        return list(reader)


def load_map(root: Path) -> list[dict[str, str]]:
    return load_csv(root / "docs" / "clrs-fourth-edition-map.csv", MAP_HEADER)


def load_progress(root: Path) -> list[dict[str, str]]:
    return load_csv(root / "docs" / "clrs-proof-progress.csv", PROGRESS_HEADER)


def chapter_sections(map_rows: list[dict[str, str]]) -> dict[int, list[dict[str, str]]]:
    grouped: dict[int, list[dict[str, str]]] = defaultdict(list)
    for row in map_rows:
        chapter = _int(row, "chapter_no")
        if 1 <= chapter <= 35:
            grouped[chapter].append(row)
    return grouped


def chapter_progress(progress_rows: list[dict[str, str]]) -> dict[int, dict[str, str]]:
    return {_int(row, "chapter_no"): row for row in progress_rows if _int(row, "chapter_no")}


def build_module_index(root: Path) -> dict[str, tuple[int, frozenset[str]]]:
    """Index every ``CLRSLean`` module to (declared heads, internal imports)."""
    index: dict[str, tuple[int, frozenset[str]]] = {}
    paths: list[Path] = []
    src_root = root / "src"
    root_file = src_root / "CLRSLean.lean"
    if root_file.is_file():
        paths.append(root_file)
    library = src_root / "CLRSLean"
    if library.is_dir():
        paths.extend(sorted(library.rglob("*.lean")))
    for path in paths:
        module = ".".join(path.relative_to(src_root).with_suffix("").parts)
        code = strip_lean_comments_and_strings(path.read_text(encoding="utf-8"))
        declared = len(THEOREM_RE.findall(code))
        imports = frozenset(
            name for name in IMPORT_RE.findall(code) if name.startswith("CLRSLean")
        )
        index[module] = (declared, imports)
    return index


def closure_declared(index: dict[str, tuple[int, frozenset[str]]], seeds: set[str]) -> int:
    """Total theorem/lemma heads reachable from ``seeds`` through imports."""
    seen: set[str] = set()
    stack = list(seeds)
    total = 0
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        entry = index.get(module)
        if entry is None:
            continue
        declared, imports = entry
        total += declared
        stack.extend(imports)
    return total


def check_section_coverage(
    root: Path, map_rows: list[dict[str, str]], index: dict[str, tuple[int, frozenset[str]]]
) -> list[str]:
    """Map -> disk (sources must exist) and disk -> map (no orphan sections)."""
    errors: list[str] = []
    map_sources: set[str] = set()
    for row in map_rows:
        chapter = _int(row, "chapter_no")
        if chapter == 0:
            continue
        section = row["section_no"].strip()
        for source in split_source_modules(row["source_modules"]):
            map_sources.add(source)
            if not module_source(root, source).is_file():
                errors.append(
                    f"chapter {chapter} section {section}: mapped source module does "
                    f"not exist: {source}"
                )
    for module in index:
        if TOP_LEVEL_SECTION_RE.fullmatch(module) and module not in map_sources:
            errors.append(
                f"orphan FourthEdition section module has no edition-map row: {module}"
            )
    return errors


def check_theorem_accounting(
    map_rows: list[dict[str, str]],
    progress_rows: list[dict[str, str]],
    index: dict[str, tuple[int, frozenset[str]]],
) -> tuple[list[str], dict[int, int]]:
    """Compare tracked/proved counts against declared heads in the sources."""
    errors: list[str] = []
    sections = chapter_sections(map_rows)
    progress = chapter_progress(progress_rows)
    declared_by_chapter: dict[int, int] = {}
    for chapter in range(1, 36):
        seeds = {
            source
            for row in sections.get(chapter, [])
            for source in split_source_modules(row["source_modules"])
        }
        declared = closure_declared(index, seeds)
        declared_by_chapter[chapter] = declared

        row = progress.get(chapter)
        if row is None:
            continue
        tracked = _int(row, "tracked_key_theorems")
        proved = _int(row, "proved_tracked_theorems")
        status = row["repo_status"].strip()
        if proved > tracked:
            errors.append(
                f"chapter {chapter}: proved_tracked_theorems ({proved}) exceeds "
                f"tracked_key_theorems ({tracked})"
            )
        if status in ZERO_THEOREM_STATUSES:
            continue  # zero-theorem expectations are asserted in status consistency
        if tracked == 0 and declared > 0:
            errors.append(
                f"chapter {chapter}: sources declare {declared} theorem/lemma heads "
                "but tracked_key_theorems is 0"
            )
        if tracked > 0 and declared == 0:
            errors.append(
                f"chapter {chapter}: tracks {tracked} theorems but its mapped "
                "sources declare no theorem/lemma heads"
            )
    return errors, declared_by_chapter


def _section_num(section_no: str) -> int | None:
    parts = section_no.strip().split(".")
    if not parts:
        return None
    try:
        return int(parts[-1])
    except ValueError:
        return None


def extract_section_refs(text: str) -> set[tuple[int, int]]:
    """Best-effort section-number references (``chapter.section``) in prose."""
    refs: set[tuple[int, int]] = set()
    for match in SECTION_REF_RE.finditer(text or ""):
        chapter = int(match.group(1))
        section = int(match.group(2))
        if 1 <= chapter <= 35:
            refs.add((chapter, section))
    return refs


def check_gap_integrity(
    map_rows: list[dict[str, str]],
    progress_rows: list[dict[str, str]],
    index: dict[str, tuple[int, frozenset[str]]],
) -> list[str]:
    """Gap records must reference real absences, and absences need records."""
    errors: list[str] = []
    sections = chapter_sections(map_rows)
    progress = chapter_progress(progress_rows)
    for chapter in range(1, 36):
        rows = sections.get(chapter, [])
        gap_nums: dict[int, str] = {}
        for row in rows:
            if row["migration_state"].strip() in GAP_STATES:
                num = _section_num(row["section_no"])
                if num is not None:
                    gap_nums[num] = row["migration_state"].strip()

        # Stale gap: a "not-started" section must not already carry theorems.
        for row in rows:
            if row["migration_state"].strip() == "not-started":
                sources = set(split_source_modules(row["source_modules"]))
                if sources and closure_declared(index, sources) > 0:
                    errors.append(
                        f"chapter {chapter}: not-started section "
                        f"{row['section_no']} has a theorem-bearing source"
                    )

        # References gathered from the chapter gap prose and the gap sections'
        # own coverage notes.
        refs: set[tuple[int, int]] = set()
        progress_row = progress.get(chapter)
        if progress_row is not None:
            refs |= extract_section_refs(progress_row["remaining_edition_gaps"])
        for row in rows:
            if row["migration_state"].strip() in GAP_STATES:
                refs |= extract_section_refs(row["coverage_note"])

        # Stale reference: prose names a section that is not actually a gap.
        for ref_chapter, ref_section in refs:
            if ref_chapter == chapter and ref_section not in gap_nums:
                errors.append(
                    f"chapter {chapter}: gap prose references section "
                    f"{ref_chapter}.{ref_section} which is not a gap"
                )

        # Missing record: a wholly absent section must be named in the prose.
        for num, state in gap_nums.items():
            if state == "not-started" and (chapter, num) not in refs:
                errors.append(
                    f"chapter {chapter}: not-started section {chapter}.{num} has no "
                    "gap record"
                )
    return errors


def check_status_consistency(
    map_rows: list[dict[str, str]],
    progress_rows: list[dict[str, str]],
    declared_by_chapter: dict[int, int],
) -> list[str]:
    """Reconcile ``repo_status`` with edition-map states and theorem counts."""
    errors: list[str] = []
    sections = chapter_sections(map_rows)
    progress = chapter_progress(progress_rows)
    for chapter in range(1, 36):
        row = progress.get(chapter)
        if row is None:
            continue
        status = row["repo_status"].strip()
        tracked = _int(row, "tracked_key_theorems")
        proved = _int(row, "proved_tracked_theorems")
        gaps = _int(row, "edition_gap_units")
        states = {r["migration_state"].strip() for r in sections.get(chapter, [])}
        has_gap = bool(states & GAP_STATES)
        declared = declared_by_chapter.get(chapter, 0)

        if status == "main-proof-complete":
            if proved != tracked:
                errors.append(
                    f"chapter {chapter}: main-proof-complete but proved ({proved}) "
                    f"!= tracked ({tracked})"
                )
            if gaps != 0:
                errors.append(
                    f"chapter {chapter}: main-proof-complete but edition_gap_units "
                    f"= {gaps}"
                )
            if has_gap:
                errors.append(
                    f"chapter {chapter}: main-proof-complete but the edition map "
                    "still has partial/not-started sections"
                )
        elif status == "main-proof-complete-for-correctness":
            if proved != tracked:
                errors.append(
                    f"chapter {chapter}: main-proof-complete-for-correctness but "
                    f"proved ({proved}) != tracked ({tracked})"
                )
        elif status == "expository":
            if tracked != 0 or proved != 0:
                errors.append(
                    f"chapter {chapter}: expository but tracks theorems "
                    f"({tracked} tracked / {proved} proved)"
                )
            if declared != 0:
                errors.append(
                    f"chapter {chapter}: expository chapter declares {declared} "
                    "theorem/lemma heads"
                )
        elif status == "partial":
            if not has_gap:
                errors.append(
                    f"chapter {chapter}: partial but the edition map has no "
                    "partial/not-started sections"
                )
            if gaps == 0:
                errors.append(
                    f"chapter {chapter}: partial but edition_gap_units = 0"
                )
        elif status == "not-started":
            if tracked != 0 or proved != 0:
                errors.append(
                    f"chapter {chapter}: not-started but tracks theorems "
                    f"({tracked} tracked / {proved} proved)"
                )
            if gaps != 1:
                errors.append(
                    f"chapter {chapter}: not-started but edition_gap_units = {gaps}"
                )
    return errors


def collect_errors(
    root: Path,
) -> tuple[list[str], dict[int, int], list[dict[str, str]], list[dict[str, str]]]:
    """Run every check and return (errors, declared_by_chapter, map, progress)."""
    map_rows = load_map(root)
    progress_rows = load_progress(root)
    index = build_module_index(root)

    errors: list[str] = []
    errors += check_section_coverage(root, map_rows, index)
    theorem_errors, declared = check_theorem_accounting(map_rows, progress_rows, index)
    errors += theorem_errors
    errors += check_gap_integrity(map_rows, progress_rows, index)
    errors += check_status_consistency(map_rows, progress_rows, declared)
    return sorted(set(errors)), declared, map_rows, progress_rows


def render_report(
    map_rows: list[dict[str, str]],
    progress_rows: list[dict[str, str]],
    declared_by_chapter: dict[int, int],
    errors: list[str],
) -> str:
    sections = chapter_sections(map_rows)
    progress = chapter_progress(progress_rows)
    lines = [
        "Formalization-to-book coverage report (chapters 1--35)",
        "=" * 54,
        "",
    ]
    for chapter in range(1, 36):
        rows = sections.get(chapter, [])
        row = progress.get(chapter)
        if row is None:
            continue
        title = row["chapter_title"].strip() or (rows[0]["chapter_title"].strip() if rows else "")
        status = row["repo_status"].strip()
        declared = declared_by_chapter.get(chapter, 0)
        tracked = _int(row, "tracked_key_theorems")
        proved = _int(row, "proved_tracked_theorems")
        gaps = _int(row, "edition_gap_units")

        section_summary = ", ".join(
            f"{r['section_no']} {r['migration_state'].strip()}" for r in rows
        )
        drift_notes: list[str] = []
        if tracked > declared > 0:
            drift_notes.append(f"tracked {tracked} exceeds declared {declared}")
        if declared == 0 and status not in ZERO_THEOREM_STATUSES:
            drift_notes.append("no declared heads")

        lines.append(f"Chapter {chapter:2d}  {title}  [{status}]")
        lines.append(f"  sections: {section_summary or '(none)'}")
        lines.append(f"  theorems: declared {declared} | tracked {tracked} | proved {proved}")
        if drift_notes:
            lines.append(f"  drift: {'; '.join(drift_notes)}")
        if gaps > 0:
            remaining = row["remaining_edition_gaps"].strip()
            lines.append(f"  gaps ({gaps} units): {remaining}")
        else:
            lines.append("  gaps: none")
        lines.append("")

    if errors:
        lines.append(f"{len(errors)} coverage drift error(s):")
        for error in errors:
            lines.append(f"  - {error}")
    else:
        lines.append("No coverage drift detected.")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--report",
        action="store_true",
        help="print the full per-chapter report to stdout (always shown on failure)",
    )
    args = parser.parse_args()

    try:
        errors, declared, map_rows, progress_rows = collect_errors(ROOT)
    except SystemExit as exc:
        print(exc, file=sys.stderr)
        return 1

    if errors:
        print("Book-coverage errors:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        print(render_report(map_rows, progress_rows, declared, errors))
        return 1

    print("Book coverage OK (35 chapters)")
    if args.report:
        print(render_report(map_rows, progress_rows, declared, []))
    return 0


if __name__ == "__main__":
    sys.exit(main())
