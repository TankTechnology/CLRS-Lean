#!/usr/bin/env python3
"""
Semantic Fidelity Audit Orchestrator

Coordinates a multi-agent audit of a CLRS-Lean chapter:
1. Reads the edition map to find source modules for the chapter
2. Spawns auditor subagents per section
3. Spawns adversary subagents to review MATCH verdicts
4. Synthesizes a final report

This script is designed to be invoked by the Claude Code harness via the
semantic-fidelity-audit skill. It produces structured output that the
harness can use to fan out subagent calls.
"""

import csv
import json
import os
import sys
from pathlib import Path
from typing import Optional

REPO_ROOT = Path(__file__).resolve().parents[4]  # .claude/skills/.../scripts -> repo root
EDITION_MAP = REPO_ROOT / "docs" / "clrs-fourth-edition-map.csv"
SKILL_DIR = Path(__file__).resolve().parents[1]  # semantic-fidelity-audit/
REFERENCES = SKILL_DIR / "references"


def load_edition_map() -> list[dict]:
    """Load the edition map CSV, returning only canonical (non-online) rows."""
    rows = []
    with open(EDITION_MAP, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row.get("chapter_no", "0") == "0":
                continue  # skip online-material rows
            rows.append(row)
    return rows


def get_chapter_rows(rows: list[dict], chapter_no: int) -> list[dict]:
    """Return all edition-map rows for a given chapter number."""
    return [r for r in rows if int(r["chapter_no"]) == chapter_no]


def get_sections(chapter_rows: list[dict]) -> list[dict]:
    """Group rows by section, returning one entry per unique section."""
    seen = set()
    sections = []
    for row in chapter_rows:
        sec = row["section_no"]
        if sec not in seen:
            seen.add(sec)
            sections.append({
                "section_no": sec,
                "section_title": row["section_title"],
                "source_modules": row["source_modules"],
                "migration_state": row["migration_state"],
                "coverage_note": row["coverage_note"],
            })
    return sections


def generate_audit_plan(chapter_no: int, corpus_path: Optional[str] = None) -> dict:
    """
    Generate an audit plan for a chapter.

    Returns a dict with:
    - chapter_no, chapter_title
    - sections: list of {section_no, title, source_modules, migration_state, coverage_note}
    - corpus_path: str or None
    - checklist_path: str
    - verdict_defs_path: str
    - adversary_playbook_path: str
    """
    rows = load_edition_map()
    chapter_rows = get_chapter_rows(rows, chapter_no)
    if not chapter_rows:
        sys.exit(f"Chapter {chapter_no} not found in edition map")

    chapter_title = chapter_rows[0]["chapter_title"]
    sections = get_sections(chapter_rows)

    plan = {
        "chapter_no": chapter_no,
        "chapter_title": chapter_title,
        "sections": sections,
        "corpus_path": corpus_path,
        "checklist_path": str(REFERENCES / "checklist.md"),
        "verdict_defs_path": str(REFERENCES / "verdict-definitions.md"),
        "adversary_playbook_path": str(REFERENCES / "adversary-playbook.md"),
        "report_template_path": str(REFERENCES / "report-template.md"),
        "auditor_prompt_template": str(REFERENCES / "auditor-prompt.md"),
        "adversary_prompt_template": str(REFERENCES / "adversary-prompt.md"),
    }
    return plan


def main():
    import argparse
    parser = argparse.ArgumentParser(
        description="Generate audit plan for semantic-fidelity-audit skill"
    )
    parser.add_argument("chapter", type=int, help="Chapter number to audit")
    parser.add_argument("--corpus", type=str, default=None,
                        help="Path to textbook reference text (optional)")
    parser.add_argument("--json", action="store_true",
                        help="Output as JSON instead of human-readable")
    args = parser.parse_args()

    plan = generate_audit_plan(args.chapter, args.corpus)

    if args.json:
        print(json.dumps(plan, indent=2, ensure_ascii=False))
    else:
        print(f"# Audit Plan: Chapter {plan['chapter_no']} — {plan['chapter_title']}")
        print(f"  Corpus: {plan['corpus_path'] or 'NOT PROVIDED (NOT-INDEPENDENTLY-VERIFIED)'}")
        print(f"  Sections: {len(plan['sections'])}")
        for sec in plan["sections"]:
            print(f"    §{sec['section_no']} {sec['section_title']}")
            print(f"      State: {sec['migration_state']}")
            print(f"      Sources: {sec['source_modules']}")
        print()
        print(f"  Phase 1: spawn {len(plan['sections'])} auditor subagents (one per section)")
        print(f"  Phase 2: spawn {len(plan['sections'])} adversary subagents (one per section)")
        print(f"  Phase 3: synthesize report → docs/audits/ch{plan['chapter_no']:02d}-semantic-fidelity.md")
        print()
        print("  Reference files:")
        print(f"    Checklist:    {plan['checklist_path']}")
        print(f"    Verdict defs: {plan['verdict_defs_path']}")
        print(f"    Adversary:    {plan['adversary_playbook_path']}")


if __name__ == "__main__":
    main()
