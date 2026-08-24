#!/usr/bin/env python3
"""Contract tests for the repository-local complexity reduction skill."""

from __future__ import annotations

import json
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKILL_DIR = ROOT / ".codex" / "skills" / "complexity-reduction-closure"
SKILL_FILE = SKILL_DIR / "SKILL.md"
EVAL_FILE = SKILL_DIR / "evals" / "evals.json"
CHAPTER_SKILL_FILE = ROOT / ".codex" / "skills" / "clrs-chapter-formalization" / "SKILL.md"

REFERENCE_NAMES = {
    "reduction-contract.md",
    "np-membership-contract.md",
    "semantic-to-machine.md",
    "encoding-and-malformed-input.md",
    "polynomial-bound-composition.md",
    "ch34-case-study.md",
}

DRY_RUN_NAMES = {
    "clique-to-vertex-cover-dry-run.md",
    "ham-cycle-gadget-dry-run.md",
    "subset-sum-numeric-dry-run.md",
}

REQUIRED_STATUSES = {
    "semantic-only",
    "size-certified",
    "machine-certified",
    "reduction-complete",
    "np-complete",
}

REQUIRED_EVAL_IDS = {
    "clique-to-vertex-cover",
    "ham-cycle-gadget",
    "subset-sum-numeric",
}


class ComplexityReductionClosureSkillTest(unittest.TestCase):
    """Check the skill package's stable public contract."""

    def read_required(self, path: Path) -> str:
        self.assertTrue(path.is_file(), f"missing required file: {path.relative_to(ROOT)}")
        return path.read_text(encoding="utf-8")

    def test_required_package_files_exist(self) -> None:
        self.assertTrue(SKILL_FILE.is_file(), "missing skill entrypoint")
        for name in sorted(REFERENCE_NAMES):
            self.assertTrue(
                (SKILL_DIR / "references" / name).is_file(),
                f"missing reference: {name}",
            )
        self.assertTrue(EVAL_FILE.is_file(), "missing evaluation fixture")
        for name in sorted(DRY_RUN_NAMES):
            self.assertTrue(
                (SKILL_DIR / "evals" / name).is_file(),
                f"missing dry run: {name}",
            )

    def test_skill_declares_closure_statuses_and_valid_reference_links(self) -> None:
        text = self.read_required(SKILL_FILE)
        for status in sorted(REQUIRED_STATUSES):
            self.assertIn(status, text, f"missing closure status: {status}")

        links = set(re.findall(r"references/([a-z0-9-]+\.md)", text))
        self.assertEqual(REFERENCE_NAMES, links)
        for name in links:
            self.assertTrue((SKILL_DIR / "references" / name).is_file())

    def test_evaluation_fixture_has_three_grounded_cases(self) -> None:
        raw = self.read_required(EVAL_FILE)
        payload = json.loads(raw)
        self.assertEqual("complexity-reduction-closure", payload["skill_name"])
        evaluations = payload["evals"]
        self.assertEqual(REQUIRED_EVAL_IDS, {entry["id"] for entry in evaluations})
        for entry in evaluations:
            self.assertTrue(entry["prompt"].strip())
            self.assertTrue(entry["expected_output"].strip())
            self.assertIsInstance(entry["files"], list)

    def test_dry_runs_expose_the_common_report_surface(self) -> None:
        for name in sorted(DRY_RUN_NAMES):
            text = self.read_required(SKILL_DIR / "evals" / name)
            for heading in (
                "## Closure ledger",
                "## First missing bridge",
                "## File decomposition",
                "## Narrow verification",
            ):
                self.assertIn(heading, text, f"{name} omits {heading}")

    def test_chapter_skill_routes_complexity_reductions(self) -> None:
        text = self.read_required(CHAPTER_SKILL_FILE)
        self.assertIn("complexity-reduction-closure", text)
        self.assertRegex(text, r"polynomial-time reductions.*NP-completeness")


if __name__ == "__main__":
    unittest.main()
