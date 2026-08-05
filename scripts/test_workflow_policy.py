#!/usr/bin/env python3
"""Regression tests for the repository's manual-only GitHub workflows."""

from __future__ import annotations

import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = (
    ROOT / ".github" / "workflows" / "lean_action_ci.yml",
    ROOT / ".github" / "workflows" / "pages.yml",
)
PAGES = WORKFLOWS[1]
AUTOMATIC_TRIGGERS = ("push:", "pull_request:", "schedule:", "workflow_run:")


def trigger_block(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    start = text.index("on:")
    end = text.index("\n\n", start)
    return text[start:end]


class WorkflowPolicyTests(unittest.TestCase):
    def test_all_workflows_are_manual_only(self) -> None:
        for workflow in WORKFLOWS:
            block = trigger_block(workflow)
            with self.subTest(workflow=workflow.name):
                self.assertIn("workflow_dispatch:", block)
                for trigger in AUTOMATIC_TRIGGERS:
                    self.assertNotIn(trigger, block)

    def test_pages_applies_patch_and_guards_raw_html_in_order(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        commands = (
            "python3 scripts/apply_verso_patch.py",
            "lake build :literateHtml",
            "python3 scripts/check_literate_html_weight.py",
            "python3 scripts/prepare_literate_site.py",
        )
        for command in commands:
            self.assertIn(command, pages)

        patch_at, build_at, guard_at, prepare_at = map(pages.index, commands)
        self.assertLess(patch_at, build_at)
        self.assertLess(build_at, guard_at)
        self.assertLess(guard_at, prepare_at)


if __name__ == "__main__":
    unittest.main()
