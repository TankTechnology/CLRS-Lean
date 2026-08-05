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

    def test_pages_uses_four_stage_parallel_pipeline(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        for job in ("prepare:", "render:", "merge:", "deploy:"):
            self.assertIn(f"  {job}", pages)
        self.assertIn("shard: [0, 1, 2, 3]", pages)
        self.assertIn("needs: prepare", pages)
        self.assertIn("needs: [prepare, render]", pages)
        self.assertIn("needs: merge", pages)
        self.assertIn("actions/upload-artifact@v4", pages)
        self.assertIn("actions/download-artifact@v4", pages)

    def test_pages_validates_atomic_merge_before_single_deployment_artifact(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        commands = (
            "python3 scripts/apply_verso_patch.py",
            "python3 scripts/plan_literate_shards.py",
            "python3 scripts/render_literate_shard.py",
            "python3 scripts/merge_literate_shards.py",
            "python3 scripts/check_literate_html_weight.py",
            "python3 scripts/prepare_literate_site.py",
            "actions/upload-pages-artifact@v3",
        )
        for command in commands:
            self.assertIn(command, pages)

        plan_at = pages.index(commands[1])
        render_at = pages.index(commands[2])
        merge_at, guard_at, prepare_at, upload_at = map(pages.index, commands[3:])
        self.assertLess(plan_at, render_at)
        self.assertLess(render_at, merge_at)
        self.assertLess(merge_at, guard_at)
        self.assertLess(guard_at, prepare_at)
        self.assertLess(prepare_at, upload_at)
        self.assertNotIn("lake build :literateHtml", pages)


if __name__ == "__main__":
    unittest.main()
