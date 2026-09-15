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
        for job in ("plan:", "prepare:", "render:", "merge:", "refresh:", "deploy:"):
            self.assertIn(f"  {job}", pages)
        self.assertIn("shard: [0, 1, 2, 3]", pages)
        self.assertIn("needs: [plan, prepare]", pages)
        self.assertIn("needs: [prepare, render]", pages)
        self.assertIn("needs: [merge, refresh]", pages)
        self.assertIn("actions/upload-artifact@v4", pages)
        self.assertIn("actions/download-artifact@v4", pages)

    def test_pages_prunes_orphan_literate_json_before_cache_save(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        prepare = pages[pages.index("  prepare:") : pages.index("\n  render:")]

        build_at = prepare.index("lake build :literate")
        map_at = prepare.index("python3 scripts/prepare_literate_module_map.py")
        prune_at = prepare.index("--prune-orphans")
        save_at = prepare.index("actions/cache/save@v5")

        self.assertLess(build_at, map_at)
        self.assertLess(map_at, prune_at)
        self.assertLess(prune_at, save_at)

    def test_pages_validates_atomic_merge_before_single_deployment_artifact(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        commands = (
            "python3 scripts/apply_verso_patch.py",
            "python3 scripts/plan_literate_shards.py",
            "python3 scripts/render_literate_shard.py",
            "python3 scripts/merge_literate_shards.py",
            "python3 scripts/check_literate_html_weight.py",
            "python3 scripts/prepare_literate_site.py",
            "python3 scripts/check_literate_rendering.py _site",
            "actions/upload-pages-artifact@v3",
        )
        for command in commands:
            self.assertIn(command, pages)

        plan_at = pages.index(commands[1])
        render_at = pages.index(commands[2])
        merge_at, guard_at, prepare_at, rendering_at, upload_at = map(
            pages.index, commands[3:]
        )
        self.assertLess(plan_at, render_at)
        self.assertLess(render_at, merge_at)
        self.assertLess(merge_at, guard_at)
        self.assertLess(guard_at, prepare_at)
        self.assertLess(prepare_at, rendering_at)
        self.assertLess(rendering_at, upload_at)
        self.assertLess(prepare_at, upload_at)
        self.assertNotIn("lake build :literateHtml", pages)

    def test_refresh_skips_lean_and_requires_validation_before_upload(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        refresh = pages[pages.index("\n  refresh:"):pages.index("\n  deploy:")]
        self.assertNotIn("leanprover/lean-action", refresh)
        self.assertNotIn("lake build", refresh)
        self.assertIn("scripts/site_deploy.py refresh", refresh)
        self.assertIn("scripts/smoke_reader_book.py", refresh)
        self.assertLess(refresh.index("scripts/check_reader_site.py"),
                        refresh.index("actions/upload-pages-artifact"))
        self.assertLess(refresh.index("scripts/smoke_reader_site.py"),
                        refresh.index("actions/upload-pages-artifact"))

    def test_render_refresh_uses_separate_matrix_runners_without_lean(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        prepare = pages[pages.index("\n  prepare:"):pages.index("\n  render:")]
        render = pages[pages.index("\n  render:"):pages.index("\n  merge:")]
        refresh = pages[pages.index("\n  refresh:"):pages.index("\n  deploy:")]
        self.assertIn("if: needs.plan.outputs.mode == 'full' || needs.plan.outputs.mode == 'render'", prepare)
        self.assertIn("scripts/site_deploy.py prepare-inputs --plan plan.json", prepare)
        self.assertIn("fetch-depth: 0", prepare)
        # Compilation and cache writes are full-only. Cache recovery uses exact
        # existing entries and fails instead of compiling when either is absent.
        for step in prepare.split("      - ")[1:]:
            if any(token in step for token in ('leanprover/lean-action', 'lake build',
                                               'apply_verso_patch.py', 'actions/cache/save')):
                self.assertIn("if: needs.plan.outputs.mode == 'full'", step)
            if 'id: compiled-' in step and 'actions/cache/restore' in step:
                self.assertIn("needs.plan.outputs.inputs_source == 'cache'", step)
                self.assertIn('fail-on-cache-miss: true', step)
                self.assertNotIn('restore-keys:', step)
        self.assertIn("shard: [0, 1, 2, 3]", render)
        lean_step = next(step for step in render.split("      - ") if 'leanprover/lean-action' in step)
        self.assertIn("if: needs.plan.outputs.mode == 'full'", lean_step)
        self.assertIn("if: needs.plan.outputs.mode == 'assets' || needs.plan.outputs.mode == 'presentation'", refresh)
        inputs_upload = next(step for step in prepare.split("      - ")
                             if 'name: literate-inputs' in step and 'upload-artifact' in step)
        self.assertIn('retention-days: 90', inputs_upload)
        self.assertIn('compiled_sha=pathlib.Path("_site/compiled-revision.txt")', pages)

    def test_auto_routing_preserves_full_rebuild_and_guards_deployment(self) -> None:
        pages = PAGES.read_text(encoding="utf-8")
        self.assertIn("default: auto", pages)
        self.assertIn("options: [auto, refresh, full]", pages)
        prepare = pages[pages.index("\n  prepare:"):pages.index("\n  render:")]
        self.assertIn("needs: plan", prepare)
        self.assertIn("if: needs.plan.outputs.mode == 'full'", prepare)
        deploy = pages[pages.index("\n  deploy:"):]
        self.assertIn("always()", deploy)
        self.assertIn("needs.merge.result == 'success'", deploy)
        self.assertIn("needs.refresh.result == 'success'", deploy)
        self.assertIn("github.ref == 'refs/heads/main'", deploy)
        self.assertIn("name: reader-site", pages)
        self.assertIn("name: literate-raw", pages)
        self.assertIn("retention-days: 90", pages)


if __name__ == "__main__":
    unittest.main()
