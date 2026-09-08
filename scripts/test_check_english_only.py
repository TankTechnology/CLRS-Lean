#!/usr/bin/env python3
"""Tests for the English-only repository policy checker."""

from __future__ import annotations

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("check_english_only.py")


def load_checker():
    spec = importlib.util.spec_from_file_location("check_english_only", SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", *args], cwd=repo, text=True, stderr=subprocess.STDOUT
    ).strip()


class EnglishOnlyPolicyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.repo = Path(self.tempdir.name)
        git(self.repo, "init", "-b", "main")
        git(self.repo, "config", "user.name", "Policy Test")
        git(self.repo, "config", "user.email", "policy@example.com")

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def commit(self, name: str, text: str, message: str) -> None:
        (self.repo / name).write_text(text, encoding="utf-8")
        git(self.repo, "add", name)
        git(self.repo, "commit", "-m", message)

    def test_clean_repository_has_no_violations(self) -> None:
        self.commit("README.md", "English text.\n", "docs: add README")
        checker = load_checker()

        self.assertEqual(checker.collect_violations(self.repo), [])

    def test_reports_cjk_in_tracked_text_with_line_number(self) -> None:
        cjk_text = "\u4e2d\u6587\u5185\u5bb9"
        self.commit("README.md", f"English text.\n{cjk_text}\n", "docs: add README")
        checker = load_checker()

        violations = checker.collect_violations(self.repo, include_history=False)

        self.assertIn("README.md:2: tracked text contains CJK characters", violations)

    def test_reports_cjk_in_commit_message(self) -> None:
        message = "docs: \u6dfb\u52a0 README"
        self.commit("README.md", "English text.\n", message)
        checker = load_checker()

        violations = checker.collect_violations(self.repo, include_files=False)

        self.assertTrue(
            any("commit message contains CJK characters" in item for item in violations)
        )

    def test_reports_non_ascii_branch_name(self) -> None:
        self.commit("README.md", "English text.\n", "docs: add README")
        branch_name = "\u529f\u80fd\u5206\u652f"
        git(self.repo, "branch", branch_name)
        checker = load_checker()

        violations = checker.collect_violations(
            self.repo, include_files=False, include_history=False
        )

        self.assertIn(f"branch {branch_name}: branch name must be ASCII", violations)

    def test_ignores_binary_files(self) -> None:
        path = self.repo / "image.bin"
        path.write_bytes(b"\x00\xe4\xb8\xad\xe6\x96\x87")
        git(self.repo, "add", "image.bin")
        git(self.repo, "commit", "-m", "test: add binary fixture")
        checker = load_checker()

        self.assertEqual(checker.collect_violations(self.repo), [])

    def test_selected_ref_limits_history_scan(self) -> None:
        self.commit("README.md", "English text.\n", "docs: add README")
        clean_commit = git(self.repo, "rev-parse", "HEAD")
        message = "docs: \u6dfb\u52a0 changelog"
        self.commit("CHANGELOG.md", "English text.\n", message)
        checker = load_checker()

        violations = checker.collect_violations(
            self.repo, include_files=False, refs=[clean_commit]
        )

        self.assertEqual(violations, [])

    def test_ignores_tracked_file_deleted_from_worktree(self) -> None:
        self.commit("obsolete.md", "English text.\n", "docs: add obsolete file")
        (self.repo / "obsolete.md").unlink()
        checker = load_checker()

        self.assertEqual(
            checker.collect_violations(self.repo, include_history=False), []
        )


if __name__ == "__main__":
    unittest.main()
