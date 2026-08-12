import unittest

import check_repository
from check_repository import strip_markdown_fenced_code


class StripMarkdownFencedCodeTest(unittest.TestCase):
    def test_ignores_links_in_backtick_fences(self) -> None:
        text = """[real](real.md)\n```markdown\n[example](missing.md)\n```\n"""

        stripped = strip_markdown_fenced_code(text)

        self.assertIn("[real](real.md)", stripped)
        self.assertNotIn("[example](missing.md)", stripped)
        self.assertEqual(text.count("\n"), stripped.count("\n"))


class GeneratedDocumentationCheckTest(unittest.TestCase):
    def test_repository_checks_generated_readme(self) -> None:
        self.assertTrue(hasattr(check_repository, "CHECK_COMMANDS"))
        self.assertIn(
            ("scripts/check_progress_csv.py", "--check-dashboard"),
            check_repository.CHECK_COMMANDS,
        )
        self.assertIn(
            ("scripts/gen_readme_table.py", "--check"),
            check_repository.CHECK_COMMANDS,
        )

    def test_repository_runs_site_consistency_regressions(self) -> None:
        self.assertIn(
            ("scripts/test_check_site_consistency.py",),
            check_repository.CHECK_COMMANDS,
        )

    def test_ignores_links_in_tilde_fences(self) -> None:
        text = """~~~text\n[example](missing.md)\n~~~~\n[real](real.md)\n"""

        stripped = strip_markdown_fenced_code(text)

        self.assertNotIn("[example](missing.md)", stripped)
        self.assertIn("[real](real.md)", stripped)
        self.assertEqual(text.count("\n"), stripped.count("\n"))


if __name__ == "__main__":
    unittest.main()
