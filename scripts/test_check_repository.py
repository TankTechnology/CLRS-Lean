import unittest

from check_repository import strip_markdown_fenced_code


class StripMarkdownFencedCodeTest(unittest.TestCase):
    def test_ignores_links_in_backtick_fences(self) -> None:
        text = """[real](real.md)\n```markdown\n[example](missing.md)\n```\n"""

        stripped = strip_markdown_fenced_code(text)

        self.assertIn("[real](real.md)", stripped)
        self.assertNotIn("[example](missing.md)", stripped)
        self.assertEqual(text.count("\n"), stripped.count("\n"))

    def test_ignores_links_in_tilde_fences(self) -> None:
        text = """~~~text\n[example](missing.md)\n~~~~\n[real](real.md)\n"""

        stripped = strip_markdown_fenced_code(text)

        self.assertNotIn("[example](missing.md)", stripped)
        self.assertIn("[real](real.md)", stripped)
        self.assertEqual(text.count("\n"), stripped.count("\n"))


if __name__ == "__main__":
    unittest.main()
