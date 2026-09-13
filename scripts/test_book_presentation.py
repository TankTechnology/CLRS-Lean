"""Book presentation must preserve source content and chapter boundaries."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.book_presentation import present_book_page, book_metadata


class BookPresentationTests(unittest.TestCase):
    source = '<html><head></head><body><main><section class="code-content"><h1 id="old">Original</h1><p>Selected models only.</p></section></main></body></html>'

    def test_cover_retains_original_heading_target_and_scope(self):
        result = present_book_page(self.source, 'CLRSLean')
        self.assertIn('id="old"', result)
        self.assertIn('Selected models only.', result)
        self.assertEqual(result.count('<h1'), 1)
        self.assertIn('class="clrs-book-cover"', result)
        self.assertIn('width="720" height="680"', result)
        self.assertEqual(result, present_book_page(result, 'CLRSLean'))

    def test_first_and_last_chapters_have_no_nonexistent_neighbors(self):
        first = present_book_page(self.source, 'CLRSLean.FourthEdition.Chapter_01')
        last = present_book_page(self.source, 'CLRSLean.FourthEdition.Chapter_35')
        self.assertIn('Chapter_02/', first)
        self.assertNotIn('Chapter_00/', first)
        self.assertIn('Chapter_34/', last)
        self.assertNotIn('Chapter_36/', last)
        self.assertIn('clrs-book-colophon', last)
        self.assertIn('Selected models only.', last)

    def test_middle_chapter_links_include_names_and_site_relative_routes(self):
        result = present_book_page(self.source, 'CLRSLean.FourthEdition.Chapter_26')
        self.assertIn('CLRSLean/FourthEdition/Chapter_25/', result)
        self.assertIn('CLRSLean/FourthEdition/Chapter_27/', result)
        self.assertIn('Online Algorithms', result)
        self.assertNotIn('clrs-book-colophon', result)

    def test_metadata_is_absolute_escaped_and_idempotent(self):
        result = book_metadata(self.source, 'https://example.test/book/')
        self.assertIn('https://example.test/book/assets/book-social.png', result)
        self.assertEqual(result, book_metadata(result, 'https://example.test/book/'))


if __name__ == '__main__':
    unittest.main()
