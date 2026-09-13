"""Reader regressions: reading order, preserved scope, headings and TOC targets."""
import unittest
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.reader_layout import chapter_layout, chapter_toc, nest_headings, reader_chrome, canonical_section_title


class ReaderLayoutTests(unittest.TestCase):
    def test_section_titles_match_navigation_without_breaking_old_anchors(self):
        source = ('<header><h1>Site</h1></header><main><h1 id="old-title">Old <code>title</code></h1>'
                  '<p>Original scope.</p></main><nav class="page-toc">'
                  '<a href="section/#old-title">Old title</a><a href="section/#proof">Proof</a></nav>')
        result = canonical_section_title(source, '32.1. A & B')
        self.assertIn('<h1 id="old-title">32.1. A &amp; B</h1>', result)
        self.assertIn('<a href="section/#old-title">32.1. A &amp; B</a>', result)
        self.assertIn('<h1>Site</h1>', result)
        self.assertIn('<p>Original scope.</p>', result)
        self.assertIn('<a href="section/#proof">Proof</a>', result)
        self.assertEqual(result, canonical_section_title(result, '32.1. A & B'))

    def test_reading_pages_defer_full_text_but_search_page_keeps_index(self):
        source = '<script defer src="-verso-search/searchIndex.js"></script>'
        self.assertIn('src="clrs-search.js"', reader_chrome(source, 'chapter/'))
        search = source + '<main data-search-host></main>'
        self.assertIn('src="-verso-search/searchIndex.js"', reader_chrome(search, 'search/'))

    def test_skip_link_uses_page_route_despite_document_base(self):
        source = '<html><body><header class="title-bar"></header><main>Body</main></body></html>'
        result = reader_chrome(source, 'CLRSLean/FourthEdition/Chapter_26/')
        self.assertIn('href="CLRSLean/FourthEdition/Chapter_26/#clrs-main"', result)
        self.assertIn('id="clrs-main"', result)
        self.assertEqual(result, reader_chrome(result, 'CLRSLean/FourthEdition/Chapter_26/'))

    def test_reading_order_preserves_scope_and_original_anchors(self):
        guide = '<h1 id="title">Chapter 26</h1><h2 id="scope">Scope</h2><p>Power-of-two inputs only.</p>'
        body = '<section id="matrix"><h2>26.2. Matrices</h2><p>Algorithm</p></section>'
        result = chapter_layout(guide, body, [('matrix', '26.2. Matrices')], 'chapter/')
        self.assertLess(result.index('In this chapter'), result.index('Algorithm'))
        self.assertLess(result.index('Algorithm'), result.index('Power-of-two inputs only.'))
        self.assertEqual(result.count('id="title"'), 1)
        self.assertIn('id="scope"', result)
        self.assertIn('href="chapter/#matrix"', result)
        self.assertNotIn('<details', result)

    def test_embedded_headings_preserve_ids_and_inline_links(self):
        result = nest_headings('<h1 id="sec">Section <code>A</code></h1><h2 id="thm">Theorem</h2><a href="#thm">Proof</a>')
        self.assertIn('<h2 id="sec">', result)
        self.assertIn('<h3 id="thm">', result)
        self.assertIn('<a href="#thm">Proof</a>', result)
        self.assertNotIn('<h1', result)

    def test_toc_points_to_sections_and_scope_without_stale_guide_entries(self):
        result = chapter_toc('<nav aria-label="Contents" class="page-toc"><a href="#old">Old</a></nav>', [('s1', 'A & B')], 'chapter/')
        self.assertIn('chapter/#s1', result)
        self.assertIn('A &amp; B', result)
        self.assertIn('chapter/#clrs-chapter-notes', result)
        self.assertNotIn('#old', result)


if __name__ == '__main__':
    unittest.main()
