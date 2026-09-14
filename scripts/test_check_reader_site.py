"""Reader result links must reach actual code, independently of coverage metadata."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.check_reader_site import unresolved_visible_results


class VisibleResultTests(unittest.TestCase):
    route = 'CLRSLean/FourthEdition/Chapter_16/Section_16_3_The_Potential_Method/'

    def page(self, href, target='<span class="const token" id="proof">fact</span>'):
        return (f'<a href="{href}" title="Definition of `CLRS.fact`">fact</a>'
                '<section class="clrs-implementation"><div class="code-box">'
                + target + ' := by trivial</div></section>')

    def test_result_cannot_remain_an_external_source_link_even_without_report(self):
        href = 'CLRSLean/Implementation/#CLRS___fact'
        self.assertEqual(unresolved_visible_results(self.page(href), self.route), [href])

    def test_visible_local_declaration_passes(self):
        self.assertEqual(unresolved_visible_results(self.page(self.route + '#proof'), self.route), [])

    def test_heading_is_not_a_concrete_declaration(self):
        href = self.route + '#proof'
        self.assertEqual(unresolved_visible_results(self.page(href, '<h3 id="proof">Summary</h3>'), self.route), [href])

    def test_external_library_link_is_not_transcluded(self):
        self.assertEqual(unresolved_visible_results(self.page('https://example.test/Mathlib/#fact'), self.route), [])


if __name__ == '__main__':
    unittest.main()
