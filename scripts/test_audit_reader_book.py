from pathlib import Path
import sys
import unittest
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.audit_reader_book import Page, command_chunks, missing_commands, missing_compiled_modules


class WholeBookAuditTests(unittest.TestCase):
    def test_compiled_scoped_theorem_requires_the_whole_proof(self):
        compiled = {'items': {'tokens': {'0': {'content': 'set_option maxRecDepth 1000 in'},
                                         '1': {'content': 'theorem result : True := by trivial'}},
                              'code': {'0': {'token': {'tok': 0}}, '1': {'token': {'tok': 1}}},
                              'items': [{'defines': ['CLRS.result'], 'code': [{'highlighted': 0}, {'highlighted': 1}]}]}}
        chunks = list(command_chunks(compiled))
        self.assertEqual(missing_commands(Page('<div class="code-box">set_option maxRecDepth 1000 in</div>'), chunks), ['CLRS.result'])
        complete = Page('<div class="code-box">set_option maxRecDepth 1000 in</div><div class="code-box">theorem result : True := by trivial</div>')
        self.assertEqual(missing_commands(complete, chunks), [])

    def test_coverage_script_cannot_substitute_for_visible_proof(self):
        page = Page('<script type="application/json">theorem result : True := by trivial</script><p>theorem result : True := by trivial</p>')
        self.assertEqual(missing_commands(page, [(['CLRS.result'], ['theoremresult:True:=bytrivial'])]), ['CLRS.result'])

    def test_token_markup_does_not_change_the_compiled_text(self):
        page = Page('<div class="code-box"><pre><code><span>def</span> <a href="a/#b">x</a> := &lt;value&gt;</code></pre></div>')
        self.assertEqual(page.boxes, ['defx:=<value>'])
        self.assertEqual(page.links, ['a/#b'])

    def test_duplicate_ids_remain_detectable(self):
        self.assertEqual(Page('<span id="a"></span><span id="a"></span>').ids, ['a', 'a'])

    def test_hover_diagnostics_do_not_replace_or_interrupt_code(self):
        page = Page('<div class="code-box">if<span class="hover-container"><span class="hover-info">unused variable</span></span>h : p then a else b</div>')
        self.assertEqual(page.boxes, ['ifh:pthen aelseb'.replace(' ', '')])

    def test_incomplete_compiled_inputs_cannot_skip_a_required_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertEqual(missing_compiled_modules(root, ['CLRSLean.Required']), ['CLRSLean.Required'])
            (root / 'CLRSLean').mkdir()
            (root / 'CLRSLean/Required.json').write_text('{}')
            self.assertEqual(missing_compiled_modules(root, ['CLRSLean.Required']), [])


if __name__ == '__main__':
    unittest.main()
