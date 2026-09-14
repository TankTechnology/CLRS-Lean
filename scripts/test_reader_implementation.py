import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import reader_implementation as reader


FACADE = 'CLRSLean.FourthEdition.Chapter_01.Section_01_1'
A, B, C = 'CLRSLean.Implementation.A', 'CLRSLean.Implementation.B', 'CLRSLean.Implementation.C'


def route(module):
    return module.replace('.', '/') + '/'


def imports(*modules):
    return '<details class="imports-list"><summary>Imports</summary>' + ''.join(
        f'<a href="{route(m)}"><span class="module-name">{m}</span></a>' for m in modules) + '</details>'


def declaration(name, proof='by\n  exact True.intro', extra=''):
    return (f'<div class="verso-text mod-doc"><p>Documentation for {name}</p></div>'
            f'<div class="code-box"><code><span class="keyword">theorem</span> '
            f'<span class="const token" id="{name.replace(".", "___")}" data-binding="const-{name}">{name}</span>'
            f' : True := <span class="proof">{proof}</span>{extra}</code></div>')


class EnrichmentTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.site = Path(self.temp.name)

    def page(self, module, body):
        path = self.site / route(module) / 'index.html'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('<html><head><base href="/"></head><body><main>'
                        '<section class="code-content">' + body + '</section></main></body></html>')
        return path

    def facade(self, *modules, links=''):
        return self.page(FACADE, imports(*modules) + '<h1>Guide</h1>' + links +
                         '<div class="code-box"><code><span class="keyword">namespace</span> CLRS</code></div>')

    def test_namespace_facade_gets_full_proof_docs_and_source(self):
        path = self.facade(A)
        proof = 'by\n  have h : True := True.intro\n  exact h'
        self.page(A, imports('Mathlib') + '<h1>Implementation</h1>' + declaration('CLRS.fact', proof))
        result = reader.enrich_sections(self.site, [FACADE], {})
        html = path.read_text()
        self.assertEqual(result.sections, 1)
        self.assertEqual(result.declarations, 1)
        self.assertIn(proof, html)
        self.assertIn('Documentation for CLRS.fact', html)
        self.assertIn('Definitions and proofs', html)
        self.assertEqual(html.count('<h1'), 1)
        self.assertEqual(html.count('class="imports-list"'), 1)
        self.assertIn('clrs-implementation-source', html)
        self.assertIn(f'href="{route(A)}"', html)
        self.assertEqual(result.coverage[FACADE]['sources'][A], ['CLRS.fact'])
        json.dumps(result.coverage)

    def test_recursive_imports_deduplicate_shared_module(self):
        path = self.facade(A, B)
        self.page(A, imports(C))
        self.page(B, imports(C))
        self.page(C, declaration('CLRS.fact'))
        result = reader.enrich_sections(self.site, [FACADE], {})
        self.assertEqual(result.sources, 1)
        self.assertEqual(path.read_text().count('Documentation for CLRS.fact'), 1)

    def test_cycles_missing_imports_and_empty_facades_fail(self):
        self.facade(A)
        self.page(A, imports(B))
        self.page(B, imports(A))
        with self.assertRaisesRegex(ValueError, 'cycle'):
            reader.enrich_sections(self.site, [FACADE], {})
        self.page(A, imports(C))
        with self.assertRaisesRegex(ValueError, 'missing'):
            reader.enrich_sections(self.site, [FACADE], {})
        self.page(A, '<p>No implementation</p>')
        with self.assertRaisesRegex(ValueError, 'declaration|implementation'):
            reader.enrich_sections(self.site, [FACADE], {})

    def test_selection_keeps_entire_code_box_and_caller_dependencies(self):
        path = self.facade(A)
        self.page(A, declaration('CLRS.chosen', extra=f'<a href="{route(B)}#CLRS___dependency">dependency</a>')
                  + declaration('CLRS.unselected'))
        self.page(B, declaration('CLRS.dependency'))
        result = reader.enrich_sections(self.site, [FACADE],
                                        {FACADE: {A: ['CLRS.chosen'], B: ['CLRS.dependency']}})
        html = path.read_text()
        self.assertIn('Documentation for CLRS.chosen', html)
        self.assertIn('exact True.intro', html)
        self.assertNotIn('CLRS.unselected', html)
        self.assertEqual(result.declarations, 2)
        self.assertRegex(html, re.escape(route(FACADE)) + r'#clrs-implementation-[^"]+CLRS___dependency')

    def test_guide_result_adds_missing_block_and_points_to_visible_target(self):
        original = f'/{route(B)}#CLRS%5F%5F%5Fresult'
        path = self.facade(A, links=f'<a title="Definition of `CLRS.result`" href="{original}">result</a>'
                          '<a href="https://example.org/CLRSLean/B/#x">external</a>')
        self.page(A, declaration('CLRS.primary'))
        self.page(B, declaration('CLRS.result') + declaration('CLRS.unrelated'))
        result = reader.enrich_sections(self.site, [FACADE], {})
        html = path.read_text()
        report = result.coverage[FACADE]['resolved_guide_links'][0]
        self.assertEqual(report['source'], B)
        self.assertIn(f'id="{report["target"]}"', html)
        self.assertIn(f'href="{route(FACADE)}#{report["target"]}"', html)
        self.assertIn('https://example.org/CLRSLean/B/#x', html)
        self.assertNotIn('CLRS.unrelated', html)

    def test_missing_selected_declaration_or_guide_target_fails(self):
        self.facade(A)
        self.page(A, declaration('CLRS.fact'))
        with self.assertRaisesRegex(ValueError, 'missing.*declaration|declaration.*missing'):
            reader.enrich_sections(self.site, [FACADE], {FACADE: {A: ['CLRS.nope']}})
        self.facade(A, links=f'<a title="Definition of x" href="{route(A)}#missing">x</a>')
        with self.assertRaisesRegex(ValueError, 'missing.*target|target.*missing'):
            reader.enrich_sections(self.site, [FACADE], {})

    def test_duplicate_ids_local_links_and_aria_are_namespaced(self):
        path = self.facade(A, B)
        extras = '<span id="label">first</span><span id="label">second</span><span id="label--duplicate-2">reserved</span><a href="#label">local</a><span aria-labelledby="label">use</span>'
        self.page(A, declaration('CLRS.a', extra=extras))
        self.page(B, declaration('CLRS.b', extra=extras))
        reader.enrich_sections(self.site, [FACADE], {})
        html = path.read_text()
        ids = re.findall(r'\bid="([^"]+)"', html)
        self.assertEqual(len(ids), len(set(ids)))
        refs = re.findall(r'aria-labelledby="([^"]+)"', html)
        self.assertTrue(all(ref in ids for ref in refs))
        self.assertNotIn('href="#label"', html)

    def test_non_id_attributes_and_unquoted_ids_are_handled(self):
        path = self.facade(A)
        self.page(A, declaration('CLRS.fact', extra='<span id=label data-id="untouched" title="text id=sample">label</span><a href=#label>label</a>'))
        reader.enrich_sections(self.site, [FACADE], {})
        html = path.read_text()
        self.assertIn('data-id="untouched"', html)
        self.assertIn('title="text id=sample"', html)
        self.assertNotIn('id=label', html)
        self.assertNotIn('href=#label', html)

    def test_multiple_facades_use_original_sources_independent_of_order(self):
        reports = []
        for order in ([A, FACADE], [FACADE, A]):
            self.facade(A)
            self.page(A, imports(C) + '<h1>Intermediate facade</h1>')
            self.page(C, declaration('CLRS.fact'))
            result = reader.enrich_sections(self.site, order, {})
            reports.append(result.coverage)
            self.assertEqual(result.coverage[FACADE]['sources'], {C: ['CLRS.fact']})
            self.assertEqual((self.site / route(FACADE) / 'index.html').read_text().count('data-clrs-implementation-report'), 1)
        self.assertEqual(reports[0], reports[1])

    def test_coverage_script_escapes_html_and_proof_details_are_open(self):
        path = self.facade(A, links=f'<a title="Definition of fact" href="{route(A)}?q=&lt;/script&gt;#CLRS___fact">fact</a>')
        self.page(A, '<details><summary>Proof</summary>' + declaration('CLRS.fact') + '</details>')
        reader.enrich_sections(self.site, [FACADE], {})
        html = path.read_text()
        self.assertIn('<details open>', html)
        self.assertIn('\\u003c/script>', html)
        self.assertEqual(html.count('</script>'), 1)
        self.assertEqual(reader.enrich_sections(self.site, [FACADE], {}).sections, 0)

    def test_existing_declarations_and_repeat_calls_do_not_duplicate(self):
        native = self.page(A, declaration('CLRS.native'))
        before = native.read_text()
        self.assertEqual(reader.enrich_sections(self.site, [A], {}).sections, 0)
        self.assertEqual(native.read_text(), before)
        path = self.facade(A)
        first = reader.enrich_sections(self.site, [FACADE], {})
        enriched = path.read_text()
        second = reader.enrich_sections(self.site, [FACADE], {})
        self.assertEqual(second.sections, 0)
        self.assertEqual(first.coverage, second.coverage)
        self.assertEqual(path.read_text(), enriched)

    def test_traversal_is_rejected_and_limit_preserves_original(self):
        path = self.facade(A)
        self.page(A, declaration('CLRS.fact'))
        before = path.read_text()
        with self.assertRaises(ValueError):
            reader.enrich_sections(self.site, [FACADE], {FACADE: {'CLRSLean...escape': None}})
        with patch.object(reader, 'MAX_INSERTED_BYTES', 10), self.assertRaisesRegex(ValueError, 'limit|MiB|bytes'):
            reader.enrich_sections(self.site, [FACADE], {})
        self.assertEqual(path.read_text(), before)
        self.facade(A, links='<a title="Definition of x" href="CLRSLean/%2e%2e/escape/#x">x</a>')
        with self.assertRaisesRegex(ValueError, 'unsafe|traversal'):
            reader.enrich_sections(self.site, [FACADE], {})


if __name__ == '__main__':
    unittest.main()
