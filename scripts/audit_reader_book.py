#!/usr/bin/env python3
"""Audit the whole published book, optionally against compiled Lean command bodies."""
from __future__ import annotations

import argparse
from collections import Counter
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urljoin, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.inline_chapter_sections import extract_code_content
from scripts.literate_navigation import canonical_sections
from scripts.reader_implementation import section_companions

VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}


def compact(text):
    return ''.join(text.replace('\u00ad', '').replace('\u200b', '').split())


class Page(HTMLParser):
    """Read real HTML text, never JSON coverage scripts or attribute values."""
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.boxes, self.paragraphs = [], [], [], []
        self.paragraph = None
        self.declarations = 0
        self.depth, self.box, self.ignored = 0, None, 0
        self.feed(text)
        self.close()
        self.code = ''.join(self.boxes)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.append(attrs['id'])
            if tag == 'span' and 'const' in attrs.get('class', '').split():
                self.declarations += 1
        if 'href' in attrs:
            self.links.append(attrs['href'])
        if tag == 'p' and self.box is None:
            self.paragraph = []
        if self.box is not None and tag not in VOID:
            self.depth += 1
            if self.ignored:
                self.ignored += 1
            elif set(attrs.get('class', '').split()) & {'hover-container', 'hover-info', 'verso-message'}:
                self.ignored = 1
        elif 'code-box' in attrs.get('class', '').split():
            self.box, self.depth = [], 1

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        if tag == 'p' and self.paragraph is not None:
            self.paragraphs.append(compact(''.join(self.paragraph)))
            self.paragraph = None
        if self.box is not None and tag not in VOID:
            if self.ignored:
                self.ignored -= 1
            self.depth -= 1
            if self.depth == 0:
                self.boxes.append(compact(''.join(self.box)))
                self.box = None

    def handle_data(self, text):
        if self.box is not None and not self.ignored:
            self.box.append(text)
        if self.paragraph is not None and not self.ignored:
            self.paragraph.append(text)


def highlighted_text(items, key):
    """Decode the existing compiled highlight tree without executing Lean."""
    stack, result = [key], []
    while stack:
        node = items['code'][str(stack.pop())]
        if 'text' in node:
            result.append(node['text']['str'])
        elif 'token' in node:
            result.append(items['tokens'][str(node['token']['tok'])]['content'])
        elif 'seq' in node:
            stack.extend(reversed(node['seq']['highlights']))
        elif 'tactics' in node:
            stack.append(node['tactics']['content'])
        elif 'span' in node:
            stack.append(node['span']['content'])
        elif 'point' not in node:
            raise ValueError(f'unknown compiled highlight node: {list(node)}')
    return ''.join(result)


def command_chunks(compiled):
    items = compiled['items']
    for command in items['items']:
        if command['defines']:
            chunks = [compact(highlighted_text(items, part['highlighted']))
                      for part in command['code'] if 'highlighted' in part]
            yield command['defines'], [chunk for chunk in chunks if chunk]


def missing_commands(page, commands):
    return [names[0] for names, parts in commands
            if not parts or any(part not in page.code for part in parts)]


def missing_compiled_modules(compiled, modules):
    return [module for module in sorted(set(modules))
            if not compiled.joinpath(*module.split('.')).with_suffix('.json').is_file()]


def audit(site: Path, compiled: Path | None = None):
    site = site.resolve()
    sections = sorted(canonical_sections())
    chapters = [f'CLRSLean.FourthEdition.Chapter_{n:02d}' for n in range(1, 36)]
    reader_modules = ['CLRSLean', 'CLRSLean.FourthEdition', *chapters, *sections]
    companions = section_companions(ROOT, sections)
    selections = json.loads((ROOT / 'docs/literate/reader-implementations.json').read_text())
    errors, records, ids = [], {}, {}
    pages = {}
    link_count = 0

    def load(module):
        path = site.joinpath(*module.split('.'), 'index.html')
        if module not in pages:
            if not path.is_file():
                raise ValueError(f'missing page: {module}')
            pages[module] = Page(path.read_text())
        return pages[module]

    # Every reader link is checked, including fragments on other pages.
    for module in reader_modules:
        try:
            page = load(module)
        except ValueError as exc:
            errors.append(str(exc))
            continue
        duplicates = [identifier for identifier, n in Counter(page.ids).items() if n > 1]
        if duplicates:
            errors.append(f'{module}: duplicate IDs: {duplicates[:3]}')
        for href in page.links:
            url = urlsplit(urljoin('https://reader.test/', href))
            if url.netloc != 'reader.test':
                continue
            link_count += 1
            path = site / unquote(url.path).lstrip('/')
            if url.path.endswith('/'):
                path /= 'index.html'
            if not path.resolve().is_relative_to(site) or not path.is_file():
                errors.append(f'{module}: missing link target: {href}')
                continue
            if url.fragment and path.suffix == '.html':
                if path not in ids:
                    # Reference destinations do not need a second full HTML parse.
                    import html
                    ids[path] = {html.unescape(x) for x in re.findall(r'\bid="([^"]+)"', path.read_text())}
                if unquote(url.fragment) not in ids[path]:
                    errors.append(f'{module}: missing anchor: {href}')

    coverage_path = site / 'reader-implementation-coverage.json'
    coverage = json.loads(coverage_path.read_text()) if coverage_path.is_file() else {}
    for chapter in chapters:
        children = [s for s in sections if s.startswith(chapter + '.')]
        text = site.joinpath(*chapter.split('.'), 'index.html').read_text()
        rows = []
        for section in children:
            page = load(section)
            section_text = site.joinpath(*section.split('.'), 'index.html').read_text()
            prose = Page(extract_code_content(section_text, section)).paragraphs
            match = re.search(r'<section\b[^>]*data-module="' + re.escape(section) + '"[^>]*>', text)
            embedded = Page(extract_code_content(text[match.start():], section)) if match else None
            if embedded is None:
                errors.append(f'{section}: missing chapter body')
            else:
                for box in page.boxes:
                    if box and box not in embedded.code:
                        errors.append(f'{section}: chapter lost a code/proof block: {box[:100]}')
                for paragraph in prose:
                    if paragraph and paragraph not in embedded.paragraphs:
                        errors.append(f'{section}: chapter lost a prose paragraph: {paragraph[:100]}')
            expected = set(companions.get(section, [])) if section not in selections else set()
            report = coverage.get(section, {})
            rows.append(dict(module=section, code_blocks=len(page.boxes),
                             declarations=page.declarations,
                             owned_companions=len(expected),
                             selected_declarations=sum(len(names or []) for names in selections.get(section, {}).values()),
                             included_sources=sorted(report.get('sources', {}))))
        records[chapter] = dict(sections=rows, section_count=len(children),
                                code_blocks=len(load(chapter).boxes),
                                declarations=load(chapter).declarations,
                                exposition_only=chapter.endswith('Chapter_01'))

    compiled_modules, commands, chunks = 0, 0, 0
    # Each compiled definition-bearing command must remain readable in its source
    # page. This catches whole theorems hidden by renderer configuration.
    if compiled is not None:
        required = set(reader_modules)
        required.update(module for sources in companions.values() for module in sources)
        required.update(module for sources in selections.values() for module in sources)
        for module in missing_compiled_modules(compiled, required):
            errors.append(f'{module}: missing required compiled input')
        for path in sorted(compiled.rglob('*.json')):
            data = json.loads(path.read_text())
            module = data['module']
            target = site.joinpath(*module.split('.'), 'index.html')
            if not target.is_file():
                errors.append(f'{module}: compiled source has no published page')
                continue
            page = pages.get(module) or Page(target.read_text())
            module_chunks = list(command_chunks(data))
            compiled_modules += 1
            if compiled_modules % 200 == 0:
                print(f'Audited {compiled_modules} compiled modules', flush=True)
            for names, parts in module_chunks:
                commands += 1
                if not parts:
                    errors.append(f'{module}: no highlighted body for {names[0]}')
                for part in parts:
                    chunks += 1
                    if part not in page.code:
                        errors.append(f'{module}: missing compiled body for {names[0]}: {part[:100]}')
            # Normal split sections include all owned command bodies. Curated
            # facades have an explicit, independently checked declaration list.
            owners = [s for s in sections if s not in selections and module in companions[s]]
            for owner in owners:
                visible = load(owner).code
                for names, parts in module_chunks:
                    if any(part not in visible for part in parts):
                        errors.append(f'{owner}: missing owned implementation {module}: {names[0]}')
            for owner, sources in selections.items():
                if module not in sources:
                    continue
                selected = sources[module]
                found = set()
                for names, parts in module_chunks:
                    requested = set(names) if selected is None else set(names) & set(selected)
                    found.update(requested)
                    if requested and any(part not in load(owner).code for part in parts):
                        errors.append(f'{owner}: missing selected implementation {module}: {sorted(requested)[0]}')
                if selected is not None:
                    for name in set(selected) - found:
                        errors.append(f'{owner}: selected declaration absent from compiled input: {name}')
    for chapter, row in records.items():
        row['status'] = 'failed' if any(error.startswith((chapter + '.', chapter + ':')) for error in errors) else 'passed'
    return dict(chapters=records, summary=dict(chapters=len(chapters), sections=len(sections),
                reader_pages=len(reader_modules), local_links=link_count,
                compiled_modules=compiled_modules, compiled_commands=commands, compiled_chunks=chunks),
                errors=sorted(set(errors)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--compiled', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = audit(args.site, args.compiled)
    output = args.output or args.site / 'reader-book-audit.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['summary']))
    for failure in report['errors'][:30]:
        print(failure)
    print(f'Whole-book audit: {len(report["errors"])} errors; report {output}')
    return bool(report['errors'])


if __name__ == '__main__':
    sys.exit(main())
