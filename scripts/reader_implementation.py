"""Embed existing rendered Lean declarations and complete proofs in reader facades."""
from __future__ import annotations

from dataclasses import dataclass, field
from html import escape, unescape
from html.parser import HTMLParser
import csv
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit

from scripts.inline_chapter_sections import _code_content_bounds

MAX_INSERTED_BYTES = 12 * 1024 * 1024
MARKER = 'data-clrs-implementation="true"'
VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'param', 'source', 'track', 'wbr'}
ATTR = re.compile(r"(?P<name>[^\s=<>/]+)\s*=\s*(?:(?P<q>['\"])(?P<value>.*?)(?P=q)|(?P<bare>[^\s>]+))", re.S)
ID_REFS = {'aria-labelledby', 'aria-describedby', 'aria-controls', 'aria-owns', 'aria-activedescendant', 'headers', 'for'}


@dataclass
class ImplementationEnrichmentResult:
    sections: int = 0
    sources: int = 0
    declarations: int = 0
    resolved_guide_links: int = 0
    coverage: dict = field(default_factory=dict)


@dataclass(eq=False)
class Node:
    tag: str
    attrs: dict
    start: int
    start_end: int
    end_start: int = 0
    end: int = 0
    parent: Node | None = None
    children: list = field(default_factory=list)

    def has_class(self, value):
        return value in self.attrs.get('class', '').split()


class Document(HTMLParser):
    """Keep source offsets so unchanged proof markup is copied without reserialization."""
    def __init__(self, text):
        super().__init__(convert_charrefs=False)
        self.text, self.nodes, self.stack = text, [], []
        self.lines = [0] + [m.end() for m in re.finditer('\n', text)]
        self.feed(text)
        self.close()
        if self.stack:
            raise ValueError(f'unbalanced implementation HTML: {self.stack[-1].tag}')

    def source_offset(self):
        line, column = self.getpos()
        return self.lines[line - 1] + column

    def handle_starttag(self, tag, attrs):
        start = self.source_offset()
        node = Node(tag, dict(attrs), start, start + len(self.get_starttag_text()),
                    parent=self.stack[-1] if self.stack else None)
        self.nodes.append(node)
        if node.parent:
            node.parent.children.append(node)
        if tag in VOID:
            node.end_start = node.end = node.start_end
        else:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            node = self.stack.pop()
            node.end_start = node.end = node.start_end

    def handle_endtag(self, tag):
        if not self.stack or self.stack[-1].tag != tag:
            raise ValueError(f'unbalanced implementation HTML closing tag: {tag}')
        node = self.stack.pop()
        node.end_start = self.source_offset()
        node.end = self.text.index('>', node.end_start) + 1

    def declarations(self):
        result = {}
        for node in self.nodes:
            if node.tag != 'span' or not node.has_class('const') or not node.attrs.get('id'):
                continue
            box = node.parent
            while box and not box.has_class('code-box'):
                box = box.parent
            if box:
                binding = node.attrs.get('data-binding', '')
                name = binding[6:] if binding.startswith('const-') else node.attrs['id'].replace('___', '.')
                result[name] = (node, box)
        return result


def module_route(module):
    if not re.fullmatch(r'CLRSLean(?:\.[A-Za-z0-9_]+)*', module):
        raise ValueError(f'unsafe project module: {module}')
    return module.replace('.', '/') + '/'


def project_target(href, current):
    parsed = urlsplit(unescape(href))
    if parsed.scheme or parsed.netloc:
        return None
    path, fragment = unquote(parsed.path), unquote(parsed.fragment)
    if not path:
        return current, fragment
    stripped = path.lstrip('/')
    if stripped.startswith('CLRS-Lean/'):
        stripped = stripped[len('CLRS-Lean/'):]
    if not stripped.startswith('CLRSLean/'):
        return None
    parts = stripped.split('/')
    if any(part in {'.', '..'} for part in parts) or '\\' in stripped:
        raise ValueError(f'unsafe project route traversal: {href}')
    if parts[-1] == 'index.html':
        parts.pop()
    if parts[-1] == '':
        parts.pop()
    module = '.'.join(parts)
    module_route(module)
    return module, fragment


def namespace(destination, source, identifier):
    return 'clrs-implementation-' + destination.replace('.', '___') + '--' + source.replace('.', '___') + '--' + identifier


def imports(document, current):
    result = []
    for node in document.nodes:
        if not node.has_class('imports-list'):
            continue
        for child in document.nodes:
            if not node.start_end <= child.start < node.end_start:
                continue
            target = project_target(child.attrs['href'], current) if child.tag == 'a' and child.attrs.get('href') else None
            binding = child.attrs.get('data-binding', '')
            module = target[0] if target else binding.removeprefix('module-name-')
            if module.startswith('CLRSLean.') and module not in result:
                module_route(module)
                result.append(module)
    return result


def guide_links(document, current):
    for node in document.nodes:
        if node.tag == 'a' and node.attrs.get('title', '').lower().startswith('definition of'):
            parent = node.parent
            while parent and not parent.has_class('code-box'):
                parent = parent.parent
            if parent:
                continue
            target = project_target(node.attrs.get('href', ''), current)
            if target:
                yield node, target


def section_companions(root: Path, modules: list[str]) -> dict[str, list[str]]:
    """Inventory section-owned sources, including split files omitted from navigation."""
    source = root / 'src'
    mapping = root / 'docs/clrs-fourth-edition-map.csv'
    rows = []
    if mapping.is_file():
        with mapping.open() as handle:
            rows = list(csv.DictReader(handle))
    result = {}
    for module in modules:
        roots = [module]
        for row in rows:
            mapped = [item.strip() for item in row['source_modules'].split(';')]
            if mapped and module == mapped[0]:
                roots.extend(mapped)
        owned = []
        for item in dict.fromkeys(roots):
            module_route(item)
            if item != module:
                owned.append(item)
            directory = source.joinpath(*item.split('.'))
            if directory.is_dir():
                owned.extend('.'.join(p.relative_to(source).with_suffix('').parts)
                             for p in sorted(directory.rglob('*.lean')))
        result[module] = list(dict.fromkeys(m for m in owned if m != module))
    return result


def selected_content(document, names, source):
    declarations = document.declarations()
    if names is None:
        ranges = [(n.start, n.end) for n in document.nodes if n.has_class('imports-list')]
        return apply_edits(document.text, [(a, b, '') for a, b in ranges])
    boxes = set()
    for name in names:
        if name not in declarations:
            raise ValueError(f'missing selected declaration {name} in {source}')
        boxes.add(declarations[name][1])
    selected = set(boxes)
    for box in boxes:
        siblings = box.parent.children if box.parent else [n for n in document.nodes if n.parent is None]
        index = siblings.index(box)
        if index and siblings[index - 1].has_class('verso-text'):
            selected.add(siblings[index - 1])
    return '\n'.join(document.text[n.start:n.end] for n in sorted(selected, key=lambda n: n.start))


def apply_edits(text, edits):
    chunks, cursor = [], 0
    for start, end, replacement in sorted(edits):
        if start < cursor:
            raise ValueError('overlapping implementation HTML edits')
        chunks.extend((text[cursor:start], replacement))
        cursor = end
    chunks.append(text[cursor:])
    return ''.join(chunks)


def rewrite(document, source, destination, targets, embedded):
    edits, occurrences = [], {}
    reserved_ids = set(targets.values())
    for node in document.nodes:
        tag = document.text[node.start:node.start_end]
        def replace(match):
            key = match['name'].lower()
            if key not in {'id', 'href'} | ID_REFS:
                return match[0]
            value = unescape(match['value'] if match['value'] is not None else match['bare'])
            updated = value
            if key == 'id' and embedded:
                occurrences[value] = occurrences.get(value, 0) + 1
                updated = targets[(source, value)]
                if occurrences[value] > 1:
                    number = occurrences[value]
                    while f'{updated}--duplicate-{number}' in reserved_ids:
                        number += 1
                    updated += f'--duplicate-{number}'
                    reserved_ids.add(updated)
            elif key == 'href':
                target = project_target(value, source)
                if target in targets:
                    updated = module_route(destination) + '#' + targets[target]
                elif embedded and value.startswith('#'):
                    updated = module_route(source) + value
            elif embedded and key != 'id':
                updated = ' '.join(targets.get((source, item), item) for item in value.split())
            quote = match['q'] or '"'
            return f'{match["name"]}={quote}{escape(updated, quote=True)}{quote}' if updated != value else match[0]
        tag = ATTR.sub(replace, tag)
        if embedded and re.fullmatch('h[1-6]', node.tag):
            heading = 'h' + str(min(6, int(node.tag[1]) + 2))
            tag = re.sub(r'^<h[1-6]\b', '<' + heading, tag)
            edits.append((node.end_start, node.end, '</' + heading + '>'))
        if embedded and node.tag == 'details' and 'open' not in node.attrs:
            tag = tag[:-1] + ' open>'
        if tag != document.text[node.start:node.start_end]:
            edits.append((node.start, node.start_end, tag))
    return apply_edits(document.text, edits)


def enrich_sections(site: Path, modules: list[str], selections: dict[str, dict[str, list[str] | None]],
                    companions: dict[str, list[str]] | None = None) -> ImplementationEnrichmentResult:
    result = ImplementationEnrichmentResult()
    site = site.resolve()
    originals = {}
    companions = companions or {}
    for destination in dict.fromkeys(modules):
        cache = {}
        def load(module):
            path = site / module_route(module) / 'index.html'
            if not path.resolve().is_relative_to(site):
                raise ValueError(f'unsafe project page: {path}')
            if not path.is_file():
                raise ValueError(f'missing project implementation page: {module}')
            if module not in cache:
                if module not in originals:
                    originals[module] = path.read_text(encoding='utf-8')
                html = originals[module]
                _, start, end, _ = _code_content_bounds(html, module)
                cache[module] = (path, html, start, end, Document(html[start:end]))
            return cache[module]
        path, html, start, end, facade = load(destination)
        reports = [n for n in facade.nodes if 'data-clrs-implementation-report' in n.attrs]
        if reports:
            node = reports[0]
            result.coverage[destination] = json.loads(facade.text[node.start_end:node.end_start])
            continue
        native = facade.declarations()
        requested = dict(selections.get(destination, {}))
        guides = list(guide_links(facade, destination))
        project_imports = imports(facade, destination)
        if destination not in selections:
            visited, active = set(), set()
            def visit(module):
                if module == destination:
                    return
                if module in active:
                    raise ValueError(f'project import cycle at {module}')
                if module in visited:
                    return
                active.add(module)
                document = load(module)[4]
                if document.declarations():
                    requested[module] = None
                else:
                    for dependency in imports(document, module):
                        visit(dependency)
                active.remove(module)
                visited.add(module)
            for module in [*(project_imports if not native else []), *companions.get(destination, [])]:
                visit(module)
        resolved = []
        for node, (source, fragment) in guides:
            declarations = load(source)[4].declarations()
            name = next((name for name, (anchor, _) in declarations.items() if anchor.attrs['id'] == fragment), None)
            if name is None:
                raise ValueError(f'missing guide declaration target: {source}#{fragment}')
            if source == destination and name in native:
                resolved.append(dict(href=node.attrs['href'], source=source, declaration=name,
                                     target=fragment))
                continue
            if source not in requested:
                requested[source] = [name]
            elif requested[source] is not None and name not in requested[source]:
                requested[source] = [*requested[source], name]
            resolved.append(dict(href=node.attrs['href'], source=source, declaration=name,
                                 target=namespace(destination, source, fragment)))
        if native and not requested:
            result.coverage[destination] = dict(sources={destination: list(native)}, declarations=len(native),
                                                resolved_guide_links=resolved, status='native', companions=[])
            continue
        if not requested and not project_imports and not guides and destination not in selections:
            continue
        fragments, targets = {}, {(destination, anchor.attrs['id']): anchor.attrs['id']
                                  for anchor, _ in native.values()}
        coverage = {destination: list(native)} if native else {}
        for source, names in requested.items():
            document = Document(selected_content(load(source)[4], names, source))
            fragments[source] = document
            coverage[source] = list(document.declarations())
            for node in document.nodes:
                if node.attrs.get('id'):
                    identifier = node.attrs['id']
                    targets[(source, identifier)] = namespace(destination, source, identifier)
        count = sum(map(len, coverage.values()))
        if not count:
            raise ValueError(f'no concrete implementation declarations for facade {destination}')
        report = dict(sources=coverage, declarations=count, resolved_guide_links=resolved, status='enriched',
                      companions=[] if destination in selections else companions.get(destination, []))
        pieces = [f'<section class="clrs-implementation" {MARKER}><h2>Definitions and proofs</h2>']
        for source, document in fragments.items():
            pieces.append('<section class="clrs-implementation-source"><h3>'
                          f'<a class="clrs-implementation-provenance" href="{module_route(source)}">{escape(source)}</a>'
                          '</h3>' + rewrite(document, source, destination, targets, True) + '</section>')
        serialized = json.dumps(report, ensure_ascii=True).replace('<', '\\u003c')
        pieces.append('<script type="application/json" data-clrs-implementation-report="true">' + serialized + '</script></section>')
        insertion = '\n'.join(pieces)
        if len(insertion.encode('utf-8')) > MAX_INSERTED_BYTES:
            raise ValueError(f'implementation insertion exceeds {MAX_INSERTED_BYTES} bytes limit for {destination}')
        updated = html[:start] + rewrite(facade, destination, destination, targets, False) + insertion + html[end:]
        temporary = path.with_name(path.name + '.implementation.tmp')
        temporary.write_text(updated, encoding='utf-8', newline='')
        temporary.replace(path)
        result.sections += 1
        result.sources += len(fragments)
        result.declarations += count - len(native)
        result.resolved_guide_links += len(resolved)
        result.coverage[destination] = report
    return result
