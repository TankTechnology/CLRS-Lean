#!/usr/bin/env python3
"""Reuse a trusted Pages artifact when committed changes do not require Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

WORKFLOW = '.github/workflows/pages.yml'
# Audited 2026-09-14 migrations preserve the compiled input producer and renderer.
# The second adds the no-Lean render refresh and explicit revision metadata.
# Exact raw Git blob pairs only; all other workflow edits require a full build.
AUDITED_WORKFLOW_MIGRATION = (
    '700849ebd7ceebe9220154c4c6f3c7344f797b0002ece6b7decb1cc5dc98466f',
    'e9bebfee64683d5e1fb2a904f03d60238723e484065ebe905ffcde266c0c5bd5',
)
AUDITED_RENDER_WORKFLOW = '60d03b3aa26587b7a54ee9d25e03eb3e242668f07567c54364ecb6f03d3c9802'
AUDITED_WORKFLOW_MIGRATIONS = {
    AUDITED_WORKFLOW_MIGRATION,
    (AUDITED_WORKFLOW_MIGRATION[0], AUDITED_RENDER_WORKFLOW),
    (AUDITED_WORKFLOW_MIGRATION[1], AUDITED_RENDER_WORKFLOW),
}
PRESENTATION = {
    'book_presentation.py', 'prepare_literate_site.py', 'optimize_literate_html.py',
    'reader_layout.py', 'inline_chapter_sections.py', 'literate_navigation.py',
    'reader_implementation.py',
    'prepare_search_assets.py', 'generate_sitemap.py',
}
BENIGN_SCRIPTS = {'check_repository.py', 'check_reader_site.py', 'audit_reader_book.py',
                  'smoke_reader_site.py', 'smoke_reader_book.py', 'site_deploy.py'}
BENIGN_FILES = {'README.md', 'CLAUDE.md', '.gitignore', 'pyproject.toml', 'uv.lock'}
RANK = {'assets': 0, 'presentation': 1, 'render': 2, 'full': 3}
INPUT_REVISION = '.lake/build/compiled-revision.txt'
RENDERER = '.lake/packages/verso/.lake/build/bin/verso-literate-html'
RAW_PROVENANCE = 'raw-provenance.json'


class DeployError(RuntimeError):
    pass


def command(args, root=None):
    result = subprocess.run(args, cwd=root, text=True, capture_output=True)
    if result.returncode:
        raise DeployError(f'{args[0]} failed: {result.stderr.strip() or result.stdout.strip()}')
    return result.stdout


def git(root, *args):
    output = command(['git', *args], root)
    return output if '-z' in args else output.strip()


def asset_path(path):
    p = PurePosixPath(path)
    return path.startswith('docs/literate/assets/') or (
        p.parent == PurePosixPath('docs/literate') and p.suffix in {'.css', '.js'})


def classify_paths(paths):
    mode = 'assets'
    for path in paths:
        p = PurePosixPath(path)
        if p.suffix == '.lean':
            return 'full'
        if asset_path(path):
            continue
        if path == 'literate.toml':
            mode = 'render'
        elif path.startswith('docs/literate/') or (
                p.parent == PurePosixPath('scripts') and p.name in PRESENTATION):
            mode = max((mode, 'presentation'), key=RANK.get)
        elif (path in BENIGN_FILES or path.startswith(('docs/', 'tests/'))
              or (p.parent == PurePosixPath('scripts') and
                  (p.name in BENIGN_SCRIPTS or (p.name.startswith('test_') and p.suffix == '.py')))):
            continue
        else:
            return 'full'
    return mode


def changed_paths(root, baseline):
    return git(root, 'diff', '--name-only', '--no-renames', '-z', baseline, 'HEAD', '--').split('\0')[:-1]


def classify_changes(root, baseline):
    paths = changed_paths(root, baseline)
    if WORKFLOW in paths:
        hashes = []
        for revision in (baseline, 'HEAD'):
            blob = subprocess.run(['git', 'show', f'{revision}:{WORKFLOW}'],
                                  cwd=root, capture_output=True)
            hashes.append(hashlib.sha256(blob.stdout).hexdigest() if blob.returncode == 0 else None)
        if tuple(hashes) in AUDITED_WORKFLOW_MIGRATIONS:
            paths.remove(WORKFLOW)
    return classify_paths(paths)


def validate_run(root, run):
    sha = run.get('head_sha', '')
    repository, head_repository = run.get('repository'), run.get('head_repository')
    if (run.get('event') != 'workflow_dispatch' or not isinstance(repository, dict)
            or not isinstance(head_repository, dict) or not isinstance(repository.get('id'), int)
            or repository['id'] <= 0 or repository['id'] != head_repository.get('id')):
        raise DeployError('Untrusted baseline: expected a dispatch from the same repository')
    if (not isinstance(sha, str) or not re.fullmatch(r'[0-9a-f]{40}', sha)
            or run.get('path') != WORKFLOW or run.get('head_branch') != 'main'
            or run.get('status') != 'completed' or run.get('conclusion') != 'success'
            or not isinstance(run.get('id'), int) or run['id'] <= 0):
        raise DeployError('Untrusted baseline: expected a successful main Pages run and full SHA')
    ancestor = subprocess.run(['git', 'merge-base', '--is-ancestor', sha, 'HEAD'],
                              cwd=root, capture_output=True)
    if ancestor.returncode:
        raise DeployError(f'Baseline {sha} is not a known ancestor of HEAD; fetch full history')
    return sha


class GitHub:
    def __init__(self, root):
        self.root = root
        self.repo = os.environ.get('GITHUB_REPOSITORY') or command(
            ['gh', 'repo', 'view', '--json', 'nameWithOwner', '--jq', '.nameWithOwner'], root).strip()
        if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', self.repo):
            raise DeployError('Invalid GitHub repository name')

    def api(self, path):
        return json.loads(command(['gh', 'api', f'repos/{self.repo}/{path}'], self.root))

    def runs(self):
        records = command(['gh', 'api', '--paginate',
                           f'repos/{self.repo}/actions/workflows/pages.yml/runs'
                           '?branch=main&status=success&event=workflow_dispatch&per_page=100',
                           '--jq', '.workflow_runs[] | tojson'], self.root)
        return [json.loads(line) for line in records.splitlines() if line]

    def run(self, run_id):
        return self.api(f'actions/runs/{run_id}')

    def artifacts(self, run_id):
        names = command(['gh', 'api', '--paginate',
                         f'repos/{self.repo}/actions/runs/{run_id}/artifacts?per_page=100',
                         '--jq', '.artifacts[] | select(.expired == false) | .name'], self.root)
        return set(names.splitlines())

    def caches(self):
        records = command(['gh', 'api', '--paginate',
                           f'repos/{self.repo}/actions/caches?ref=refs/heads/main&per_page=100',
                           '--jq', '.actions_caches[] | tojson'], self.root)
        return [json.loads(line) for line in records.splitlines() if line]

    def download(self, run_id, name, destination):
        destination.mkdir(parents=True, exist_ok=True)
        command(['gh', 'run', 'download', str(run_id), '--repo', self.repo,
                 '--name', name, '--dir', str(destination)], self.root)


def raw_format(artifacts):
    if 'literate-raw' in artifacts:
        return 'raw'
    if {'literate-inputs', *(f'literate-shard-{i}' for i in range(4))} <= artifacts:
        return 'legacy'
    return None


def compiled_cache_keys(caches, sha):
    """Exact main-branch caches produced at a verified source revision only."""
    keys = {record.get('key', '') for record in caches
            if record.get('ref') == 'refs/heads/main' and record.get('size_in_bytes', 0) > 0}
    patterns = {'lake_cache_key': rf'lake-Linux-X64-[0-9a-f]{{64}}-[0-9a-f]{{64}}-{sha}',
                'literate_cache_key': rf'verso-literate-Linux-[0-9a-f]{{64}}-{sha}'}
    found = {field: next((key for key in sorted(keys) if re.fullmatch(pattern, key)), None)
             for field, pattern in patterns.items()}
    return found if all(found.values()) else None


def create_plan(root, requested, github):
    if git(root, 'status', '--porcelain', '--untracked-files=no'):
        raise DeployError('Planning requires a clean tracked checkout')
    head = git(root, 'rev-parse', 'HEAD')
    full = dict(mode='full', reason='Full build explicitly requested', head_sha=head,
                baseline_run_id=None, baseline_sha=None, site_artifact=None)
    if requested == 'full':
        return full
    plan, raw, render, caches = None, None, None, None
    for run in github.runs():
        try:
            sha = validate_run(root, run)
        except DeployError:
            continue
        mode = classify_changes(root, sha)
        if mode == 'full':
            continue
        artifacts = github.artifacts(run['id'])
        if render is None and 'literate-inputs' in artifacts:
            render = dict(mode='render',
                          reason=f'Re-render trusted compiled inputs from main run {run["id"]} without Lean',
                          head_sha=head, inputs_run_id=run['id'], inputs_sha=sha)
        if render is None:
            if caches is None:
                caches = github.caches()
            keys = compiled_cache_keys(caches, sha)
            if keys:
                render = dict(mode='render', inputs_source='cache', **keys,
                              reason=f'Re-render exact compiled caches from main run {run["id"]} without recompiling book proofs',
                              head_sha=head, inputs_run_id=run['id'], inputs_sha=sha)
        if mode == 'render':
            continue
        fmt = raw_format(artifacts)
        if raw is None and fmt:
            raw = dict(raw_run_id=run['id'], raw_sha=sha, raw_format=fmt)
        site = next((name for name in ('reader-site', 'github-pages') if name in artifacts), None)
        if site:
            candidate = dict(mode=mode, reason=f'Reuse verified site from main run {run["id"]}: {mode} changes',
                             head_sha=head, baseline_run_id=run['id'], baseline_sha=sha,
                             site_artifact=site)
            if mode == 'assets' and site == 'reader-site':
                return candidate
            if plan is None or (not raw and mode == 'assets' and plan['mode'] == 'presentation'):
                plan = candidate
        if plan and raw:
            plan.update(raw)
            return plan
    if plan and plan['mode'] == 'assets':
        return plan
    if render:
        return render
    reason = 'No unexpired compatible ancestor artifacts (including compiled inputs); full Lean build required'
    if requested == 'refresh':
        raise DeployError(reason)
    full['reason'] = reason
    return full


def safe_extract(archive, destination):
    """Extract regular files/directories only; never follow archive links."""
    destination.mkdir(parents=True, exist_ok=True)
    root = destination.resolve()
    with tarfile.open(archive, 'r:*') as tar:
        members = tar.getmembers()
        for member in members:
            path = PurePosixPath(member.name)
            target = destination / member.name
            if (path.is_absolute() or '..' in path.parts or '\\' in member.name
                    or not (member.isfile() or member.isdir())
                    or not target.resolve().is_relative_to(root)):
                raise DeployError(f'Unsafe archive member: {member.name}')
        for member in members:
            target = destination / member.name
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with tar.extractfile(member) as source, target.open('wb') as output:
                    shutil.copyfileobj(source, output)


def owned_assets(root, revision):
    paths = git(root, 'ls-tree', '-r', '--name-only', '-z', revision, '--', 'docs/literate')
    return {p for p in paths.split('\0') if p and asset_path(p)}


def sync_assets(root, baseline, site):
    before, after = owned_assets(root, baseline), owned_assets(root, 'HEAD')
    for path in sorted(before - after):
        target = site / PurePosixPath(path).relative_to('docs/literate')
        if target.is_file():
            target.unlink()
    for path in sorted(after):
        source = root / path
        if source.is_symlink() or not source.is_file():
            raise DeployError(f'Asset must be a regular tracked file: {path}')
        target = site / PurePosixPath(path).relative_to('docs/literate')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)


def validate_output(root, output):
    root, output = root.resolve(), output.resolve()
    if root.is_relative_to(output):
        raise DeployError('Output must not contain the repository')
    protected = [root / '.git', root / '.lake']
    packages = root / '.lake/packages'
    if packages.is_dir():
        protected.extend(packages.iterdir())
    for option in ('--git-dir', '--git-common-dir'):
        protected.append((root / git(root, 'rev-parse', option)).resolve())
    for path in protected:
        path = path.resolve()
        if output.is_relative_to(path) or path.is_relative_to(output):
            raise DeployError(f'Output overlaps Git metadata or Lean dependencies: {output}')
    for path in git(root, 'ls-files', '-z').split('\0'):
        if path and (root / path).resolve().is_relative_to(output):
            raise DeployError(f'Output overlaps tracked repository files: {output}')


def validate_plan_run(root, plan, prefix, github):
    run_id, sha = plan.get(f'{prefix}_run_id'), plan.get(f'{prefix}_sha')
    if not isinstance(run_id, int) or run_id <= 0:
        raise DeployError('Invalid artifact run ID in plan')
    run = github.run(run_id)
    if run.get('id') != run_id or validate_run(root, run) != sha:
        raise DeployError('Artifact run provenance differs from plan')
    mode = classify_changes(root, sha)
    limit = 'render' if prefix == 'inputs' else plan['mode'] if prefix == 'baseline' else 'presentation'
    if RANK[mode] > RANK[limit]:
        raise DeployError('Current changes require a full build or a new presentation plan')
    return github.artifacts(run_id)


def restore_raw(root, plan, github, temp):
    artifacts = validate_plan_run(root, plan, 'raw', github)
    fmt = plan.get('raw_format')
    if fmt not in {'raw', 'legacy'} or raw_format(artifacts) != fmt:
        raise DeployError('Raw artifact missing, expired, or different from plan')
    run_id = plan['raw_run_id']
    raw = temp / 'raw'
    if fmt == 'raw':
        download = temp / 'raw-download'
        github.download(run_id, 'literate-raw', download)
        safe_extract(download / 'raw.tar.gz', raw)
    else:
        download = temp / 'inputs-download'
        github.download(run_id, 'literate-inputs', download)
        tar_path = temp / 'inputs.tar'
        command(['zstd', '-d', '-f', str(download / 'literate-inputs.tar.zst'), '-o', str(tar_path)])
        inputs = temp / 'inputs'
        safe_extract(tar_path, inputs)
        shards = temp / 'shards'
        for i in range(4):
            github.download(run_id, f'literate-shard-{i}', shards)
        command([sys.executable, str(root / 'scripts/merge_literate_shards.py'),
                 str(inputs / '.lake/build/literate-shards/manifest.json'), str(raw),
                 *(str(shards / f'shard-{i}') for i in range(4))], root)
    return raw


def checked_revision(root, value, maximum, description):
    if not isinstance(value, str) or not re.fullmatch(r'[0-9a-f]{40}', value):
        raise DeployError(f'Invalid {description} revision')
    if subprocess.run(['git', 'merge-base', '--is-ancestor', value, 'HEAD'],
                      cwd=root, capture_output=True).returncode:
        raise DeployError(f'{description} revision is not a known ancestor')
    if RANK[classify_changes(root, value)] > RANK[maximum]:
        raise DeployError(f'{description} revision requires a new build')
    return value


def raw_provenance(root, raw, fallback):
    path = raw / RAW_PROVENANCE
    record = json.loads(path.read_text()) if path.is_file() else {
        'raw_sha': fallback, 'compiled_sha': fallback}
    return dict(raw_sha=checked_revision(root, record['raw_sha'], 'presentation', 'raw'),
                compiled_sha=checked_revision(root, record['compiled_sha'], 'render', 'compiled'))


def restore_inputs(root, plan, github, temp):
    """Restore only a validated ancestor artifact into an isolated directory."""
    artifacts = validate_plan_run(root, plan, 'inputs', github)
    if plan.get('inputs_source') == 'cache':
        keys = compiled_cache_keys(github.caches(), plan['inputs_sha'])
        if keys is None or any(plan.get(key) != value for key, value in keys.items()):
            raise DeployError('Exact compiled caches expired or differ from the plan')
        for key, env in [('lake_cache_key', 'CLRS_RESTORED_LAKE_CACHE'),
                         ('literate_cache_key', 'CLRS_RESTORED_JSON_CACHE')]:
            if os.environ.get(env) != plan[key]:
                raise DeployError('Compiled cache refresh requires exact CI cache restoration')
        inputs = temp / 'inputs'
        for relative in ('.lake/build/literate', RENDERER):
            source, destination = root / relative, inputs / relative
            if source.is_symlink() or not source.exists():
                raise DeployError(f'Compiled cache lacks a regular input: {relative}')
            destination.parent.mkdir(parents=True, exist_ok=True)
            if source.is_dir():
                shutil.copytree(source, destination)
            else:
                shutil.copy2(source, destination)
        compiled = checked_revision(root, plan['inputs_sha'], 'render', 'compiled')
        (inputs / INPUT_REVISION).write_text(compiled + '\n')
        (inputs / RENDERER).chmod(0o755)
        return inputs, compiled
    if 'literate-inputs' not in artifacts:
        raise DeployError('Compiled inputs missing or expired; refresh cannot compile Lean')
    download, inputs = temp / 'inputs-download', temp / 'inputs'
    github.download(plan['inputs_run_id'], 'literate-inputs', download)
    archive = download / 'literate-inputs.tar.zst'
    tar_path = temp / 'inputs.tar'
    command(['zstd', '-d', '-f', str(archive), '-o', str(tar_path)])
    safe_extract(tar_path, inputs)
    revision = inputs / INPUT_REVISION
    compiled = checked_revision(root, revision.read_text().strip() if revision.is_file()
                                else plan['inputs_sha'], 'render', 'compiled')
    executable = inputs / RENDERER
    if not executable.is_file() or not (inputs / '.lake/build/literate').is_dir():
        raise DeployError('Compiled artifact lacks renderer or literate JSON inputs')
    executable.chmod(0o755)
    revision.write_text(compiled + "\n")
    return inputs, compiled


def plan_inputs(root, inputs, portable=False):
    module_map, shard_plan = inputs / '.lake/build/literate-module-map', inputs / '.lake/build/literate-shards'
    command([sys.executable, str(root / 'scripts/prepare_literate_module_map.py'),
             str(inputs / '.lake/build/literate'), str(module_map)], root)
    if portable:
        rows = []
        for line in module_map.read_text().splitlines():
            module, json_path, source = line.split('\t')
            relative = Path(json_path).relative_to(inputs).as_posix()
            rows.append(f'{module}\t{relative}\t{source}\n')
        module_map.write_text(''.join(rows))
    command([sys.executable, str(root / 'scripts/plan_literate_shards.py'),
             str(module_map), str(shard_plan), '--shards', '4',
             *[arg for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'literate.toml')
               for arg in ('--digest-input', str(root / name))]], inputs if portable else root)
    return module_map, shard_plan


def prepare_inputs(root, plan, output, github):
    """Package portable, freshly planned inputs for independent CI shard runners."""
    if git(root, 'status', '--porcelain', '--untracked-files=no'):
        raise DeployError('Input preparation requires a clean tracked checkout')
    if plan.get('mode') != 'render' or plan.get('head_sha') != git(root, 'rev-parse', 'HEAD'):
        raise DeployError('Input preparation requires a current render plan')
    validate_output(root, output)
    with tempfile.TemporaryDirectory(prefix='render-inputs-') as directory:
        inputs, compiled = restore_inputs(root, plan, github, Path(directory))
        plan_inputs(root, inputs, portable=True)
        output.parent.mkdir(parents=True, exist_ok=True)
        command(['tar', '--zstd', '-cf', str(output), '-C', str(inputs),
                 '.lake/build/literate', INPUT_REVISION, RENDERER,
                 '.lake/build/literate-module-map', '.lake/build/literate-shards'])
    print(f'Prepared four shards from compiled revision {compiled} without Lean')


def render_inputs(root, plan, github, temp, inputs_output=None):
    """Sequential local fallback; CI runs these shards on four separate runners."""
    inputs, compiled = restore_inputs(root, plan, github, temp)
    module_map, shard_plan = plan_inputs(root, inputs)
    executable = inputs / RENDERER
    shards = [temp / f'shard-{i}' for i in range(4)]
    for i, shard in enumerate(shards):
        print(f'Rendering shard {i + 1}/4 from compiled revision {compiled}', flush=True)
        command([sys.executable, str(root / 'scripts/render_literate_shard.py'),
                 '--executable', str(executable), '--module-map', str(module_map),
                 '--config', str(root / 'literate.toml'),
                 '--manifest', str(shard_plan / 'manifest.json'),
                 '--shard-index', str(i), '--output', str(shard)], root)
    raw = temp / 'raw'
    command([sys.executable, str(root / 'scripts/merge_literate_shards.py'),
             str(shard_plan / 'manifest.json'), str(raw), *map(str, shards)], root)
    for script in ('check_literate_html_weight.py', 'check_literate_html_freshness.py'):
        command([sys.executable, str(root / 'scripts' / script), str(raw)], root)
    record = dict(raw_sha=plan['head_sha'], compiled_sha=compiled)
    (raw / RAW_PROVENANCE).write_text(json.dumps(record) + '\n')
    if inputs_output:
        # Carry the original compile revision forward, even after multiple renders.
        inputs_output.parent.mkdir(parents=True, exist_ok=True)
        command(['tar', '--zstd', '-cf', str(inputs_output), '-C', str(inputs),
                 '.lake/build/literate', INPUT_REVISION, RENDERER])
    return raw, record


def publish_site(source, site):
    """Complete the copy before replacing a preview, with rollback on rename failure."""
    site.parent.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix=f'.{site.name}-', dir=site.parent))
    new, backup = directory / 'new', directory / 'previous'
    installed = False
    try:
        shutil.copytree(source, new)
        had_previous = site.exists()
        if had_previous:
            os.replace(site, backup)
        try:
            os.replace(new, site)
            installed = True
        except OSError:
            if had_previous:
                try:
                    os.replace(backup, site)
                except OSError as error:
                    raise DeployError(f'Replacement and rollback failed; previous site saved at {backup}') from error
            raise
    finally:
        if installed or not backup.exists():
            shutil.rmtree(directory)


def refresh(root, plan, site, github, raw_output=None, inputs_output=None):
    if git(root, 'status', '--porcelain', '--untracked-files=no'):
        raise DeployError('Refresh requires a clean tracked checkout')
    if plan.get('mode') not in {'assets', 'presentation', 'render'}:
        raise DeployError('Refresh requires an assets, presentation, or render plan')
    if plan.get('head_sha') != git(root, 'rev-parse', 'HEAD'):
        raise DeployError('HEAD changed since planning; create a fresh plan')
    validate_output(root, site)
    if raw_output:
        validate_output(root, raw_output)
        if raw_output.resolve().is_relative_to(site.resolve()) or site.resolve().is_relative_to(raw_output.resolve()):
            raise DeployError('Raw output and site must not overlap')
    if inputs_output:
        validate_output(root, inputs_output)
        for other in (site, raw_output):
            if other and (inputs_output.resolve().is_relative_to(other.resolve())
                          or other.resolve().is_relative_to(inputs_output.resolve())):
                raise DeployError('Compiled inputs output must not overlap other outputs')
    with tempfile.TemporaryDirectory(prefix='site-refresh-') as directory:
        temp = Path(directory)
        download, staged = temp / 'site-download', temp / 'site'
        raw = None
        if plan['mode'] == 'render':
            raw, record = render_inputs(root, plan, github, temp, inputs_output)
        else:
            artifacts = validate_plan_run(root, plan, 'baseline', github)
            name = plan.get('site_artifact')
            if name not in {'reader-site', 'github-pages'} or name not in artifacts:
                raise DeployError('Site artifact missing or expired')
            github.download(plan['baseline_run_id'], name, download)
            safe_extract(download / ('site.tar.gz' if name == 'reader-site' else 'artifact.tar'), staged)
            revision = staged / 'revision.txt'
            if not revision.is_file() or revision.read_text().strip() != plan['baseline_sha']:
                raise DeployError('Site artifact revision does not match trusted baseline SHA')
            content_revision = staged / 'content-revision.txt'
            content = content_revision.read_text().strip() if content_revision.is_file() else plan['baseline_sha']
            compiled_revision = staged / 'compiled-revision.txt'
            compiled = compiled_revision.read_text().strip() if compiled_revision.is_file() else content
            record = dict(raw_sha=checked_revision(root, content, 'presentation', 'content'),
                          compiled_sha=checked_revision(root, compiled, 'render', 'compiled'))
            if plan['mode'] == 'presentation' or (raw_output and name == 'github-pages' and plan.get('raw_run_id')):
                raw = restore_raw(root, plan, github, temp)
                raw_record = raw_provenance(root, raw, plan['raw_sha'])
                if plan['mode'] == 'presentation':
                    record = raw_record
                (raw / RAW_PROVENANCE).write_text(json.dumps(raw_record) + '\n')
        if plan['mode'] in {'presentation', 'render'}:
            command([sys.executable, str(root / 'scripts/prepare_literate_site.py'), str(raw), str(staged)], root)
        else:
            sync_assets(root, plan['baseline_sha'], staged)
        if plan['mode'] == 'render':
            command([sys.executable, str(root / 'scripts/audit_reader_book.py'),
                     '--site', str(staged), '--compiled', str(temp / 'inputs/.lake/build/literate')], root)
        (staged / 'content-revision.txt').write_text(record['raw_sha'] + '\n')
        (staged / 'compiled-revision.txt').write_text(record['compiled_sha'] + '\n')
        (staged / 'revision.txt').write_text(plan['head_sha'] + '\n')
        if raw_output and raw:
            raw_output.parent.mkdir(parents=True, exist_ok=True)
            with tarfile.open(raw_output, 'w:gz') as tar:
                for path in sorted(raw.iterdir()):
                    tar.add(path, arcname=path.name)
        publish_site(staged, site)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    plan_parser = commands.add_parser('plan')
    plan_parser.add_argument('--mode', choices=['auto', 'refresh', 'full'], default='auto')
    plan_parser.add_argument('--output', type=Path, required=True)
    plan_parser.add_argument('--github-output', type=Path)
    inputs_parser = commands.add_parser('prepare-inputs')
    inputs_parser.add_argument('--plan', type=Path, required=True)
    inputs_parser.add_argument('--output', type=Path, required=True)
    refresh_parser = commands.add_parser('refresh')
    refresh_parser.add_argument('--plan', type=Path, required=True)
    refresh_parser.add_argument('--site', type=Path, required=True)
    refresh_parser.add_argument('--raw-output', type=Path)
    refresh_parser.add_argument('--inputs-output', type=Path)
    for subparser in (plan_parser, refresh_parser, inputs_parser):
        subparser.add_argument('--repo-root', type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.repo_root.resolve()
    try:
        github = None if args.command == 'plan' and args.mode == 'full' else GitHub(root)
        if args.command == 'plan':
            plan = create_plan(root, args.mode, github)
            args.output.write_text(json.dumps(plan, indent=2) + '\n')
            if args.github_output:
                with args.github_output.open('a') as output:
                    output.write(f'mode={plan["mode"]}\nreason={plan["reason"]}\n')
                    for key in ('inputs_source', 'lake_cache_key', 'literate_cache_key'):
                        output.write(f'{key}={plan.get(key, "")}\n')
            print(plan['reason'])
        elif args.command == 'prepare-inputs':
            prepare_inputs(root, json.loads(args.plan.read_text()), args.output.resolve(), github)
        else:
            refresh(root, json.loads(args.plan.read_text()), args.site.resolve(), github,
                    args.raw_output.resolve() if args.raw_output else None,
                    args.inputs_output.resolve() if args.inputs_output else None)
            print(f'Refreshed site: {args.site}')
    except (DeployError, OSError, ValueError, KeyError, tarfile.TarError) as error:
        print(f'site_deploy: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
