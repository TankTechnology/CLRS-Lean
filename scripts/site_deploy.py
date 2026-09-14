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
# Audited 2026-09-14 migration: preserves full-build commands and introduces
# routing/retention only. Exact raw Git blob hashes; future workflow edits rebuild.
AUDITED_WORKFLOW_MIGRATION = (
    '700849ebd7ceebe9220154c4c6f3c7344f797b0002ece6b7decb1cc5dc98466f',
    'e9bebfee64683d5e1fb2a904f03d60238723e484065ebe905ffcde266c0c5bd5',
)
PRESENTATION = {
    'book_presentation.py', 'prepare_literate_site.py', 'optimize_literate_html.py',
    'reader_layout.py', 'inline_chapter_sections.py', 'literate_navigation.py',
    'prepare_search_assets.py', 'generate_sitemap.py',
}
BENIGN_SCRIPTS = {'check_repository.py', 'check_reader_site.py',
                  'smoke_reader_site.py', 'site_deploy.py'}
BENIGN_FILES = {'README.md', 'CLAUDE.md', '.gitignore', 'pyproject.toml', 'uv.lock'}
RANK = {'assets': 0, 'presentation': 1, 'full': 2}


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
        if path.startswith('docs/literate/') or (
                p.parent == PurePosixPath('scripts') and p.name in PRESENTATION):
            mode = 'presentation'
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
        if tuple(hashes) == AUDITED_WORKFLOW_MIGRATION:
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


def create_plan(root, requested, github):
    if git(root, 'status', '--porcelain', '--untracked-files=no'):
        raise DeployError('Planning requires a clean tracked checkout')
    head = git(root, 'rev-parse', 'HEAD')
    full = dict(mode='full', reason='Full build explicitly requested', head_sha=head,
                baseline_run_id=None, baseline_sha=None, site_artifact=None)
    if requested == 'full':
        return full
    plan, raw = None, None
    for run in github.runs():
        try:
            sha = validate_run(root, run)
        except DeployError:
            continue
        mode = classify_changes(root, sha)
        if mode == 'full':
            continue
        artifacts = github.artifacts(run['id'])
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
    reason = 'No unexpired compatible ancestor artifacts; full Lean build required'
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
    if mode == 'full' or (prefix == 'baseline' and RANK[mode] > RANK[plan['mode']]):
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


def refresh(root, plan, site, github, raw_output=None):
    if git(root, 'status', '--porcelain', '--untracked-files=no'):
        raise DeployError('Refresh requires a clean tracked checkout')
    if plan.get('mode') not in {'assets', 'presentation'}:
        raise DeployError('Refresh requires an assets or presentation plan')
    if plan.get('head_sha') != git(root, 'rev-parse', 'HEAD'):
        raise DeployError('HEAD changed since planning; create a fresh plan')
    validate_output(root, site)
    if raw_output:
        validate_output(root, raw_output)
        if raw_output.resolve().is_relative_to(site.resolve()) or site.resolve().is_relative_to(raw_output.resolve()):
            raise DeployError('Raw output and site must not overlap')
    artifacts = validate_plan_run(root, plan, 'baseline', github)
    name = plan.get('site_artifact')
    if name not in {'reader-site', 'github-pages'} or name not in artifacts:
        raise DeployError('Site artifact missing or expired')
    with tempfile.TemporaryDirectory(prefix='site-refresh-') as directory:
        temp = Path(directory)
        download, staged = temp / 'site-download', temp / 'site'
        github.download(plan['baseline_run_id'], name, download)
        safe_extract(download / ('site.tar.gz' if name == 'reader-site' else 'artifact.tar'), staged)
        revision = staged / 'revision.txt'
        if not revision.is_file() or revision.read_text().strip() != plan['baseline_sha']:
            raise DeployError('Site artifact revision does not match trusted baseline SHA')
        content_revision = staged / 'content-revision.txt'
        provenance = content_revision.read_text().strip() if content_revision.is_file() else plan['baseline_sha']
        if not re.fullmatch(r'[0-9a-f]{40}', provenance):
            raise DeployError('Invalid content revision in site artifact')
        raw = None
        if plan['mode'] == 'presentation' or (raw_output and name == 'github-pages' and plan.get('raw_run_id')):
            raw = restore_raw(root, plan, github, temp)
        if plan['mode'] == 'presentation':
            command([sys.executable, str(root / 'scripts/prepare_literate_site.py'), str(raw), str(staged)], root)
            provenance = plan['raw_sha']
        else:
            sync_assets(root, plan['baseline_sha'], staged)
        (staged / 'content-revision.txt').write_text(provenance + '\n')
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
    refresh_parser = commands.add_parser('refresh')
    refresh_parser.add_argument('--plan', type=Path, required=True)
    refresh_parser.add_argument('--site', type=Path, required=True)
    refresh_parser.add_argument('--raw-output', type=Path)
    for subparser in (plan_parser, refresh_parser):
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
            print(plan['reason'])
        else:
            refresh(root, json.loads(args.plan.read_text()), args.site.resolve(), github,
                    args.raw_output.resolve() if args.raw_output else None)
            print(f'Refreshed site: {args.site}')
    except (DeployError, OSError, ValueError, KeyError, tarfile.TarError) as error:
        print(f'site_deploy: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
