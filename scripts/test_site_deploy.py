"""Safety checks for refreshing an already verified reader site."""
import hashlib
import io
import subprocess
import tarfile
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

import site_deploy as deploy


class DeployTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'repo'
        self.root.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.email', 'test@example.org')
        self.git('config', 'user.name', 'Test')
        self.write('src/Proof.lean', 'theorem preserved := True\n')
        self.write('docs/literate/reader.css', 'old css')
        self.write('docs/literate/assets/old.svg', 'old image')
        self.base = self.commit()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), *args], text=True).strip()

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def commit(self):
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')
        return self.git('rev-parse', 'HEAD')

    def run_record(self, sha=None, **kwargs):
        return dict(id=12, head_sha=sha or self.base, head_branch='main',
                    path='.github/workflows/pages.yml', status='completed',
                    conclusion='success', event='workflow_dispatch',
                    repository={'id': 7}, head_repository={'id': 7}, **kwargs)

    def client(self, artifacts=('reader-site',)):
        gh = Mock()
        gh.runs.return_value = [self.run_record()]
        gh.run.return_value = self.run_record()
        gh.artifacts.return_value = set(artifacts)
        return gh

    def test_diff_keeps_both_sides_of_rename_and_deletion(self):
        self.git('mv', 'src/Proof.lean', 'docs/proof.txt')
        (self.root / 'docs/literate/assets/old.svg').unlink()
        self.commit()
        paths = deploy.changed_paths(self.root, self.base)
        self.assertIn('src/Proof.lean', paths)
        self.assertIn('docs/proof.txt', paths)
        self.assertIn('docs/literate/assets/old.svg', paths)
        self.assertEqual(deploy.classify_paths(paths), 'full')

    def test_git_paths_preserve_leading_whitespace(self):
        self.write(' README.md', 'unknown file with misleading name')
        self.commit()
        paths = deploy.changed_paths(self.root, self.base)
        self.assertEqual(paths, [' README.md'])
        self.assertEqual(deploy.classify_paths(paths), 'full')

    def test_classification_is_conservative(self):
        for paths, expected in [([], 'assets'),
                (['docs/literate/assets/new.webp', 'docs/literate/reader.css'], 'assets'),
                (['README.md', 'docs/guide.md', 'scripts/test_anything.py'], 'assets'),
                (['scripts/book_presentation.py'], 'presentation'),
                (['scripts/reader_implementation.py', 'docs/literate/reader-implementations.json'], 'presentation'),
                (['docs/literate/contents.json'], 'presentation'),
                (['tests/Proof.lean'], 'full'), (['docs/Foo.lean'], 'full'),
                (['scripts/unknown.py'], 'full'), (['lake-manifest.json'], 'full'),
                (['literate.toml'], 'full'), (['unknown'], 'full')]:
            with self.subTest(paths=paths):
                self.assertEqual(deploy.classify_paths(paths), expected)

    def test_workflow_changes_require_full_build(self):
        for path in ['.github/workflows/pages.yml', '.github/workflows/other.yml']:
            with self.subTest(path=path):
                self.assertEqual(deploy.classify_paths([path]), 'full')
        self.write('.github/workflows/pages.yml', 'run: renderer --base-url https://old.example/\n')
        self.base = self.commit()
        self.write('.github/workflows/pages.yml', 'run: renderer --base-url https://new.example/\n')
        self.commit()
        gh = self.client()
        self.assertEqual(deploy.create_plan(self.root, 'auto', gh)['mode'], 'full')
        with self.assertRaises(deploy.DeployError):
            deploy.create_plan(self.root, 'refresh', gh)

    def test_only_exact_audited_workflow_migration_allows_reuse(self):
        before, after = b' old workflow\n\n', b' reviewed workflow\n\n'
        path = self.write('.github/workflows/pages.yml', before.decode())
        self.base = self.commit()
        path.write_bytes(after)
        self.commit()
        pair = (hashlib.sha256(before).hexdigest(), hashlib.sha256(after).hexdigest())
        with patch.object(deploy, 'AUDITED_WORKFLOW_MIGRATION', pair):
            gh = self.client()
            plan = deploy.create_plan(self.root, 'refresh', gh)
            self.assertEqual(plan['mode'], 'assets')
            deploy.validate_plan_run(self.root, plan, 'baseline', gh)
            # Removing exactly one newline must invalidate the exception.
            path.write_bytes(after[:-1])
            self.commit()
            self.assertEqual(deploy.create_plan(self.root, 'auto', gh)['mode'], 'full')
            with self.assertRaises(deploy.DeployError):
                deploy.validate_plan_run(self.root, plan, 'baseline', gh)

    def test_audited_migration_does_not_exempt_other_workflows(self):
        before, after = b'old workflow\n', b'reviewed workflow\n'
        self.write('.github/workflows/pages.yml', before.decode())
        self.base = self.commit()
        self.write('.github/workflows/pages.yml', after.decode())
        self.write('.github/workflows/other.yml', 'run: changed renderer\n')
        self.commit()
        pair = (hashlib.sha256(before).hexdigest(), hashlib.sha256(after).hexdigest())
        with patch.object(deploy, 'AUDITED_WORKFLOW_MIGRATION', pair):
            self.assertEqual(deploy.create_plan(self.root, 'auto', self.client())['mode'], 'full')

    def test_planner_never_reuses_site_after_lean_change(self):
        self.write('src/Proof.lean', 'changed proof')
        self.commit()
        gh = self.client()
        self.assertEqual(deploy.create_plan(self.root, 'auto', gh)['mode'], 'full')
        with self.assertRaisesRegex(deploy.DeployError, 'full|Lean|compatible'):
            deploy.create_plan(self.root, 'refresh', gh)

    def test_presentation_requires_compatible_raw_ancestor(self):
        self.write('scripts/book_presentation.py', '# changed')
        self.commit()
        gh = self.client(('reader-site', 'literate-raw'))
        plan = deploy.create_plan(self.root, 'auto', gh)
        self.assertEqual(plan['mode'], 'presentation')
        self.assertEqual(plan['raw_run_id'], 12)
        self.assertEqual(plan['raw_format'], 'raw')
        gh.artifacts.return_value = {'reader-site'}
        self.assertEqual(deploy.create_plan(self.root, 'auto', gh)['mode'], 'full')

    def test_legacy_artifacts_are_supported(self):
        self.write('scripts/book_presentation.py', '# changed')
        self.commit()
        names = ['github-pages', 'literate-inputs'] + [f'literate-shard-{n}' for n in range(4)]
        plan = deploy.create_plan(self.root, 'refresh', self.client(names))
        self.assertEqual(plan['site_artifact'], 'github-pages')
        self.assertEqual(plan['raw_format'], 'legacy')

    def test_bad_run_provenance_is_rejected(self):
        for key, value in [('head_sha', '--help'), ('head_sha', 'a' * 40),
                           ('head_branch', 'feature'), ('path', 'other.yml'),
                           ('conclusion', 'failure'), ('status', 'in_progress'),
                           ('event', 'pull_request'), ('head_repository', {'id': 8}),
                           ('head_repository', None), ('repository', {})]:
            record = self.run_record()
            record[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(deploy.DeployError):
                deploy.validate_run(self.root, record)

    def test_network_error_does_not_trigger_expensive_full_build(self):
        gh = self.client()
        gh.runs.side_effect = deploy.DeployError('GitHub API unavailable')
        with self.assertRaisesRegex(deploy.DeployError, 'unavailable'):
            deploy.create_plan(self.root, 'auto', gh)

    def test_asset_sync_removes_deleted_owned_files_and_preserves_proof(self):
        site = Path(self.temp.name) / 'site'
        (site / 'assets').mkdir(parents=True)
        (site / 'assets/old.svg').write_text('old image')
        (site / 'assets/renderer.svg').write_text('generated image')
        proof = site / 'proof.html'
        proof.write_bytes(b'<html>verified proof\x00</html>')
        original = proof.read_bytes()
        (self.root / 'docs/literate/assets/old.svg').unlink()
        self.write('docs/literate/assets/new.svg', 'new image')
        self.write('docs/literate/reader.css', 'new css')
        self.commit()
        deploy.sync_assets(self.root, self.base, site)
        self.assertFalse((site / 'assets/old.svg').exists())
        self.assertEqual((site / 'assets/new.svg').read_text(), 'new image')
        self.assertEqual((site / 'reader.css').read_text(), 'new css')
        self.assertTrue((site / 'assets/renderer.svg').exists())
        self.assertEqual(proof.read_bytes(), original)

    def test_tar_rejects_traversal_and_links(self):
        for name, kind in [('../escape', tarfile.REGTYPE), ('/escape', tarfile.REGTYPE),
                           ('link', tarfile.SYMTYPE), ('hard', tarfile.LNKTYPE)]:
            with self.subTest(name=name):
                archive = Path(self.temp.name) / 'bad.tar'
                with tarfile.open(archive, 'w') as tar:
                    member = tarfile.TarInfo(name)
                    member.type = kind
                    member.linkname = '/tmp/escape'
                    tar.addfile(member)
                with self.assertRaises(deploy.DeployError):
                    deploy.safe_extract(archive, Path(self.temp.name) / 'out')

    def test_safe_tar_extracts_regular_files(self):
        archive = Path(self.temp.name) / 'good.tar'
        with tarfile.open(archive, 'w') as tar:
            info = tarfile.TarInfo('./chapter/index.html')
            info.size = 5
            tar.addfile(info, io.BytesIO(b'proof'))
        destination = Path(self.temp.name) / 'out'
        deploy.safe_extract(archive, destination)
        self.assertEqual((destination / 'chapter/index.html').read_bytes(), b'proof')

    def test_plan_requires_clean_tracked_checkout(self):
        self.write('src/Proof.lean', 'uncommitted proof')
        with self.assertRaisesRegex(deploy.DeployError, 'clean|dirty'):
            deploy.create_plan(self.root, 'auto', self.client())

    def test_refresh_asset_success_and_legacy_raw_bootstrap(self):
        self.write('docs/literate/reader.css', 'updated css')
        head = self.commit()
        gh = self.client(('github-pages', 'literate-raw'))
        plan = deploy.create_plan(self.root, 'refresh', gh)
        proof = b'<html>original verified proof</html>'
        def download(run_id, name, destination):
            destination.mkdir(parents=True, exist_ok=True)
            filename = 'raw.tar.gz' if name == 'literate-raw' else 'artifact.tar'
            contents = {'raw.html': b'raw proof'} if name == 'literate-raw' else {
                'revision.txt': self.base.encode(), 'proof.html': proof,
                'reader.css': b'old css'}
            with tarfile.open(destination / filename, 'w:gz') as tar:
                for path, data in contents.items():
                    info = tarfile.TarInfo(path)
                    info.size = len(data)
                    tar.addfile(info, io.BytesIO(data))
        gh.download.side_effect = download
        site = Path(self.temp.name) / 'out'
        raw = Path(self.temp.name) / 'raw.tar.gz'
        deploy.refresh(self.root, plan, site, gh, raw)
        self.assertEqual((site / 'proof.html').read_bytes(), proof)
        self.assertEqual((site / 'reader.css').read_text(), 'updated css')
        self.assertEqual((site / 'revision.txt').read_text().strip(), head)
        self.assertEqual((site / 'content-revision.txt').read_text().strip(), self.base)
        with tarfile.open(raw) as tar:
            self.assertEqual(tar.extractfile('raw.html').read(), b'raw proof')

    def test_output_cannot_replace_repository_or_tracked_directories(self):
        for output in [self.root, self.root.parent, self.root / 'docs',
                       self.root / 'src/Proof.lean', self.root / '.git',
                       self.root / '.git/objects', self.root / '.lake',
                       self.root / '.lake/packages/verso']:
            with self.subTest(output=output), self.assertRaises(deploy.DeployError):
                deploy.validate_output(self.root, output)

    def test_output_rejects_worktree_common_git_directory(self):
        worktree = Path(self.temp.name) / 'worktree'
        self.git('worktree', 'add', '--detach', str(worktree), 'HEAD')
        common = self.root / '.git'
        gitdir = Path(subprocess.check_output(
            ['git', '-C', str(worktree), 'rev-parse', '--git-dir'], text=True).strip())
        for output in [common, gitdir, gitdir / 'objects']:
            with self.subTest(output=output), self.assertRaises(deploy.DeployError):
                deploy.validate_output(worktree, output)

    def test_output_rejects_symlinked_lean_dependency(self):
        dependency = Path(self.temp.name) / 'external-dependency'
        dependency.mkdir()
        packages = self.root / '.lake/packages'
        packages.mkdir(parents=True)
        (packages / 'verso').symlink_to(dependency, target_is_directory=True)
        with self.assertRaises(deploy.DeployError):
            deploy.validate_output(self.root, packages / 'verso')

    def test_runs_api_paginates(self):
        import json
        client = deploy.GitHub.__new__(deploy.GitHub)
        client.root, client.repo = self.root, 'owner/repo'
        records = [self.run_record() for _ in range(101)]
        with patch.object(deploy, 'command', return_value='\n'.join(map(json.dumps, records))) as call:
            self.assertEqual(len(client.runs()), 101)
        self.assertIn('--paginate', call.call_args.args[0])
        self.assertTrue(any('per_page=100' in arg for arg in call.call_args.args[0]))

    def test_asset_planning_stops_after_first_usable_site(self):
        gh = self.client()
        gh.runs.return_value = [self.run_record() for _ in range(40)]
        self.assertEqual(deploy.create_plan(self.root, 'auto', gh)['mode'], 'assets')
        gh.artifacts.assert_called_once_with(12)

    def test_presentation_finds_raw_after_more_than_thirty_runs(self):
        self.write('scripts/book_presentation.py', '# changed')
        self.commit()
        gh = self.client()
        records = []
        for run_id in range(50, 0, -1):
            record = self.run_record()
            record['id'] = run_id
            records.append(record)
        gh.runs.return_value = records
        gh.artifacts.side_effect = lambda run_id: {'reader-site', 'literate-raw'} if run_id == 1 else {'reader-site'}
        plan = deploy.create_plan(self.root, 'refresh', gh)
        self.assertEqual(plan['baseline_run_id'], 50)
        self.assertEqual(plan['raw_run_id'], 1)

    def test_publish_copy_failure_preserves_existing_site(self):
        source, site = Path(self.temp.name) / 'source', Path(self.temp.name) / 'out'
        source.mkdir()
        site.mkdir()
        (site / 'index.html').write_text('previous preview')
        with patch.object(deploy.shutil, 'copytree', side_effect=OSError('disk full')):
            with self.assertRaises(OSError):
                deploy.publish_site(source, site)
        self.assertEqual((site / 'index.html').read_text(), 'previous preview')

    def test_publish_replace_failure_rolls_back_existing_site(self):
        source, site = Path(self.temp.name) / 'source', Path(self.temp.name) / 'out'
        source.mkdir()
        site.mkdir()
        (source / 'index.html').write_text('new preview')
        (site / 'index.html').write_text('previous preview')
        replace = deploy.os.replace
        def fail_install(src, dst):
            if Path(src).name == 'new':
                raise OSError('rename failed')
            return replace(src, dst)
        with patch.object(deploy.os, 'replace', side_effect=fail_install):
            with self.assertRaises(OSError):
                deploy.publish_site(source, site)
        self.assertEqual((site / 'index.html').read_text(), 'previous preview')

    def test_failed_rollback_keeps_recoverable_backup(self):
        source, site = Path(self.temp.name) / 'source', Path(self.temp.name) / 'out'
        source.mkdir()
        site.mkdir()
        (site / 'index.html').write_text('previous preview')
        replace = deploy.os.replace
        def fail_install_and_rollback(src, dst):
            if Path(src).name in {'new', 'previous'}:
                raise OSError('rename failed')
            return replace(src, dst)
        with patch.object(deploy.os, 'replace', side_effect=fail_install_and_rollback):
            with self.assertRaises((OSError, deploy.DeployError)):
                deploy.publish_site(source, site)
        backups = list(site.parent.glob('.out-*/previous/index.html'))
        self.assertEqual(len(backups), 1)
        self.assertEqual(backups[0].read_text(), 'previous preview')

    def test_refresh_revalidates_plan_and_dirty_checkout(self):
        gh = self.client()
        plan = deploy.create_plan(self.root, 'refresh', gh)
        self.write('src/Proof.lean', 'dirty proof')
        with self.assertRaisesRegex(deploy.DeployError, 'clean|dirty'):
            deploy.refresh(self.root, plan, Path(self.temp.name) / 'out', gh)
        self.commit()
        with self.assertRaises(deploy.DeployError):
            deploy.refresh(self.root, plan, Path(self.temp.name) / 'out', gh)
        gh.download.assert_not_called()

    def test_refresh_checks_revision_inside_site_artifact(self):
        gh = self.client()
        plan = deploy.create_plan(self.root, 'refresh', gh)
        def download(run_id, name, destination):
            destination.mkdir(parents=True, exist_ok=True)
            with tarfile.open(destination / 'site.tar.gz', 'w:gz') as tar:
                data = b'b' * 40
                info = tarfile.TarInfo('revision.txt')
                info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
        gh.download.side_effect = download
        site = Path(self.temp.name) / 'out'
        site.mkdir()
        (site / 'existing.html').write_text('existing preview')
        with self.assertRaisesRegex(deploy.DeployError, 'revision'):
            deploy.refresh(self.root, plan, site, gh)
        self.assertEqual((site / 'existing.html').read_text(), 'existing preview')


if __name__ == '__main__':
    unittest.main()
