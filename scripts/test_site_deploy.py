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
        gh.caches.return_value = []
        return gh

    def cache_records(self):
        return [dict(ref='refs/heads/main', size_in_bytes=1, key=key) for key in
                [f'lake-Linux-X64-{"a" * 64}-{"b" * 64}-{self.base}',
                 f'verso-literate-Linux-{"c" * 64}-{self.base}']]

    def test_expired_inputs_can_use_exact_main_compilation_caches(self):
        self.write('literate.toml', 'hide_commands = []')
        self.commit()
        gh = self.client(())
        gh.caches.return_value = self.cache_records()
        plan = deploy.create_plan(self.root, 'refresh', gh)
        self.assertEqual((plan['mode'], plan['inputs_source'], plan['inputs_sha']), ('render', 'cache', self.base))

    def test_partial_other_revision_and_fork_caches_cannot_replace_inputs(self):
        records = self.cache_records()
        self.assertIsNone(deploy.compiled_cache_keys(records[:1], self.base))
        self.assertIsNone(deploy.compiled_cache_keys(records, '0' * 40))
        records[0]['ref'] = 'refs/pull/1/merge'
        self.assertIsNone(deploy.compiled_cache_keys(records, self.base))

    def test_cache_restoration_must_match_plan(self):
        gh = self.client(())
        gh.caches.return_value = self.cache_records()
        plan = dict(mode='render', inputs_source='cache', inputs_run_id=12, inputs_sha=self.base,
                    **deploy.compiled_cache_keys(gh.caches(), self.base))
        with self.assertRaisesRegex(deploy.DeployError, 'exact CI cache'):
            deploy.restore_inputs(self.root, plan, gh, self.root / 'restored')

    def test_verified_cache_restoration_preserves_compiled_revision(self):
        gh = self.client(())
        gh.caches.return_value = self.cache_records()
        plan = dict(mode='render', inputs_source='cache', inputs_run_id=12, inputs_sha=self.base,
                    **deploy.compiled_cache_keys(gh.caches(), self.base))
        self.write('.lake/build/literate/CLRSLean.json', '{}')
        self.write(deploy.RENDERER, 'trusted renderer fixture')
        with patch.dict(deploy.os.environ, {'CLRS_RESTORED_LAKE_CACHE': plan['lake_cache_key'],
                                           'CLRS_RESTORED_JSON_CACHE': plan['literate_cache_key']}):
            inputs, sha = deploy.restore_inputs(self.root, plan, gh, self.root / 'restored')
        self.assertEqual(sha, self.base)
        self.assertEqual((inputs / deploy.INPUT_REVISION).read_text().strip(), self.base)
        self.assertEqual((inputs / deploy.RENDERER).read_text(), 'trusted renderer fixture')

    def test_compiled_caches_never_authorize_changed_lean_sources(self):
        gh = self.client(())
        gh.caches.return_value = self.cache_records()
        self.write('src/Proof.lean', 'theorem changed := False\n')
        self.commit()
        with self.assertRaises(deploy.DeployError):
            deploy.create_plan(self.root, 'refresh', gh)

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
                (['literate.toml'], 'render'), (['unknown'], 'full')]:
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
        with patch.object(deploy, 'AUDITED_WORKFLOW_MIGRATIONS', {pair}):
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
        with patch.object(deploy, 'AUDITED_WORKFLOW_MIGRATIONS', {pair}):
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

    def test_config_refresh_selects_compiled_inputs_without_site_or_raw(self):
        self.write('literate.toml', 'hide_commands = []')
        head = self.commit()
        plan = deploy.create_plan(self.root, 'refresh', self.client(('literate-inputs',)))
        self.assertEqual(plan['mode'], 'render')
        self.assertEqual(plan['inputs_run_id'], 12)
        self.assertEqual(plan['inputs_sha'], self.base)
        self.assertEqual(plan['head_sha'], head)
        self.assertNotIn('raw_sha', plan)

    def test_config_refresh_cannot_reuse_stale_raw_or_site_without_inputs(self):
        self.write('literate.toml', 'hide_commands = []')
        self.commit()
        gh = self.client(('reader-site', 'literate-raw'))
        with self.assertRaisesRegex(deploy.DeployError, 'compiled inputs'):
            deploy.create_plan(self.root, 'refresh', gh)
        self.assertEqual(deploy.create_plan(self.root, 'auto', gh)['mode'], 'full')

    def test_source_and_renderer_changes_cannot_reuse_compiled_inputs(self):
        for path in ('src/Proof.lean', 'lean-toolchain', 'scripts/render_literate_shard.py',
                     'patches/verso.patch', 'scripts/plan_literate_shards.py'):
            with self.subTest(path=path):
                self.assertEqual(deploy.classify_paths(['literate.toml', path]), 'full')
        self.write('src/Proof.lean', 'changed proof')
        self.commit()
        with self.assertRaises(deploy.DeployError):
            deploy.create_plan(self.root, 'refresh', self.client(('literate-inputs',)))

    def test_render_rank_does_not_depend_on_path_order(self):
        paths = ['literate.toml', 'docs/literate/contents.json']
        self.assertEqual(deploy.classify_paths(paths), 'render')
        self.assertEqual(deploy.classify_paths(paths[::-1]), 'render')

    def test_render_input_revalidation_rejects_expired_artifact(self):
        self.write('literate.toml', 'hide_commands = []')
        self.commit()
        gh = self.client(('literate-inputs',))
        plan = deploy.create_plan(self.root, 'refresh', gh)
        gh.artifacts.return_value = set()
        with self.assertRaisesRegex(deploy.DeployError, 'missing or expired'):
            deploy.refresh(self.root, plan, Path(self.temp.name) / 'site', gh)
        gh.download.assert_not_called()

    def test_render_preserves_separate_compiled_raw_and_site_revisions(self):
        self.write('literate.toml', 'hide_commands = []')
        head = self.commit()
        gh = self.client(('literate-inputs',))
        plan = deploy.create_plan(self.root, 'refresh', gh)
        site = Path(self.temp.name) / 'site'
        raw_output = Path(self.temp.name) / 'raw.tar.gz'
        def render(root, plan, github, temp, inputs_output):
            raw = temp / 'raw'
            raw.mkdir()
            (raw / 'index.html').write_text('rendered theorem')
            return raw, dict(raw_sha=head, compiled_sha=self.base)
        def assemble(args, root):
            if Path(args[1]).name == 'audit_reader_book.py':
                self.assertIn('--compiled', args)
                return
            self.assertEqual(Path(args[1]).name, 'prepare_literate_site.py')
            Path(args[-1]).mkdir()
            (Path(args[-1]) / 'index.html').write_text('assembled theorem')
        with patch.object(deploy, 'render_inputs', side_effect=render), \
                patch.object(deploy, 'command', side_effect=assemble):
            # Keep Git validation real while mocking only the assembler subprocess.
            with patch.object(deploy, 'git', side_effect=lambda root, *args: self.git(*args)):
                deploy.refresh(self.root, plan, site, gh, raw_output)
        self.assertEqual((site / 'compiled-revision.txt').read_text().strip(), self.base)
        self.assertEqual((site / 'content-revision.txt').read_text().strip(), head)
        self.assertEqual((site / 'revision.txt').read_text().strip(), head)
        gh.download.assert_not_called()
        self.assertTrue(raw_output.is_file())

    def test_render_replans_four_shards_and_carries_compile_provenance(self):
        import json
        import shutil
        self.write('literate.toml', 'hide_commands = []')
        head = self.commit()
        gh = self.client(('literate-inputs',))
        plan = deploy.create_plan(self.root, 'refresh', gh)
        temp = Path(self.temp.name) / 'render'
        temp.mkdir()
        inputs_output = Path(self.temp.name) / 'inputs.tar.zst'
        def download(run_id, name, destination):
            self.assertEqual((run_id, name), (12, 'literate-inputs'))
            destination.mkdir()
            with tarfile.open(destination / 'literate-inputs.tar.zst', 'w') as tar:
                for path, data in {
                    deploy.INPUT_REVISION: self.base.encode(),
                    deploy.RENDERER: b'trusted executable',
                    '.lake/build/literate/Proof.json': b'{}',
                }.items():
                    info = tarfile.TarInfo(path)
                    info.size = len(data)
                    tar.addfile(info, io.BytesIO(data))
        gh.download.side_effect = download
        calls = []
        def run(args, root=None):
            calls.append(args)
            if args[0] == 'zstd':
                shutil.copyfile(args[3], args[5])
            elif args[0] == 'tar':
                extracted = Path(args[5])
                self.assertEqual((extracted / deploy.INPUT_REVISION).read_text().strip(), self.base)
                inputs_output.write_bytes(b'packed inputs')
            elif Path(args[1]).name == 'merge_literate_shards.py':
                Path(args[3]).mkdir()
        with patch.object(deploy, 'command', side_effect=run), \
                patch.object(deploy, 'git', side_effect=lambda root, *args: self.git(*args)):
            raw, record = deploy.render_inputs(self.root, plan, gh, temp, inputs_output)
        self.assertEqual(record, dict(raw_sha=head, compiled_sha=self.base))
        self.assertEqual(json.loads((raw / deploy.RAW_PROVENANCE).read_text()), record)
        render_calls = [args for args in calls if len(args) > 1 and
                        Path(args[1]).name == 'render_literate_shard.py']
        self.assertEqual(len(render_calls), 4)
        for i, args in enumerate(render_calls):
            self.assertEqual(args[args.index('--shard-index') + 1], str(i))
            self.assertEqual(args[args.index('--config') + 1], str(self.root / 'literate.toml'))
            self.assertEqual(args[args.index('--executable') + 1], str(temp / 'inputs' / deploy.RENDERER))
        self.assertFalse(any(args[0] in {'lean', 'lake', 'elan'} for args in calls))
        self.assertTrue(inputs_output.is_file())
        self.assertTrue((temp / 'inputs' / deploy.RENDERER).stat().st_mode & 0o100)

    def test_portable_input_plan_survives_moving_to_another_runner(self):
        import json
        import shutil
        scripts = Path(deploy.__file__).parent
        for name in ('prepare_literate_module_map.py', 'plan_literate_shards.py'):
            self.write('scripts/' + name, (scripts / name).read_text())
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'literate.toml'):
            self.write(name, 'fixture configuration')
        inputs = Path(self.temp.name) / 'first-runner'
        compiled = inputs / '.lake/build/literate/Proof.json'
        compiled.parent.mkdir(parents=True)
        compiled.write_text('{}')
        module_map, shard_plan = deploy.plan_inputs(self.root, inputs, portable=True)
        self.assertEqual(module_map.read_text(), 'Proof\t.lake/build/literate/Proof.json\tsrc\n')
        manifest = json.loads((shard_plan / 'manifest.json').read_text())
        other = Path(self.temp.name) / 'second-runner'
        shutil.move(inputs, other)
        deploy.command([__import__('sys').executable, str(self.root / 'scripts/plan_literate_shards.py'),
                        str(other / '.lake/build/literate-module-map'), str(other / 'replanned'),
                        '--shards', '4',
                        *[arg for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'literate.toml')
                          for arg in ('--digest-input', str(self.root / name))]], other)
        moved = json.loads((other / 'replanned/manifest.json').read_text())
        self.assertEqual(manifest, moved)
        self.assertEqual(manifest['module_count'], 1)
        self.assertEqual(manifest['shard_count'], 4)

    def test_ci_input_preparation_revalidates_current_render_plan(self):
        self.write('literate.toml', 'hide_commands = []')
        self.commit()
        gh = self.client(('literate-inputs',))
        plan = deploy.create_plan(self.root, 'refresh', gh)
        output = Path(self.temp.name) / 'inputs.tar.zst'
        for key, value in (('mode', 'full'), ('head_sha', self.base)):
            with self.subTest(key=key), self.assertRaises(deploy.DeployError):
                deploy.prepare_inputs(self.root, dict(plan, **{key: value}), output, gh)
        gh.artifacts.return_value = set()
        with self.assertRaisesRegex(deploy.DeployError, 'missing or expired'):
            deploy.prepare_inputs(self.root, plan, output, gh)
        gh.download.assert_not_called()

    def test_compiled_provenance_refuses_hidden_source_change(self):
        # A newer artifact run cannot make older compiled inputs compatible.
        old = self.base
        self.write('src/Proof.lean', 'changed proof')
        self.base = self.commit()
        self.write('literate.toml', 'hide_commands = []')
        self.commit()
        gh = self.client(('literate-inputs',))
        plan = deploy.create_plan(self.root, 'refresh', gh)
        temp = Path(self.temp.name) / 'render'
        temp.mkdir()
        def extract(archive, inputs):
            revision = inputs / deploy.INPUT_REVISION
            revision.parent.mkdir(parents=True)
            revision.write_text(old)
        with patch.object(deploy, 'safe_extract', side_effect=extract), \
                patch.object(deploy, 'command'), \
                patch.object(deploy, 'git', side_effect=lambda root, *args: self.git(*args)):
            with self.assertRaisesRegex(deploy.DeployError, 'compiled revision requires'):
                deploy.render_inputs(self.root, plan, gh, temp)

    def test_audited_render_workflow_hash_matches_exact_file(self):
        workflow = Path(deploy.__file__).resolve().parents[1] / deploy.WORKFLOW
        self.assertEqual(hashlib.sha256(workflow.read_bytes()).hexdigest(),
                         deploy.AUDITED_RENDER_WORKFLOW)

    def test_raw_provenance_keeps_original_compilation_and_render_revisions(self):
        import json
        raw = Path(self.temp.name) / 'raw'
        raw.mkdir()
        self.write('literate.toml', 'hide_commands = []')
        rendered = self.commit()
        self.write('scripts/book_presentation.py', '# assembled')
        published = self.commit()
        (raw / deploy.RAW_PROVENANCE).write_text(json.dumps(
            dict(raw_sha=rendered, compiled_sha=self.base)))
        self.assertEqual(deploy.raw_provenance(self.root, raw, published),
                         dict(raw_sha=rendered, compiled_sha=self.base))
        (raw / deploy.RAW_PROVENANCE).write_text(json.dumps(
            dict(raw_sha=self.base, compiled_sha=self.base)))
        with self.assertRaisesRegex(deploy.DeployError, 'raw revision requires'):
            deploy.raw_provenance(self.root, raw, published)

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
