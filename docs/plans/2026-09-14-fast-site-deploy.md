# Fast website deployment implementation plan

**Goal:** Publish image/style changes without running Lean or rendering the book again.

**Architecture:** Keep the manual Pages entry point and select `assets`,
`presentation`, or `full` before installing Lean. Reuse only unexpired artifacts
from successful `main` runs of the same Pages workflow, with an ancestor commit
and a checked change classification. Unknown inputs require a full build.

**Stack:** Python standard library, Git, GitHub CLI, GitHub Actions artifacts.

## Implementation

- [x] Add `scripts/site_deploy.py` and focused regression tests. The `plan`
  command writes `plan.json` and GitHub outputs `mode` and `reason`. It compares
  Git trees with rename detection disabled so both added and removed paths are
  classified. `auto` falls back to full; explicit `refresh` refuses unsafe reuse.
- [x] Implement `refresh --plan plan.json --site _site`: validate provenance,
  download and safely extract the baseline site, then synchronize owned static
  assets or rerun the existing assembler from a compatible raw artifact.
  Preserve Lean pages byte-for-byte for asset changes and remove deleted assets.
- [x] Support a one-time baseline from the existing `github-pages` artifact and
  legacy shard/input artifacts, so the currently running build is reusable.
- [x] Extend `.github/workflows/pages.yml`: default `auto`, optional `refresh`
  and `full`; full-only Lean jobs; separate refresh job without Lean setup;
  common guarded production deployment. Save `reader-site` and `literate-raw`
  archives for 90 days. Keep all triggers manual.
- [x] Add workflow routing tests and register helper tests in repository checks.
  Test CSS/images, template changes, Lean/config/dependency/unknown changes,
  renames/deletions, expired/missing artifacts and invalid provenance.
- [x] Reject workflow changes by default. Permit only the exact audited
  September 14 migration hash pair, whose original rendering commands and base
  URL are unchanged, to seed the first refresh without recompilation.
- [x] Update `docs/site-architecture.md` and `CLAUDE.md` with automatic routing,
  retention, explicit full rebuild, and the local refresh command.
- [x] Run repository checks, local fixture refresh and browser smoke tests;
  obtain independent review.
- [ ] Merge and dispatch a real refresh after the existing full build completes.
  Verify skipped Lean jobs, elapsed time and the public revision/image URLs.

## Acceptance commands

```sh
uv run python scripts/test_site_deploy.py
uv run python scripts/test_workflow_policy.py
uv run python scripts/check_repository.py
gh workflow run pages.yml --ref main -f mode=refresh
```

The first retained baseline may require the existing full build to finish.
Do not launch another full build just to install the optimization, or cancel
the only running build before its replacement artifacts exist.
