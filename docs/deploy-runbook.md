# Deploy runbook — CLRS-Lean Verso site

This document covers deploying the literate Verso site to
`https://tanktechnology.github.io/CLRS-Lean/`.

## How deploys work

- **Trigger**: `workflow_dispatch` only — no push-triggered deploys.
- **Workflow**: `.github/workflows/pages.yml`
- **Deploy environment**: `github-pages` (protected)
- **Concurrency**: `group: pages`, `cancel-in-progress: true` — only one deploy
  pipeline runs at a time; a new trigger cancels any in-flight deploy.

### Pipeline stages

| Stage | What it does |
|---|---|
| `prepare` | Checkout → `check_repository.py` → `lean-action` (mathlib cache) → Verso patch → literate JSON cache → `lake build :literate` → 4-way shard plan → upload `literate-inputs` |
| `render` (×4) | Each shard downloads inputs, runs `render_literate_shard.py` on its chapter subset, uploads `literate-shard-N` |
| `merge` | Downloads all shards → `merge_literate_shards.py` → weight + freshness checks → `prepare_literate_site.py` → rendering check → upload Pages artifact |
| `deploy` | `actions/deploy-pages@v4` (only on `main` branch) |

### Cache key

```
verso-literate-${{ runner.os }}-${{ hashFiles('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'literate.toml') }}-${{ github.sha }}
```

The key depends on four files: `lean-toolchain`, `lake-manifest.json`,
`lakefile.lean`, and `literate.toml`.  **Do not touch `literate.toml`** unless
you are adding or removing a section from the site navigation — a change
invalidates the cache and forces a cold build.

A secondary restore key drops the SHA suffix, so a warm build can reuse the
literate JSON from the most recent run with the same dependency files.

## Timing

| Scenario | Approximate wall-clock |
|---|---|
| Cold build (no literate JSON cache hit) | ~67 minutes |
| Warm build (cache hit, no dep changes) | ~15–20 minutes |
| Cache hit + no `.lean` changes | ~10 minutes |

## Triggering a deploy

### Via `gh` CLI

```bash
gh workflow run pages.yml --repo TankTechnology/CLRS-Lean --ref main
```

### Via the GitHub API

```bash
curl -X POST \
  -H "Authorization: Bearer $GITHUB_TOKEN" \
  -H "Accept: application/vnd.github+json" \
  "https://api.github.com/repos/TankTechnology/CLRS-Lean/actions/workflows/pages.yml/dispatches" \
  -d '{"ref":"main"}'
```

### Via the GitHub web UI

Navigate to the Actions tab → "Build and deploy Verso site" → "Run workflow".

## Watching a deploy

```bash
# Get the latest run ID
gh run list --repo TankTechnology/CLRS-Lean --workflow=pages.yml --limit 1 --json databaseId

# Watch until completion
gh run watch <RUN_ID> --repo TankTechnology/CLRS-Lean

# Check the logs if something fails
gh run view <RUN_ID> --repo TankTechnology/CLRS-Lean --log
```

## Verifying the site after deploy

```bash
# Check the site returns HTTP 200
curl -s -o /dev/null -w "HTTP %{http_code}\n" https://tanktechnology.github.io/CLRS-Lean/

# Check the landing page content
curl -s https://tanktechnology.github.io/CLRS-Lean/ | head -5
```

## Quota caution

- **Workflow minutes are budgeted.**  A cold build costs ~67 minutes.  Only
  trigger a deploy when the site needs to reflect new commits on `main`.
- The `lean-action` step pulls the mathlib cache on every run regardless of
  warm/cold state — this is a fixed cost per run.
- Artifacts are retained for 1 day only.

## Rollback

A rollback means redeploying the last known-good SHA:

```bash
# Trigger a deploy from a specific ref (must be a branch or tag)
# For a specific commit, create a temporary branch pointing at it first:
git checkout -b deploy-rollback <KNOWN-GOOD-SHA>
git push origin deploy-rollback
gh workflow run pages.yml --repo TankTechnology/CLRS-Lean --ref deploy-rollback
# Delete the branch after the deploy completes
git push origin --delete deploy-rollback
```

Alternatively, if the last known-good SHA is already on `main` (e.g., a revert
was merged), just trigger a normal deploy from `main`.

## Troubleshooting

| Symptom | Likely cause | Fix |
|---|---|---|
| `cache-hit` is `false` | `literate.toml`, `lean-toolchain`, `lake-manifest.json`, or `lakefile.lean` changed | Expected if those files were modified; wait for the cold build |
| `merge` fails on weight check | A shard produced fewer pages than expected | Check the `prepare` step's shard plan for anomalies |
| `merge` fails on freshness check | A stale artifact was used | Re-trigger — the concurrency group may have cancelled a previous run |
| `deploy` step doesn't run | The workflow was triggered from a non-`main` branch | Deploy only runs on `refs/heads/main` |
| Site returns 404 or old content | GitHub Pages CDN propagation delay | Wait 1–2 minutes and retry |