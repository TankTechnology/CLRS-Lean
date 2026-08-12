# CLRS-Lean Site Architecture

This document records the fourth-edition-primary site design: CLRS-Lean is
deployed as a book-style Verso site rather than as unrelated proof pages.
For the full code, status, test, and tooling layer model, see
[`repository-architecture.md`](repository-architecture.md).

The Lean module root remains `CLRSLean`. Reader navigation starts at
`CLRSLean.FourthEdition`; third-edition-numbered `CLRSLean.Chapter_...` imports
remain available through the compatibility period but are not the primary
sidebar.

## Goals

- Make the deployed site easy to read from the homepage.
- Keep deployment simple: Lean source plus Verso, no separate frontend app.
- Give readers an honest status ledger for proved, partial, blocked, and
  deferred work.
- Keep maintainers aligned on which files change when a section is added.

## Information Architecture

```text
CLRSLean.lean                         project landing page
CLRSLean/FourthEdition.lean           canonical fourth-edition index
CLRSLean/FourthEdition/Chapter_19.lean fourth-edition Chapter 19 facade
CLRSLean/OnlineMaterial.lean          moved and third-edition-only material
CLRSLean/ProofPatterns.lean           reusable proof-pattern guide
CLRSLean/Progress.lean                generated progress dashboard
CLRSLean/Status.lean                  web-facing proof status ledger
CLRSLean/Workflow.lean                contributor workflow
CLRSLean/Chapter_xx/Section_xx_y.lean section-level literate proof
docs/proof-map.md                     longer maintainer ledger
docs/clrs-proof-progress.csv          chapter-level status source
docs/clrs-online-material.csv         disjoint supplementary-count source
docs/workflows/chapter-workflow.md    maintainer workflow notes
```

## Deployment Path

```text
Lean literate source
-> prepare: JSON + immutable digest + balanced four-shard plan
-> render: four full-context/disjoint-output Verso jobs
-> merge: digest, inventory, collision, and metadata validation
-> scripts/check_literate_html_weight.py
-> scripts/prepare_literate_site.py
-> one _site artifact
-> one GitHub Pages deployment
```

## Local Preview

Build and preview the same optimized site that GitHub Pages publishes. Local
concurrency is capped at four jobs:

```bash
python3 scripts/apply_verso_patch.py
lake build :literate
python3 scripts/prepare_literate_module_map.py \
  .lake/build/literate .lake/build/literate-module-map --prune-orphans
python3 scripts/plan_literate_shards.py \
  .lake/build/literate-module-map .lake/build/literate-shards \
  --shards 4 \
  --digest-input lean-toolchain \
  --digest-input lake-manifest.json \
  --digest-input lakefile.lean \
  --digest-input literate.toml
lake build verso-literate-html
python3 scripts/render_literate_shards.py \
  --executable .lake/packages/verso/.lake/build/bin/verso-literate-html \
  --module-map .lake/build/literate-module-map \
  --config literate.toml \
  --manifest .lake/build/literate-shards/manifest.json \
  --output .lake/build/literate-shard-output \
  --jobs 4
python3 scripts/merge_literate_shards.py \
  .lake/build/literate-shards/manifest.json \
  .lake/build/literate-html-merged \
  .lake/build/literate-shard-output/shard-{0,1,2,3}
python3 scripts/check_literate_html_weight.py .lake/build/literate-html-merged
python3 scripts/check_literate_html_freshness.py .lake/build/literate-html-merged
python3 scripts/prepare_literate_site.py .lake/build/literate-html-merged _site
python3 scripts/check_literate_rendering.py _site
python3 -m http.server --directory _site 8000
```

The module-map step validates each cached JSON against its current `.lean`
source and prunes orphan JSON plus its exact Lake sidecars. This prevents a
prefix cache restored from an older commit from republishing renamed or deleted
modules, and runs before CI saves the refreshed cache.

The serial renderer remains a diagnostic fallback and is not used by Pages:

```bash
python3 scripts/apply_verso_patch.py
lake build :literateHtml
```

Every shard loads the same complete module graph, preserving cross-references
and navigation, but emits only its assigned modules. Shard 0 alone emits the
landing, search, xref, and shared assets. Hover-document IDs use disjoint
one-billion-ID ranges. The merger rejects input-digest drift,
missing/duplicate/unexpected modules, unequal file collisions, and unequal
metadata keys before changing the destination directory.

The patch command expects the pinned Verso checkout to exist under
`.lake/packages/verso`; run it after normal dependency setup or use a
provisioned worktree. It is idempotent, so repeated publishing runs report each
tracked patch as `already-applied` without changing the dependency again.

Then open `http://localhost:8000/`.  Do not serve the raw Verso output
directly: reader-sidebar pruning, large-page optimization, rendering checks,
the project stylesheet, and the sitemap are all applied by the shared
preparation command.

`literate.toml` controls the sidebar order and page titles.  The public website
should not depend on a hand-written `docs/site/index.html`.

Source-module boundaries do not have to become entries in reader navigation.
The sidebar shows the 35 fourth-edition facades and top-level support pages.
Legacy theorem-bearing pages stay generated and searchable, but their nearest
canonical facade or Online Material is used as the visible navigation parent.
Supporting modules below a section, and children below top-level support pages
such as `ProofPatterns` and `Probability`, are omitted from the sidebar.  They
are still generated as complete pages and remain reachable from the nearest
visible parent's **Implementation details** section, site search, the sitemap,
and their direct URLs.  Keep these files independently importable and place
them under the main section's module path (for example,
`Section_xx_y/Helper.lean`).  Their `[order_children]` entries continue to
control generation and search order even though they are not reader-visible
navigation rows.

Verso is patched before rendering so tactic proof states are not serialized
into raw HTML.  This prevents compact shared proof-state data from expanding
into hundreds of megabytes of repeated DOM on long proofs.  The raw-output
guard rejects any residual tactic widgets and any single page above 25 MiB.

Large generated proof pages are still post-processed before deployment.  The
shared site-preparation command invokes the optimizer, rendering checks,
stylesheet copy, and sitemap generation for both local previews and GitHub
Pages.  The optimizer keeps anchors, rendered Lean code, search assets, and
copy buttons while retaining tactic-state removal as defense in depth and
removing hover metadata that makes browser parsing slow on large pages.  The
same post-processing step prunes non-reader modules from the static sidebar
HTML.  Any visible disclosure that loses all visible children becomes an
ordinary leaf row, avoiding empty arrows.  On a hidden implementation page,
the navigation script marks the nearest visible parent as current.

Both repository workflows are `workflow_dispatch` only.  Commits and pull
requests do not start Lean or Pages builds automatically; a maintainer manually
dispatches the appropriate workflow for an explicit verification or publishing
run.

All chapter disclosures still start open.  A small navigation-state script
persists sidebar scroll and manual chapter collapse/expand choices across page
loads.  New navigation-state versions intentionally start from an all-expanded
tree so stale browser storage cannot hide chapters after a redesign.  The
script stores disclosure state under stable normalized page paths, not raw
relative `href` values, so the same chapter remains open or closed after moving
between shallow chapter pages and deep section pages.  Chapter-title links
inside the sidebar must navigate without also toggling their parent disclosure
row; otherwise a click can accidentally save a collapsed state immediately
before the next page loads.

## Reader Flow

Readers should be able to move in three ways:

1. Project overview: homepage -> chapter guide -> section proof.
2. Audit path: homepage -> Proof Status -> partial or blocked item.
3. Contributor path: homepage -> Workflow -> chapter guide -> section file.

## Update Rule

When a new CLRS section is added, update these files together:

- the section `.lean` file;
- its chapter guide page;
- `CLRSLean/Status.lean` if the proof status changes;
- `literate.toml` if it should appear in navigation;
- `docs/proof-map.md` for the longer maintainer record.
