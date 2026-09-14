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
src/CLRSLean.lean                          project landing page
src/CLRSLean/FourthEdition.lean            canonical fourth-edition index
src/CLRSLean/FourthEdition/Chapter_19.lean fourth-edition Chapter 19 facade
src/CLRSLean/OnlineMaterial.lean           moved and third-edition-only material
src/CLRSLean/ProofPatterns.lean            reusable proof-pattern guide
src/CLRSLean/Progress.lean                 generated progress dashboard
src/CLRSLean/Status.lean                   web-facing proof status ledger
src/CLRSLean/Workflow.lean                 contributor workflow
src/CLRSLean/Chapter_xx/Section_xx_y.lean  section-level literate proof
docs/scope.md                         stable advertised-boundary statement
docs/clrs-proof-progress.csv          chapter-level status source
docs/clrs-online-material.csv         disjoint supplementary-count source
docs/workflows/chapter-workflow.md    maintainer workflow notes
```

## Deployment Path

The manual Pages workflow defaults to `mode=auto`. Before installing Lean it
compares the current commit with a successful `main` deployment that still has
a reusable artifact:

| Changes | Selected path | Work performed |
| --- | --- | --- |
| Images, CSS, JavaScript, or non-rendering documentation | `assets` | Restore verified pages and synchronize static assets |
| Website assembly or presentation scripts | `presentation` | Restore raw Verso HTML and rerun website assembly |
| Lean source, dependencies, renderer patches/configuration, unknown inputs, or unavailable artifacts | `full` | Compile Lean, render four shards, assemble and validate |

The asset path preserves proof-page HTML byte-for-byte. Deleted owned assets are
removed. Both refresh paths retain the reader checks and Chromium smoke test.
Reuse requires an ancestor commit, the same workflow and repository, a successful
`main` run, an unexpired artifact, and a matching embedded revision. Renames are
checked as deletion plus addition, so moving a file cannot bypass classification.
Workflow edits also require a full build, since they can change renderer flags
or the public base URL. The initial September 14 routing/retention migration has
one audited exception pinned to the exact old and new workflow content hashes
in `scripts/site_deploy.py`; modifying either version invalidates that exception.

```sh
# Choose the least expensive safe path automatically.
gh workflow run pages.yml --ref main
# Require a refresh; fail clearly if reuse is unsafe instead of compiling Lean.
gh workflow run pages.yml --ref main -f mode=refresh
# Explicitly rebuild all Lean and renderer inputs.
gh workflow run pages.yml --ref main -f mode=full
```

`reader-site` stores prepared pages and `literate-raw` stores raw rendered pages
for 90 days. Normal asset refreshes download only the prepared pages. Presentation
refreshes also retain their reused raw snapshot. Expired or missing raw data can
require a full rebuild for presentation changes; a still-valid prepared site is
enough for asset changes. Download or provenance errors fail visibly rather than
quietly launching an expensive build.

The first refresh can bootstrap from the previous workflow's `github-pages`
artifact and, while available, its four shards and immutable inputs. Subsequent
refreshes use the longer-lived archives. The existing full-build path is:

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

For a local refresh from retained CI artifacts, start from a clean tracked tree
and use GitHub CLI authentication with repository Actions read access:

```sh
python3 scripts/site_deploy.py plan --mode refresh --output /tmp/site-plan.json
python3 scripts/site_deploy.py refresh --plan /tmp/site-plan.json --site _site
python3 scripts/check_reader_site.py _site
```

This uses committed inputs; commit local source or asset changes before planning.
The workflow runs the full repository metadata checks before making this choice.

`literate.toml` controls the sidebar order and page titles.  The public website
should not depend on a hand-written `docs/site/index.html`.

Source-module boundaries do not have to become entries in reader navigation.
The sidebar shows the 35 fourth-edition chapter facades, their section pages
as child rows (in the order given by `[order_children]`), and the top-level
support pages. The site-preparation step also appends the complete rendered
content of each direct section to its chapter facade in that same order. Links
from the chapter guide to those sections become same-page anchors, while the
standalone section pages remain generated for focused reading, search results,
and stable direct URLs. Embedded IDs are namespaced by section so repeated
heading names cannot create ambiguous chapter-local anchors.

Legacy theorem-bearing pages stay generated and searchable, but their nearest
canonical facade or Online Material is used as the visible navigation parent.
Supporting modules below a section, and children below top-level support pages
such as `ProofPatterns` and `Probability`, are omitted from the sidebar and are
not appended to chapter pages. They remain reachable from the nearest visible
parent's **Implementation details** section, site search, the sitemap, and their
direct URLs. Keep these files independently importable and place them under the
main section's module path (for example, `Section_xx_y/Helper.lean`). Their
`[order_children]` entries continue to control generation and search order even
though they are not reader-visible navigation rows.

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
the static navigation rewrite marks the nearest visible parent as current.

Both repository workflows are `workflow_dispatch` only.  Commits and pull
requests do not start Lean or Pages builds automatically; a maintainer manually
dispatches the appropriate workflow for an explicit verification or publishing
run.

The fourth-edition chapter index is a permanent, non-collapsible container.
All 35 chapter names are visible in the sidebar without opening a parent group,
including on the homepage and in browsers with an old saved collapse state.
Third-edition compatibility chapter rows are excluded from the reader sidebar.

Individual chapters may still disclose their section lists. The generated HTML
opens the active chapter and keeps the remaining chapter names visible. Browser
storage does not change the initial tree or hide it while scripts load.
Chapter-title links navigate without toggling the chapter's disclosure.

## Reader Flow

Readers should be able to move in three ways:

1. Project overview: homepage -> chapter guide with inline section proofs.
2. Audit path: homepage -> Progress Dashboard / Proof Status -> source proof.
3. Contributor path: homepage -> Contributor Guide -> chapter guide -> section file.

## Update Rule

When a new CLRS section is added, update these files together:

- the section `.lean` file;
- its chapter guide page;
- `src/CLRSLean/Status.lean` if the proof status changes;
- `literate.toml` if it should appear in navigation;
- a focused interface test for any newly advertised declaration;
- `docs/scope.md` only when the project-wide claim boundary changes.

## Public entry pages

The homepage introduces the project, its qualified completion milestone, and
three paths: read the chapters, inspect proof coverage, or contribute. Detailed
build instructions belong in this runbook and the contributor documents.

The chapter index groups Chapters 1–35 into foundations, sorting, data
structures, design techniques, advanced data structures, graph algorithms, and
selected topics. Every chapter link includes its number and textbook title.

The top-level sidebar orders the chapter tree first, then Progress Dashboard
and Proof Status, followed by online material, reusable tools, research
extensions, and Contributor Guide. The contributor page retains its stable
`CLRSLean/Workflow/` URL. Internal source names do not need to be reader titles.

## Reader presentation contract

`literate.toml` owns the canonical section inventory. `literate_navigation.py`
uses that inventory to exclude compatibility facades even when Verso emits them
as direct children. All 35 chapter names remain visible. The active chapter's
section disclosure is opened in generated HTML, with no storage-dependent
initial layout or navigation-hiding bootstrap.

`inline_chapter_sections.py` handles section composition and anchor namespacing;
`reader_layout.py` handles chapter reading order and the page contents list.
Before composition, `reader_implementation.py` enriches canonical section
facades that have no declaration anchors. It follows project imports to their
first declaration-bearing implementation pages and copies the existing
rendered definitions and complete proof bodies into the section. Explicit
result links resolve to the inserted code, and source links retain access to
the original implementation. No Lean definitions or proofs are generated by
this presentation step.

`docs/literate/reader-implementations.json` selects focused public blocks for
the shared potential-method framework and the two large NP-completeness
facades. The latter expose their public definitions and theorem proofs while
linking to the source modules for the remaining supporting implementation;
they do not concatenate hundreds of implementation files. Selection errors
and oversized enrichment fail assembly instead of silently truncating it.
`reader-implementation-coverage.json` records the inserted source declarations
and resolved result links. The same enriched content is used in standalone
sections and combined chapters, with distinct namespaced anchors.

The chapter starts with its title and same-page section list, followed by the
section bodies. Detailed source, scope and implementation notes remain below
the main text, linked from a visible scope notice. Embedded headings are nested under
the chapter heading and retain their original anchor identifiers. Canonical
section headings and their TOC labels use the same configured titles as the
sidebar; changing a display title preserves existing fragment URLs.

`docs/literate/clrs-literate.css` owns the theme and responsive layout.
`docs/literate/clrs-reader.js` provides optional keyboard/menu behavior; it does
not assemble content, hide navigation or restore a different initial tree.

Run `python3 scripts/check_reader_site.py _site` after assembly. Pages runs this
same check before uploading: all chapter pages must include the canonical
navigation, inline section anchors, concrete declarations in every canonical
section and its embedded chapter body, complete page contents, unique IDs and
working local links. Browser smoke tests should include search, same-page links,
mobile menu, light/dark modes and JavaScript-disabled chapter navigation.

The pinned Verso search adapter (`prepare_search_assets.py`) handles paste and
touch-keyboard input as well as key events. `clrs-search.js` loads the full-text
index on first search focus; ordinary chapter reading does not fetch it. The
standalone search page retains its full index. Failed lazy loading leaves a
retry message and semantic declaration search available.

Pages also runs `scripts/smoke_reader_site.py` with Chromium before uploading.
For local use, serve `_site` and run:

```sh
python3 scripts/smoke_reader_site.py --base-url http://127.0.0.1:8765/
```

Use `--browser /path/to/chromium` for a system browser. The check saves screenshots
under `/tmp/clrs-reader-smoke` by default. After deployment, `revision.txt` exposes
the exact published commit for public verification.

## Book presentation and launch assets

`scripts/book_presentation.py` adds the frontispiece, sequential chapter links
and closing matter after section composition. The original source headings,
fragment targets and coverage statements remain in the document. Chapter 1
links back to the contents; Chapter 35 closes the book and links to Chapter 34
and the contents. Front matter is rendered on both homepage routes.

`docs/literate/clrs-book.css` owns this presentation layer. The current project
cover, navigation icon, browser icons and 1200-by-800 social image live in
`docs/literate/assets`; source artwork and export instructions are recorded in
[`branding/README.md`](branding/README.md). The cover preserves its full aspect
ratio on desktop and mobile. The closing illustration remains an SVG. These
are illustrations, not proof diagrams. All assets are copied by the shared site
assembler; chapter reading adds no new JavaScript dependency.

The historical September 13 social card source is
`docs/releases/assets/share-card.html`; it is separate from the current project
share image. To regenerate that card, reading screenshots and MP4 walkthrough,
serve the prepared site and run:

```sh
python3 scripts/prepare_release_media.py --base-url http://127.0.0.1:8000/ \
  --browser /snap/bin/chromium
```

This command requires Playwright with its video encoder and system `ffmpeg`.
It captures actual browser navigation from the cover through the contents,
insertion-sort correctness, Chapter 33 and the closing matter. The English
announcement stays in `docs/releases/2026-09-13-twitter-draft.md` until explicitly
published. Website deployment and social publication are separate actions.
