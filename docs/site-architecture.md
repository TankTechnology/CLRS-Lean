# CLRS-Lean Site Architecture

This document records the Scheme B site design: CLRS-Lean is deployed as a
book-style Verso site rather than as a collection of unrelated proof pages.
For the full code, status, test, and tooling layer model, see
[`repository-architecture.md`](repository-architecture.md).

The public project and repository name is `CLRS-Lean`.  The Lean module root
remains `CLRSLean`, so source paths and imports continue to use `CLRSLean/...`
and `CLRSLean.Chapter_...`.

## Goals

- Make the deployed site easy to read from the homepage.
- Keep deployment simple: Lean source plus Verso, no separate frontend app.
- Give readers an honest status ledger for proved, partial, blocked, and
  deferred work.
- Keep maintainers aligned on which files change when a section is added.

## Information Architecture

```text
CLRSLean.lean                         project landing page
CLRSLean/ProofPatterns.lean           reusable proof-pattern guide
CLRSLean/Chapter_02.lean              Chapter 2 guide
CLRSLean/Chapter_16.lean              Chapter 16 guide
CLRSLean/Chapter_23.lean              Chapter 23 guide
CLRSLean/Progress.lean                generated progress dashboard
CLRSLean/Status.lean                  web-facing proof status ledger
CLRSLean/Workflow.lean                contributor workflow
CLRSLean/Chapter_xx/Section_xx_y.lean section-level literate proof
docs/proof-map.md                     longer maintainer ledger
docs/clrs-proof-progress.csv          chapter-level status source
docs/workflows/chapter-workflow.md    maintainer workflow notes
```

## Deployment Path

```text
Lean literate source
-> lake build
-> lake build :literateHtml
-> scripts/prepare_literate_site.py
-> _site
-> GitHub Pages
```

## Local Preview

Build and preview the same optimized site that GitHub Pages publishes:

```bash
VERSO_OUT="$(lake query :literateHtml)"
python3 scripts/check_literate_html_freshness.py "$VERSO_OUT"
python3 scripts/prepare_literate_site.py "$VERSO_OUT" _site
python3 -m http.server --directory _site 8000
```

Then open `http://localhost:8000/`.  Do not serve the raw Verso output
directly: reader-sidebar pruning, large-page optimization, rendering checks,
the project stylesheet, and the sitemap are all applied by the shared
preparation command.

`literate.toml` controls the sidebar order and page titles.  The public website
should not depend on a hand-written `docs/site/index.html`.

Source-module boundaries do not have to become entries in the reader
navigation.  The sidebar keeps the existing flat top-level pages and, within a
chapter, shows only the chapter page plus its direct `Section_*` children.
Supporting modules below a section, and children below top-level support pages
such as `ProofPatterns` and `Probability`, are omitted from the sidebar.  They
are still generated as complete pages and remain reachable from the nearest
visible parent's **Implementation details** section, site search, the sitemap,
and their direct URLs.  Keep these files independently importable and place
them under the main section's module path (for example,
`Section_xx_y/Helper.lean`).  Their `[order_children]` entries continue to
control generation and search order even though they are not reader-visible
navigation rows.

Large generated proof pages are post-processed before deployment.  The shared
site-preparation command invokes the optimizer, rendering checks, stylesheet
copy, and sitemap generation for both local previews and GitHub Pages.  The
optimizer keeps anchors, rendered Lean code, search assets, and copy buttons, while
removing tactic-state DOM and hover metadata that make browser parsing slow on
long files such as the Huffman proof.  The same post-processing step prunes
non-reader modules from the static sidebar HTML and turns any visible
disclosure that loses all visible children into an ordinary leaf row, avoiding
empty arrows.  On a hidden implementation page, the navigation script marks
the nearest visible parent as current.

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
