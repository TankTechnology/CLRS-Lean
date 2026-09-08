# Reader-Site Consistency and Deployment Closure Design

Date: 2026-08-27

## Goal

Publish the current proof state through a reader-facing site whose fourth-edition
navigation, labels, landing page, and audit data agree with the repository.
Keep the existing Lean, Verso, and GitHub Pages architecture intact.

The live site is currently healthy and all 35 fourth-edition chapter pages are
reachable, but the deployed content trails `main`, several navigation labels are
stale, the mobile breadcrumb exposes a squeezed intermediate label, and the
default desktop sidebar opens the full 35-chapter tree.

## Selected approach

Make a bounded consistency pass in the existing generation pipeline, backed by
focused regression tests.  Generated HTML remains the responsibility of the
current Python postprocessor; reader prose remains in Literate Lean modules; and
the existing Pages workflow remains the deployment mechanism.

This is preferred to a theme rewrite or a second navigation system because the
current desktop and mobile presentation is otherwise consistent, accessible,
and already used by every chapter page.

## Changes

### Fourth-edition metadata

- Remove the four stale `(partial)` suffixes from fourth-edition Chapter 24
  entries in `literate.toml`.  This changes presentation metadata only and does
  not weaken or expand any proof claim.
- Rename the fourth-edition Chapter 29 duality titles from `29.4` to `29.3`, in
  agreement with the canonical module path, chapter guide, and edition map.
- Leave legacy, non-fourth-edition titles and compatibility module paths alone.

### CSV integrity gate

- Treat `csv.DictReader` overflow fields (`None` keys) as schema errors in both
  the fourth-edition map and online-material ledger loaders.
- Quote the nine current coverage notes whose commas are being parsed as extra
  columns.
- Add a regression fixture proving that an unquoted extra field fails with its
  file and line number.

This closes a gap where the repository audit accepted malformed rows while
silently discarding part of their prose.

### Mobile breadcrumb

At widths up to 768 pixels, show only the first breadcrumb item and the existing
search affordance.  Hide all later breadcrumb items instead of hiding only the
last item.  Desktop breadcrumbs remain unchanged.

This removes the stray one-character `C` produced when the intermediate
`CLRS Fourth Edition` breadcrumb is squeezed between the menu and search
controls.

### Reader sidebar state

The HTML optimizer's injected navigation script will use the following default
policy when no saved browser state exists:

- open only the details elements that contain the current page;
- keep the fourth-edition root open on fourth-edition pages;
- leave unrelated chapter branches closed;
- on project and fourth-edition landing pages, avoid opening every chapter;
- after the reader toggles branches, continue restoring the saved state exactly
  as today.

The current-page fallback and automatic ancestor opening remain in place, so a
deep link is always visible even if Verso did not mark it as current.

### Fourth-edition landing page

Expand `CLRSLean/FourthEdition.lean` from a compatibility note into a compact
reader entry point.  It will contain:

- a short statement that this is the canonical CLRS fourth-edition tree;
- links to Progress and Status for coverage and audit information;
- a recommended start path through Chapters 1 and 2;
- four compact chapter groups covering Chapters 1–9, 10–19, 20–29, and 30–35;
- a link to Online Material for topics outside the fourth-edition main text;
- the existing compatibility-path explanation, clearly labeled as maintainer
  information.

The page will link to chapter guides instead of duplicating theorem counts or
status claims, keeping ongoing documentation maintenance low.

## Verification

Implementation follows test-driven development:

1. Add failing unit tests for malformed CSV rows, navigation default state,
   mobile breadcrumb selectors, and the corrected Chapter 24/29 titles.
2. Implement the smallest changes that make those tests pass.
3. Run focused Python tests, `scripts/check_repository.py`, `git diff --check`,
   and the Lean target for `CLRSLean.FourthEdition`.
4. Render representative root, fourth-edition, Chapter 24, Chapter 29, and
   Chapter 34 pages and inspect them at desktop and 390-pixel mobile widths.
5. Require no browser console errors, no global horizontal overflow, visible
   current-page navigation, and correct labels.

After integration into `main`, trigger the existing Pages workflow and do not
declare deployment complete until the workflow succeeds and the live site
passes these checks:

- all 35 fourth-edition chapter URLs return HTTP 200;
- Progress reports the repository's current count of 470 tracked entries;
- fourth-edition Chapter 24 navigation contains no stale `(partial)` labels;
- fourth-edition Chapter 29 navigation labels Duality as 29.3;
- the mobile header has no stray intermediate breadcrumb;
- unrelated desktop chapter branches are closed for a new browser session.

## Explicit non-goals

- No theorem, proof, namespace, or compatibility-import change.
- No new frontend framework or redesign of the existing visual language.
- No search-index format, lazy-loading, or 36 MB payload rearchitecture.
- No change to the Literate JSON build/cache architecture or the roughly
  two-hour full build boundary.
- No release file or duplicate hand-maintained proof dashboard.

The search-index payload and full deployment latency will be recorded as two
separate follow-up issues after this bounded pass, so they remain visible
without delaying publication of the current proof state.

## Acceptance boundary

The work is complete only when the focused and repository-wide checks pass, the
working tree is clean, `main` and `origin/main` point to the integrated commit,
the Pages workflow has succeeded for that commit, and the live-site checks above
pass.  A pushed commit or a queued workflow alone is not a completed deployment.
