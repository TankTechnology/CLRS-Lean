# Deferred Site Issues Design

Date: 2026-08-26

## Goal

Close the three actionable issues left by the reader-site audit without
redesigning the Verso application or changing CLRS-Lean's proof claims.

## Decisions

### Progress matrix

Verso's Literate genre rejects both Markdown tables and the Manual genre's table
directive.  The generator will therefore emit a marked, tab-delimited code
block that remains valid Literate input.  The existing one-pass HTML optimizer
will recognize only that marker and replace the block with a semantic table,
including column headers and per-cell `data-label` attributes.  At narrow
widths, only this table will reflow each row into a labeled card; other
documentation tables keep their current behavior.  This provides semantic
table markup in the deployable site and removes per-row horizontal scrolling on
mobile without patching Verso.

### Literate shards

Chapter affinity remains the default because it makes shard contents stable and
reviewable.  An affinity group whose estimated JSON bytes exceed the ideal
per-shard load is the exception: its modules become individual planning units
and can be distributed by deterministic largest-first scheduling.  This fixes
the Chapter 34 straggler without special-casing a chapter name or splitting
normal chapters.

### Search indexing

The deployable site will add one canonical URL to every HTML page and generate
`robots.txt` with an allow rule and the sitemap URL.  Existing sitemap `lastmod`
generation remains authoritative.  These changes improve the signals under the
repository's control; they do not claim to invalidate a search engine's cached
copy immediately.

## Non-goals

- No new frontend framework, page template, or navigation architecture.
- No hand-maintained release metadata.
- No chapter-specific shard rule.
- No claim that an external crawler has refreshed before it actually does.

## Verification

- Generator tests require the structured marker and reject the old fixed-width
  matrix.
- Optimizer tests require the marker to become a semantic table exactly once.
- Stylesheet tests require the Progress table-only mobile card contract.
- Planner tests reproduce an oversized affinity group, require it to split,
  preserve small affinity groups, and check deterministic balance.
- Site preparation tests require correct canonical URLs, idempotent metadata,
  and `robots.txt` pointing to `sitemap.xml`.
- The real 2,001-module plan must show materially lower estimated skew.
- The final generated Progress page is checked in desktop and mobile Chrome for
  semantics, overflow, and console errors.
