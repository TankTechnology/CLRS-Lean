# Deferred Site Issues Design

Date: 2026-08-26

## Goal

Close the three actionable issues left by the reader-site audit without
redesigning the Verso application or changing CLRS-Lean's proof claims.

## Decisions

### Progress matrix

The generated fixed-width code block will become a Markdown table.  The table
keeps the same six fields and the existing CSS table treatment.  At narrow
widths, only the Chapter Matrix table will reflow each row into a labeled card;
other documentation tables keep their current behavior.  This provides
semantic table markup on desktop and removes per-row horizontal scrolling on
mobile.

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

- Generator tests require a Markdown table and reject the old code fence.
- Stylesheet tests require the Chapter Matrix-only mobile card contract.
- Planner tests reproduce an oversized affinity group, require it to split,
  preserve small affinity groups, and check deterministic balance.
- Site preparation tests require correct canonical URLs, idempotent metadata,
  and `robots.txt` pointing to `sitemap.xml`.
- The real 2,001-module plan must show materially lower estimated skew.
- The final generated Progress page is checked in desktop and mobile Chrome for
  semantics, overflow, and console errors.

