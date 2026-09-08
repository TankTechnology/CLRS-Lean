# CLRS-Lean milestone announcement draft

This draft describes the selected proof-library milestone and the September 8
chapter repairs. The [repair record](../plans/2026-09-08-chapter-repairs/index.md)
owns current verification and integration status; the
[original audit](../audits/2026-09-08-chapter-review/index.md) remains historical
evidence for its base commit. This draft does not assert a published post or a
deployed website.

## Recommended short post

CLRS-Lean has reached a milestone: selected core formalizations for CLRS (4th
ed.), with 35 chapter guides and 1,689 tracked proof entries in Lean 4. We also
completed the chapter-by-chapter repair pass, connecting more executable
algorithms to correctness and cost proofs.

Explore, reuse, and contribute:
[CLRS-Lean](https://tanktechnology.github.io/CLRS-Lean/)

## Optional follow-up

“Complete” refers to the selected proof inventory and this repair scope. It does
not mean that every theorem, exercise, or low-level implementation in the book
has been formalized. Each chapter publishes its model, cost unit, and premises;
the repair record includes builds, regressions, and axiom-dependency checks. The
textbook has not been checked independently page by page.

[Formalization scope](https://github.com/TankTechnology/CLRS-Lean/blob/main/docs/scope.md) ·
[Repair record](https://github.com/TankTechnology/CLRS-Lean/blob/main/docs/plans/2026-09-08-chapter-repairs/index.md) ·
[GitHub](https://github.com/TankTechnology/CLRS-Lean)

## Short English post

CLRS-Lean milestone: selected core formalizations for CLRS (4th ed.), with 35
chapter guides and 1,689 tracked proof entries in Lean 4. This chapter-repair
round connects more algorithms to their correctness and counted execution,
with explicit model boundaries. Explore the library:
https://tanktechnology.github.io/CLRS-Lean/

## Evidence and claim boundary

| Claim | Evidence |
| --- | --- |
| 35 chapter guides; Chapter 1 expository | [Canonical chapter ledger](../clrs-proof-progress.csv) |
| 1,689 selected entries recorded as proved | Tracked/proved ledger totals; helpers added during repairs do not inflate this inventory |
| 137 mapped section entries | [Edition map](../clrs-fourth-edition-map.csv) and structural checker |
| Chapter repairs and verification | [Repair record](../plans/2026-09-08-chapter-repairs/index.md) |
| Scope is not every textbook statement or implementation | [Scope](../scope.md); exact-real, charged-operation and representation boundaries in chapter guides |

The original audit's defects are addressed by later code and proof changes,
with explicit scope corrections where the issue allowed them. Neither the
ledger label nor a successful build alone establishes whole-book semantic
fidelity. The textbook correspondence remains NOT-INDEPENDENTLY-VERIFIED.

## Release validation

PR #377 is merged as rewritten commit `1a62e356`. On that merged checkout, the library build
passed 10,768 jobs, the repository checks and all 35 chapter trust surfaces
passed, and the GitHub Pages-equivalent four-shard pipeline built 2,188 modules
into 2,190 optimized HTML pages and sitemap URLs. Raw-page weight, source
freshness and final rendering checks passed.

The optimized `_site` was served locally and inspected with Chromium. The
homepage, all 35 fourth-edition chapter links, Chapter 35 and the progress page
loaded successfully; the fourth-edition chapter index remained fully visible
with JavaScript disabled, while third-edition compatibility chapters remained
outside default navigation. Desktop and 390px mobile pages had no horizontal
overflow, browser console errors or page exceptions. Desktop/mobile homepage
and Chapter 35 screenshots were visually checked.

Before describing the public website as updated, dispatch the manual GitHub
Pages workflow from `main`, wait for its deployment environment to succeed,
then repeat the public URL smoke checks from the
[site build and preview runbook](../site-architecture.md#local-preview).

No tweet has been posted and no website deployment is recorded by this work.
