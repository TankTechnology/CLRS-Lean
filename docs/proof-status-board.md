# Proof Status Board

This board is the compact planning view for CLRS-Lean's fourth-edition
formalization. Chapter status and counts come from
[`clrs-proof-progress.csv`](clrs-proof-progress.csv); section coverage comes
from [`clrs-fourth-edition-map.csv`](clrs-fourth-edition-map.csv); theorem-level
evidence lives in [`proof-map.md`](proof-map.md). This page owns priorities,
not a duplicate completion ledger.

Last evidence reconciliation: 2026-08-22.

The six-phase maintenance cleanup is complete: the ledger audit is reconciled,
branch hygiene is done, and the final Pages deployment (`Build and deploy Verso
site` run #215) succeeded.

## How To Read The Board

- `proved / tracked` measures only the selected proof inventory.
- `partial` means a central theorem, section, or refinement remains explicitly
  outside the proved inventory, even when every tracked theorem compiles.
- Compatibility facades preserve third-edition imports; they are source
  bridges, not a second chapter-numbering scheme.

The generated [`CLRSLean/Progress.lean`](../CLRSLean/Progress.lean) dashboard
owns live totals and status counts.

## Highest-Priority Fourth-Edition Work

| Priority | Fourth-edition scope | Current boundary | Next acceptance target |
| --- | --- | --- | --- |
| P0 | Chapter 34, §34.5 | The §34.4 chain reaches the NP-complete honest graph-plus-`k` `CLIQUE`. VERTEX-COVER has bidirectional typed/raw complement semantics and total membership-preserving raw maps in both directions. `mem_generalVERTEXCOVER_iff_exists_certificate` also gives exact Boolean-certificate semantics with a quadratic bound. Polynomial-time machines, NP membership, and NP-completeness are not yet closed. | Implement one reusable fixed complement-map machine, reuse the CLIQUE verifier where possible, then package VERTEX-COVER NP-completeness before HAM-CYCLE → TSP and SUBSET-SUM. |

## Stable Represented Scope

All 35 fourth-edition chapters now have represented theorem content. Chapter 34
is the only row still marked `partial`; every other chapter retains the more
precise `main-proof-complete`, `main-proof-complete-for-correctness`,
`selected-section-complete`, or `expository` status recorded in the progress
ledger. These labels seal only the advertised Lean model and represented
sections. Optional pointer mutation, RAM/cache accounting, numerical error,
exercises, and chapter-end problems do not silently become coverage
requirements.

Moved and third-edition-only developments remain available through
[`clrs-online-material.csv`](clrs-online-material.csv). Canonical and online
inventories are disjoint; compatibility imports do not duplicate their counts.

## Scheduling Rule

Prefer closing the named Chapter 34 boundary over adding helper lemmas to an
already sealed chapter. Every implementation task should state its textbook
section, abstraction level, public theorem boundary, and focused verification
target before proof work begins. Update the map and progress ledger in the same
commit that changes the advertised boundary.
