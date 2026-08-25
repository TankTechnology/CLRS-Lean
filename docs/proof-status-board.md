# Proof Status Board

This board is the compact planning view for CLRS-Lean's fourth-edition
formalization. Chapter status and counts come from
[`clrs-proof-progress.csv`](clrs-proof-progress.csv); section coverage comes
from [`clrs-fourth-edition-map.csv`](clrs-fourth-edition-map.csv); theorem-level
evidence lives in [`proof-map.md`](proof-map.md). This page owns priorities,
not a duplicate completion ledger.

Last evidence reconciliation: 2026-08-25.

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
| — | Chapter 34 | The advertised Chapter 34 boundary is closed. Cook--Levin, GeneralCircuitSAT, SAT, 3-CNF-SAT, general CLIQUE, VERTEX-COVER, HAM-CYCLE, decision-TSP, and SUBSET-SUM are connected by the selected exact semantic bridges and fixed polynomial-time machines; the advertised decision problems have NP-completeness wrappers. | No Chapter 34 P0 remains. A standalone SAT verifier and direct concrete machines for the empty and universal languages are optional refinements. |

## Stable Represented Scope

All 35 fourth-edition chapters now have represented theorem content. Chapter 34
is `main-proof-complete`; every chapter retains the precise
`main-proof-complete`, `main-proof-complete-for-correctness`,
`selected-section-complete`, or `expository` status recorded in the progress
ledger. These labels seal only the advertised Lean model and represented
sections. Optional pointer mutation, RAM/cache accounting, numerical error,
exercises, and chapter-end problems do not silently become coverage
requirements.

Moved and third-edition-only developments remain available through
[`clrs-online-material.csv`](clrs-online-material.csv). Canonical and online
inventories are disjoint; compatibility imports do not duplicate their counts.

## Scheduling Rule

Chapter 34 no longer has a priority exception. Every implementation task should state its textbook
section, abstraction level, public theorem boundary, and focused verification
target before proof work begins. Update the map and progress ledger in the same
commit that changes the advertised boundary.
