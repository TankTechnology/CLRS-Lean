# Proof Status Board

This board is the compact planning view for CLRS-Lean's fourth-edition
formalization. Chapter status and counts come from
[`clrs-proof-progress.csv`](clrs-proof-progress.csv); section coverage comes
from [`clrs-fourth-edition-map.csv`](clrs-fourth-edition-map.csv); theorem-level
evidence lives in [`proof-map.md`](proof-map.md). This page owns priorities,
not a duplicate completion ledger.

Last evidence reconciliation: 2026-08-24.

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
| P0 | Chapter 34, §34.5 | The selected typed textbook chain is closed: bidirectional CLIQUE / VERTEX-COVER complement semantics, the total CLRS VERTEX-COVER-to-HAM-CYCLE gadget equivalence, the exact HAM-CYCLE-to-decision-TSP equivalence, and the carry-free indexed-natural 3-CNF-SAT-to-SUBSET-SUM equivalence. VERTEX-COVER additionally has total bidirectional raw semantic maps, cubic output bounds, exact bounded Boolean-certificate semantics, and a fixed polynomial-time raw well-formedness pipeline. | Treat typed textbook coverage as complete. For the stricter complexity layer, finish the VERTEX-COVER complement emitter and verifier, package its NP-completeness theorem, then add serialized languages, fixed machines, runtime bounds, and NP wrappers for HAM-CYCLE, TSP, and SUBSET-SUM. |

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
