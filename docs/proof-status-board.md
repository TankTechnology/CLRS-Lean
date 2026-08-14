# Proof Status Board

This board is the compact planning view for CLRS-Lean's fourth-edition
formalization. Chapter status and counts come from
[`clrs-proof-progress.csv`](clrs-proof-progress.csv); section coverage comes
from [`clrs-fourth-edition-map.csv`](clrs-fourth-edition-map.csv); theorem-level
evidence lives in [`proof-map.md`](proof-map.md). This page owns priorities,
not a duplicate completion ledger.

Last evidence reconciliation: 2026-08-14.

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
| P0 | Chapter 34, NP-Completeness | The three represented §34.4 machine reductions compile. Cook--Levin has a well-formed whole-tableau circuit, exact satisfiability semantics, polynomial gate/input/encoding bounds, an exact function-level map, and finite `GeneralCircuitSAT` certificate semantics. It does not yet have concrete polynomial-time generator/checker TM2s or the final NP-completeness wrappers. | Prove the all-input polynomial runtime of the GeneralCircuit certificate checker, then implement the concrete Cook--Levin generator TM2 and assemble the `GeneralCircuitSAT` NP and NP-hardness wrappers. |
| P1 | Chapter 34, general CLIQUE and §34.5 | The current CLIQUE target is the specialized occurrence graph generated from 3-CNF. General graph-plus-`k` CLIQUE and the §34.5 reduction chain are not represented. | Add the general CLIQUE semantic/encoding layer, then formalize the selected §34.5 textbook reductions without treating open complexity questions as proof obligations. |

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
