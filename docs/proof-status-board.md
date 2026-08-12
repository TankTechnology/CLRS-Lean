# Proof Status Board

This board is the compact planning view for CLRS-Lean's fourth-edition
migration. Chapter status and counts come from
[`clrs-proof-progress.csv`](clrs-proof-progress.csv); section coverage comes
from [`clrs-fourth-edition-map.csv`](clrs-fourth-edition-map.csv); theorem-level
evidence lives in [`proof-map.md`](proof-map.md). This page owns priorities,
not a duplicate completion ledger.

Last evidence reconciliation: 2026-08-06.

## How To Read The Board

- `proved / tracked` measures only the selected proof inventory.
- `partial` means the fourth-edition map names at least one unresolved central
  section obligation, even when every selected theorem is proved.
- One edition-gap unit is one unresolved section in a represented chapter. A
  wholly unrepresented chapter contributes one aggregate whole-chapter unit.
- Compatibility facades preserve third-edition imports; they are migration
  evidence, not a second chapter-numbering scheme.

The generated [`CLRSLean/Progress.lean`](../CLRSLean/Progress.lean) dashboard
owns the live totals and status counts.

## Highest-Priority Fourth-Edition Work

| Priority | Fourth-edition scope | Current boundary | Next acceptance target |
| --- | --- | --- | --- |
| P0 | Chapter 25, Matchings in Bipartite Graphs | No canonical theorem-bearing source | Define the chapter inventory and formalize a native matching interface rather than treating max-flow matching as chapter coverage |
| P0 | Chapter 27, Online Algorithms | No canonical theorem-bearing source | Define the online model and select the first textbook algorithm/theorem boundary |
| P0 | Chapter 33, Machine-Learning Algorithms | No canonical theorem-bearing source | Define the chapter inventory and a first mathematically auditable learning-algorithm boundary |
| P0 | Chapters 34–35, NP-Completeness and Approximation Algorithms | Guide-only | Establish theorem inventories and native fourth-edition modules |
| P1 | Chapter 14, Dynamic Programming | Worked recurrences and optimality results exist, but all five sections remain partial | Add tabulated/memoized algorithm interfaces, reconstruction contracts, and stated costs; include a generic §14.3 interface |
| P1 | Chapter 13, Red-Black Trees | Functional shape and membership results exist | Combine red-black shape with BST/inorder preservation and textbook update/cost refinements for §§13.2–13.4 |
| P1 | Chapter 17, Augmenting Data Structures | Order-statistic, generic augmentation, and interval components exist in separate layers | Prove OS-RANK and logarithmic costs, the augmentation update bound, and a dynamic interval-tree bridge |
| P1 | Chapter 29, Linear Programming | Selected formulation and duality groups are proved | Add general-form normalization, finite `StandardLP` encoding bridges, and canonical declaration ownership |
| P1 | Chapter 32, String Matching | §32.1 and the naive matcher are represented | Formalize Rabin–Karp, finite automata, KMP, and suffix arrays (§§32.2–32.5) |
| P2 | Chapter 3, Characterizing Running Times | §§3.1 and 3.3 are represented; §3.2 has most asymptotic infrastructure | Add a shared-threshold two-sided Θ witness and the expected o/ω algebra/duality wrappers |

## Other Named Coverage Gaps

| Chapter | Remaining fourth-edition boundary |
| --- | --- |
| 4, Divide-and-Conquer | §§4.1 and 4.6 are partial; §4.7 Akra–Bazzi is not started |
| 7, Quicksort | §7.4 analysis remains partial |
| 10, Elementary Data Structures | §10.1 remains partial |
| 11, Hash Tables | §11.5 practical considerations is not started; perfect hashing remains online material |
| 15, Greedy Algorithms | §15.4 offline caching is not started; moved matroid/task-scheduling material remains online |

## Stable Represented Scope

All other represented chapters retain the more precise
`main-proof-complete`, `main-proof-complete-for-correctness`,
`selected-section-complete`, or `expository` status recorded in the progress
ledger. These labels seal only the advertised Lean model and represented
fourth-edition sections. Optional pointer mutation, mutable-array refinement,
RAM/cache accounting, numerical error, exercises, and chapter-end problems do
not silently become coverage requirements.

Moved and third-edition-only developments remain available through
[`clrs-online-material.csv`](clrs-online-material.csv). Canonical and online
inventories are disjoint; compatibility imports do not duplicate their counts.

## Scheduling Rule

Prefer closing a named edition-map obligation over adding helper lemmas to an
already sealed model. Every implementation task should state its fourth-edition
section, abstraction level, public theorem boundary, and focused verification
target before proof work begins. Update the map and progress ledger in the same
commit that changes the advertised boundary.
