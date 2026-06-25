# Proof Status Board

This board is the high-level answer to a practical maintainer question:
which parts of CLRS-Lean should we treat as main-proof complete, which parts
have a good Lean structure but still need a central theorem, and which parts
are missing the core theorem interface.

The detailed theorem-by-theorem ledger remains in
[`proof-map.md`](proof-map.md).  This page is intentionally coarser so future
work does not drift back to the same chapter without a clear reason.

## Main Proof Completed

These chapters or selected sections have compiler-clean Lean theorems for the
current public model.  They may still have refinement work, such as RAM costs or
pointer-level execution semantics, but the main mathematical theorem currently
advertised on the site is proved.

| Scope | Why it is in this bucket | Remaining refinement |
| --- | --- | --- |
| Chapter 2, Sections 2.1-2.3 | Insertion sort sortedness/permutation, insertion-sort quadratic comparison bound, merge-sort sortedness/permutation, and the power-of-two merge-sort recurrence are proved. | Full RAM semantics and arbitrary-size floor/ceiling merge-sort recurrence. |
| Chapter 3, Section 3.1 | CLRS-facing asymptotic notation wrappers and basic algebraic facts are proved. | Extend the standard-function table in Section 3.2. |
| Chapter 4, Sections 4.1-4.5, current models | Maximum-subarray correctness, Strassen 2 by 2 block algebra, substitution-method one-step bounds, recursion-tree additive expansions, and exact-power Master-method cases are proved. | The whole chapter is not finished until all-input Master-theorem bridging and selected runtime refinements are added. |
| Chapter 5, Section 5.1 | The hiring-problem probability and expected-hires harmonic/logarithmic results are proved for the finite rank-symmetry model. | Random-permutation execution model is optional refinement. |
| Chapter 6, Sections 6.1-6.5 | The array heap layer, fuelled recursive `MAX-HEAPIFY`, bottom-up `BUILD-MAX-HEAP`, in-place heapsort sorted-suffix invariant, top-level heapsort correctness, and array-level priority-queue state theorems are proved. | Line-by-line RAM cost model. |
| Chapter 7, Section 7.1 | Stable functional partition correctness and functional quicksort sortedness/permutation preservation are proved. | In-place `PARTITION`, deterministic recurrence analysis, randomized quicksort, and expected-time analysis. |
| Chapter 8, Sections 8.2-8.3 | Stable counting-sort bucket correctness and abstract radix-sort correctness from stable digit passes are proved. | Array count table/prefix-sum refinement, concrete base-`b` digit extraction, bucket sort, and cost/probability analysis. |
| Chapter 10, Sections 10.1-10.2 | Functional stack/queue and functional linked-list operation specifications are proved. | Pointer-level memory, sentinels, allocation, and free lists. |
| Chapter 11, Section 11.1 | Direct-address table insert/search/delete behavior is proved. | Bounded-array and cost refinement. |
| Chapter 16, Sections 16.1 and 16.3 | Activity selection has a recursive greedy optimality theorem, and Huffman V2 has frequency-table optimality and minimum-cost wrappers. | Additional Chapter 16 topics can reuse the exchange/certificate pattern. |

## Structured But Not Complete

These areas already have a meaningful Lean model and useful proved lemmas, but
the chapter or section should still be considered partial because an important
CLRS theorem is not yet internalized.

| Scope | What exists | Core gap |
| --- | --- | --- |
| Chapter 3, Section 3.2 | Many polynomial, logarithmic, exponential, harmonic, floor/ceiling, and factorial asymptotic facts are proved through CLRS-facing names. | Complete the standard-function comparison table and add missing variants. |
| Chapter 4 as a whole | The main local proof engines for maximum subarray, Strassen 2 by 2 algebra, substitution, recursion trees, and exact-power Master cases exist. | All-input Master theorem and selected runtime/cost refinements. |
| Chapter 11, Section 11.2 | Deterministic chained-hash-table insert/delete/search facts for a fixed hash function are proved. | Expected search time under a simple-uniform-hashing probability model. |
| Chapter 12, Section 12.1 | Functional BST search, minimum/maximum, successor/predecessor, insertion, deletion, and ordering preservation are proved. | Parent-pointer procedures, transplant, and imperative mutation refinement. |
| Chapter 13, Section 13.1 | Local red-black tree rotations, recoloring, red-red repair certificates, black-height, and shape facts are proved. | Full `RB-INSERT`, `RB-INSERT-FIXUP`, `RB-DELETE`, and `RB-DELETE-FIXUP`. |
| Chapter 23, Sections 23.1-23.2 | The cut property, safe-edge theorem, exact-component Kruskal scan facts, forest/spanning wrappers, and certificate-based Kruskal optimality interfaces exist. | Automatic simple path/cycle exchange extraction, fully prefix-local sorted-lightness wrapper, and Prim's theorem interface. |

## Missing Core Theorem

These items should not be counted as completed proof work.  They either have no
section file yet or only enough scaffolding to identify the intended theorem.

| Scope | Missing theorem target |
| --- | --- |
| Chapter 4, Section 4.6 | Full proof of the Master Theorem over all natural input sizes. |
| Chapter 7, Sections 7.2-7.4 | In-place partition, deterministic performance recurrence, randomized quicksort, and expected-time theorem. |
| Chapter 8, Section 8.4 | Bucket sort theorem interface and proof have not been added yet. |
| Chapter 9 | Linear-time selection and order-statistics algorithms are not yet represented in the current Lean tree. |
| Chapter 11, expected hashing analysis | Expected-time theorem for chained hashing under a formal probability model. |
| Chapter 12 pointer-level BST layer | CLRS parent-pointer search/min/max/successor/predecessor/transplant/delete refinement. |
| Chapter 13 full red-black algorithms | Full insertion/deletion fixup correctness and height theorem. |
| Chapter 14-15 and 17-22 | Not yet represented in the current Lean tree. |
| Chapter 23 Prim | Prim's algorithm theorem interface and proof have not been added yet. |
| Chapter 24 onward | Not yet represented in the current Lean tree. |

## Near-Term Scheduling Rule

When choosing the next task, prefer the highest-value item in the second bucket
over repeatedly polishing a completed first-bucket section.  Chapter 6 should
now receive only audit, documentation, or RAM-cost refinement unless a concrete
gap is found.  The next proof-heavy targets are Chapter 9 selection
correctness, Chapter 4 all-input recurrence bridging, and Chapter 23
exchange-path automation.
