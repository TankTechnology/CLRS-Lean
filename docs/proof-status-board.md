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
| Chapter 4, Sections 4.1-4.6, current models | Maximum-subarray correctness, Strassen 2 by 2 block algebra, substitution-method one-step bounds, recursion-tree additive expansions, exact-power Master-method cases, floor/ceiling exact-power extraction, generic all-input transfer, adjacent-power sandwich generation from one-step scale bounds, a discrete critical-power scale wrapper, and packaged floor/ceiling case 1 wrappers are proved. | The whole chapter is not finished until analytic comparison scales, remaining floor/ceiling Master-theorem cases, and selected runtime refinements are added. |
| Chapter 5, Section 5.1 | The hiring-problem probability and expected-hires harmonic/logarithmic results are proved for the finite rank-symmetry model. | Random-permutation execution model is optional refinement. |
| Chapter 6, Sections 6.1-6.5 | The array heap layer, fuelled recursive `MAX-HEAPIFY`, bottom-up `BUILD-MAX-HEAP`, in-place heapsort sorted-suffix invariant, top-level heapsort correctness, and array-level priority-queue state theorems are proved. | Line-by-line RAM cost model. |
| Chapter 7, Section 7.1 | Stable functional partition classification, scan-state partition-loop correctness, permutation preservation, and functional quicksort sortedness/permutation preservation are proved. | Mutable-array `PARTITION`, deterministic recurrence analysis, randomized quicksort, and expected-time analysis. |
| Chapter 8, Sections 8.2-8.4 | Stable counting-sort bucket/permutation correctness, abstract radix-sort ordering/permutation correctness plus complete digit-signature stability, a concrete base-`b` natural-key radix wrapper, key-order packaging, the bounded fixed-width arithmetic bridge, and deterministic bucket-sort correctness are proved. | Array count table/prefix-sum refinement and cost/probability analysis. |
| Chapter 9, Sections 9.2-9.3 | Selection-by-rank correctness is proved for the specification selector, a pivot-style quickselect model, and a pivot-parametric deterministic SELECT model, using a count-based order-statistic certificate; the local five-element median certificate and grouped split-count core are also proved. | Randomized SELECT expected time, executable grouping, final `7n/10` partition-size packaging, and runtime analysis. |
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
| Chapter 4 as a whole | The main local proof engines for maximum subarray, Strassen 2 by 2 algebra, substitution, recursion trees, exact-power Master cases, floor/ceiling exact-power extraction, all-input asymptotic transfer, adjacent-power sandwich generation, the discrete critical-power all-input wrapper, and packaged floor/ceiling case 1 wrappers exist. | Analytic comparison scales, remaining floor/ceiling Master-theorem cases, and selected runtime/cost refinements. |
| Chapter 11, Section 11.2 | Deterministic chained-hash-table insert/delete/search facts for a fixed hash function are proved. | Expected search time under a simple-uniform-hashing probability model. |
| Chapter 12, Section 12.1 | Functional BST search, minimum/maximum, successor/predecessor, insertion, deletion, and ordering preservation are proved. | Parent-pointer procedures, transplant, and imperative mutation refinement. |
| Chapter 13, Section 13.1 | Local red-black tree rotations, recoloring, red-red repair certificates, black-height, and shape facts are proved. | Full `RB-INSERT`, `RB-INSERT-FIXUP`, `RB-DELETE`, and `RB-DELETE-FIXUP`. |
| Chapter 23, Sections 23.1-23.2 | The cut property, safe-edge theorem, exact-component Kruskal scan facts, forest/spanning wrappers, and certificate-based Kruskal optimality interfaces exist. | Automatic simple path/cycle exchange extraction, fully prefix-local sorted-lightness wrapper, and Prim's theorem interface. |

## Missing Core Theorem

These items should not be counted as completed proof work.  They either have no
section file yet or only enough scaffolding to identify the intended theorem.

| Scope | Missing theorem target |
| --- | --- |
| Chapter 4 concrete Master-theorem instantiation | Extend the case 1 floor/ceiling package to analytic scales and package the remaining floor/ceiling Master-case statements. |
| Chapter 7, Sections 7.2-7.4 | Mutable-array partition refinement, deterministic performance recurrence, randomized quicksort, and expected-time theorem. |
| Chapter 9 linear-time SELECT refinements | Pivot-parametric deterministic SELECT, the local five-element median certificate, and the grouped split-count core are proved against the rank-certificate interface; randomized expected-time analysis, executable grouping, final `7n/10` partition-size packaging, and runtime proof remain. |
| Chapter 11, expected hashing analysis | Expected-time theorem for chained hashing under a formal probability model. |
| Chapter 12 pointer-level BST layer | CLRS parent-pointer search/min/max/successor/predecessor/transplant/delete refinement. |
| Chapter 13 full red-black algorithms | Full insertion/deletion fixup correctness and height theorem. |
| Chapter 14-15 and 17-22 | Not yet represented in the current Lean tree. |
| Chapter 23 Prim | Prim's algorithm theorem interface and proof have not been added yet. |
| Chapter 24 onward | Not yet represented in the current Lean tree. |

## Next Proof Plan

The next work should focus on removing central theorem gaps, not on reworking
chapters that already have their advertised main theorem.  The intended order is:

| Priority | Target | Concrete deliverable |
| --- | --- | --- |
| 1 | Chapter 4, Section 4.6 | Extend the new discrete critical-power case 1 wrappers to analytic comparison scales, then package the remaining floor/ceiling case statements. |
| 2 | Chapter 23, Sections 23.1-23.2 | Add a stable finite path/walk API, extract the concrete exchange edge automatically, connect sorted Kruskal scans to the finite-graph optimality wrapper, and add a Prim theorem interface. |
| 3 | Chapter 12 | Decide the public theorem boundary for BSTs: either finish the functional tree layer as the main theorem, or add a parent-pointer/transplant refinement as an explicit strengthening. |
| 4 | Chapter 13 | Extend the local rotation/recoloring certificate layer toward full `RB-INSERT`/`RB-DELETE` fixup correctness, keeping each fixup case separately named. |
| 5 | Chapter 7-9 refinements | Add lower-level mutable/count-array/numeric-digit refinements only after the current functional/specification-level correctness theorems stay clean. |

## Extreme-Difficulty Queue

These are the places that are likely to require concentrated proof-design work
rather than ordinary lemma filling.

| Difficulty | Scope | Why it is hard | Suggested attack |
| --- | --- | --- | --- |
| Extreme | Randomized expected-time analysis in Chapters 7, 8, 9, and 11 | We need a reusable finite probability model, expectation algebra, and asymptotic bounds over random choices, not just deterministic correctness. | First build one small probability toolkit for finite uniform choices, then prove one textbook theorem end-to-end before generalizing. |
| Extreme | Full red-black insertion/deletion fixup | The proof is a large state-machine invariant with rotations, recoloring, black-height preservation, and parent/shape constraints. | Keep the functional certificate layer, prove each fixup case as a separate theorem, then compose them only after the case lemmas stabilize. |
| High | Chapter 23 automatic MST exchange certificate | The textbook proof hides a path/cycle boundary-edge extraction argument that must be made explicit in finite graphs. | Introduce a reusable path/walk API, prove a cut-crossing boundary-edge lemma, then plug it into the existing cut-property theorem. |
| High | Chapter 4 final all-input Master theorem | The main bridge now exists, but the final theorem still needs concrete scale bounds plus careful floor/ceiling recurrence packaging. | Prove one-step bounds for `n^p`, `n^p log^k n`, and regularity-style forcing terms, then expose the three CLRS-facing cases. |
| High | Full RAM/pseudocode semantics | It would replace many current mathematical specifications with executable imperative-state refinement proofs. | Treat this as a separate project layer after the mathematical theorem interface is stable. |

## Near-Term Scheduling Rule

When choosing the next task, prefer the highest-value item in the second bucket
over repeatedly polishing a completed first-bucket section.  Chapter 6 should
now receive only audit, documentation, or RAM-cost refinement unless a concrete
gap is found.  The next proof-heavy targets are Chapter 4 concrete
comparison-scale Master-case packaging, Chapter 23 exchange-path automation,
and the remaining Chapter 8/9 algorithmic refinements.
