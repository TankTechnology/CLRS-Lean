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
| Chapter 4, Sections 4.1-4.6, current models | Maximum-subarray correctness, Strassen 2 by 2 block algebra, substitution-method one-step bounds, recursion-tree additive expansions, exact-power Master-method cases, floor/ceiling exact-power extraction, generic all-input transfer, adjacent-power sandwich generation from one-step scale bounds, discrete critical-power/log-critical/tail-dominated scale wrappers, packaged floor/ceiling Master cases 1/2/3, and natural-exponent polynomial wrappers for Master cases 1/2 are proved. | The whole chapter is not finished until the general `n^(log_b a)`, real-log, case-3 comparison scales, and selected runtime refinements are added. |
| Chapter 5, Section 5.1 | The hiring-problem probability and expected-hires harmonic/logarithmic results are proved for the finite rank-symmetry model. | Random-permutation execution model is optional refinement. |
| Chapter 6, Sections 6.1-6.5 | The array heap layer, fuelled recursive `MAX-HEAPIFY`, bottom-up `BUILD-MAX-HEAP`, in-place heapsort sorted-suffix invariant, top-level heapsort correctness, and array-level priority-queue state theorems are proved. | Line-by-line RAM cost model. |
| Chapter 7, Sections 7.1-7.3 | Stable functional partition classification, scan-state partition-loop correctness, returned pivot-index partition postconditions, adjacent-swap trace, permutation preservation, functional quicksort sortedness/permutation preservation, deterministic quadratic comparison-count bounds, and the expected-comparison recurrence with harmonic bounds are proved. | Index-level mutable-array `PARTITION`, explicit pivot probability space, sharp `n log n` tail/lower-bound packaging. |
| Chapter 8, Sections 8.2-8.4 | Stable counting-sort bucket/permutation correctness, abstract radix-sort ordering/permutation correctness plus complete digit-signature stability, a concrete base-`b` natural-key radix wrapper, key-order packaging, the bounded fixed-width arithmetic bridge, and deterministic bucket-sort correctness are proved. | Array count table/prefix-sum refinement and cost/probability analysis. |
| Chapter 9, Sections 9.2-9.3 | Selection-by-rank correctness is proved for the specification selector, a pivot-style quickselect model, a pivot-parametric deterministic SELECT model, and an executable median-of-medians SELECT wrapper, using a count-based order-statistic certificate; the local five-element median certificate, executable grouping, full-input split-count core, `7n/10 + O(1)` partition-size wrapper, and abstract linear recurrence theorem are also proved. | Randomized SELECT expected time and concrete executable cost theorem. |
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
| Chapter 4 as a whole | The main local proof engines for maximum subarray, Strassen 2 by 2 algebra, substitution, recursion trees, exact-power Master cases, floor/ceiling exact-power extraction, all-input asymptotic transfer, adjacent-power sandwich generation, the discrete critical-power/log-critical/tail-dominated all-input wrappers, packaged floor/ceiling Master cases 1/2/3, and natural-exponent polynomial/log-polynomial wrappers for cases 1/2 exist. | General `n^(log_b a)`, real-log, and case-3 comparison scales plus selected runtime/cost refinements. |
| Chapter 11, Section 11.2 | Deterministic chained-hash-table insert/delete/search facts for a fixed hash function are proved, and the finite-uniform bucket interface proves expected chain length equals load factor. | Lift the finite-uniform bucket abstraction to a random key or random hash-function model with independence assumptions. |
| Chapter 12, Section 12.1 | Functional BST search, minimum/maximum, insertion, complete successor/predecessor `some`/`none` specifications, deletion membership wrappers, missing-key deletion identity, search-after-delete, and ordering preservation are proved. | Parent-pointer procedures, transplant, and imperative mutation refinement. |
| Chapter 13, Section 13.1 | Local red-black tree rotations, recoloring, red-red repair certificates, black-height, shape facts, and four local insertion-fixup case certificates are proved. | Compose the local cases into full `RB-INSERT`/`RB-INSERT-FIXUP`; then prove `RB-DELETE`, `RB-DELETE-FIXUP`, and height. |
| Chapter 14, Section 14.1 | Order-statistic tree size augmentation, size-field recomputation, key preservation, size-preserving local rotations, and augmented rank selection are proved for a functional tree. | Connect the functional rotations to red-black balancing, plus interval trees and the general augmentation theorem. |
| Chapter 15, Sections 15.1, 15.2, and 15.4 | Rod-cutting Bellman recurrence facts, matrix-chain parenthesization optimality plus split-table reconstruction certificates, and LCS certificate optimality plus table-recurrence reconstruction certificates are proved. | Bottom-up/memoized implementations, executable reconstruction algorithms, and optimal BST. |
| Chapter 23, Sections 23.1-23.2 | The cut property, safe-edge theorem, exact-component Kruskal scan facts, forest/spanning wrappers, and certificate-based Kruskal optimality interfaces exist. | Automatic simple path/cycle exchange extraction, fully prefix-local sorted-lightness wrapper, and Prim's theorem interface. |

## Missing Core Theorem

These items should not be counted as completed proof work.  They either have no
section file yet or only enough scaffolding to identify the intended theorem.

| Scope | Missing theorem target |
| --- | --- |
| Chapter 4 concrete Master-theorem instantiation | Extend the proved natural-exponent case-1/2 wrappers to the general `n^(log_b a)`, real-log, and case-3 comparison-scale statements. |
| Chapter 7 remaining quicksort refinements | Index-level mutable-array partition refinement, explicit probability-space interpretation for random pivots, and sharp `n log n` tail/lower-bound packaging. |
| Chapter 9 remaining SELECT refinements | Pivot-parametric deterministic SELECT, executable median-of-medians SELECT, the local five-element median certificate, executable grouping, the full-input split-count core, the `7n/10 + O(1)` partition-size wrapper, and the abstract linear recurrence theorem are proved; randomized expected-time analysis and concrete executable runtime proof remain. |
| Chapter 11, expected hashing analysis | Extend the finite-uniform bucket theorem to chained hashing under a formal random key or random hash-function model. |
| Chapter 12 pointer-level BST layer | CLRS parent-pointer search/min/max/successor/predecessor/transplant/delete refinement. |
| Chapter 13 full red-black algorithms | Compose the local insertion-fixup cases into executable insertion; then prove deletion fixup correctness and the height theorem. |
| Chapter 14 remaining augmentation targets | Connect size-preserving rotations to red-black balancing; add interval trees and the general augmentation theorem. |
| Chapter 15 remaining dynamic-programming targets | Bottom-up/memoized rod cutting, executable matrix-chain and LCS table/reconstruction algorithms, and optimal binary search trees. |
| Chapter 21-22 | Not yet represented in the current Lean tree. |
| Chapter 17 Amortized Analysis | First-pass acceptance standard is fixed: generic aggregate/accounting/potential theorems plus `MULTIPOP`, binary counter, and dynamic-table examples. No Lean module exists yet. |
| Chapter 18 B-Trees | First-pass acceptance standard is fixed: B-tree invariant, height theorem, search correctness, split-child correctness, and insertion correctness. No Lean module exists yet. |
| Chapter 19 Fibonacci Heaps | First-pass acceptance standard is fixed: abstract operation correctness, potential-method amortized bounds, and logarithmic degree bound. No Lean module exists yet. |
| Chapter 20 van Emde Boas Trees | First-pass acceptance standard is fixed: universe decomposition, representation invariant, operation correctness, and `O(log log u)` recurrence wrapper. No Lean module exists yet. |
| Chapter 23 Prim | Prim's algorithm theorem interface and proof have not been added yet. |
| Chapter 24 onward | Not yet represented in the current Lean tree. |

## Next Proof Plan

The next work should focus on removing central theorem gaps, not on reworking
chapters that already have their advertised main theorem.  The intended order is:

| Priority | Target | Concrete deliverable |
| --- | --- | --- |
| 1 | Chapter 4, Section 4.6 | Extend the natural-exponent polynomial wrappers to the general `n^(log_b a)`, real-log, and case-3 comparison-scale statements. |
| 2 | Chapter 23, Sections 23.1-23.2 | Add a stable finite path/walk API, extract the concrete exchange edge automatically, connect sorted Kruskal scans to the finite-graph optimality wrapper, and add a Prim theorem interface. |
| 3 | Chapter 12 pointer refinement | Treat the functional tree layer as the current main theorem boundary; add parent-pointer/transplant refinement only as an explicit strengthening layer. |
| 4 | Chapter 13 | Compose the named local `RB-INSERT-FIXUP` cases into an executable insertion/fixup layer, then tackle deletion fixup. |
| 5 | Chapter 7-9 refinements | Add lower-level mutable/count-array/numeric-digit refinements only after the current functional/specification-level correctness theorems stay clean. |

## Extreme-Difficulty Queue

These are the places that are likely to require concentrated proof-design work
rather than ordinary lemma filling.

| Difficulty | Scope | Why it is hard | Suggested attack |
| --- | --- | --- | --- |
| Extreme | Randomized expected-time analysis in Chapters 7, 8, 9, and 11 | We need a reusable finite probability model, expectation algebra, and asymptotic bounds over random choices, not just deterministic correctness.  Chapter 11 now has the first finite-uniform bucket theorem, but not yet the full random key/hash-function model. | Generalize the Chapter 11 finite-uniform average layer into a reusable probability toolkit, then use it for one randomized theorem end-to-end before broadening. |
| Extreme | Full red-black insertion/deletion fixup | The proof is a large state-machine invariant with rotations, recoloring, black-height preservation, and parent/shape constraints. | Keep the functional certificate layer, prove each fixup case as a separate theorem, then compose them only after the case lemmas stabilize. |
| High | Chapter 23 automatic MST exchange certificate | The textbook proof hides a path/cycle boundary-edge extraction argument that must be made explicit in finite graphs. | Introduce a reusable path/walk API, prove a cut-crossing boundary-edge lemma, then plug it into the existing cut-property theorem. |
| High | Chapter 4 final all-input Master theorem | The main bridge and natural-exponent case-1/2 polynomial wrappers now exist, but the final theorem still needs general real-exponent and case-3 comparison scales. | Prove the `n^(log_b a)` comparison, connect discrete log to real log, then expose the remaining CLRS-facing cases. |
| High | Full RAM/pseudocode semantics | It would replace many current mathematical specifications with executable imperative-state refinement proofs. | Treat this as a separate project layer after the mathematical theorem interface is stable. |

## Near-Term Scheduling Rule

When choosing the next task, prefer the highest-value item in the second bucket
over repeatedly polishing a completed first-bucket section.  Chapter 6 should
now receive only audit, documentation, or RAM-cost refinement unless a concrete
gap is found.  The next proof-heavy targets are Chapter 4 general
comparison-scale Master-case packaging, Chapter 23 exchange-path automation,
and the remaining Chapter 8/9 algorithmic refinements.
