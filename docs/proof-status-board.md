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
| Chapter 4, Sections 4.1-4.6, current models | Maximum-subarray correctness, Strassen 2 by 2 block algebra, substitution-method one-step bounds, recursion-tree additive expansions, exact-power Master-method cases, floor/ceiling exact-power extraction, generic all-input transfer, adjacent-power sandwich generation from one-step scale bounds, discrete critical-power/log-critical/tail-dominated scale wrappers, packaged floor/ceiling Master cases 1/2/3, natural-exponent polynomial wrappers for Master cases 1/2, the real-log bridge from `a^(⌊log_b n⌋)` to `n^(log_b a)`, named case-1 real-log wrappers, the real-log-log bridge from `(⌊log_b n⌋+1)a^(⌊log_b n⌋)` to `n^(log_b a) log n`, and named case-2 real-log-log wrappers are proved. | The whole chapter is not finished until the case-3 comparison scale and selected runtime refinements are added. |
| Chapter 5, Section 5.1 | The hiring-problem probability and expected-hires harmonic/logarithmic results are proved for the finite rank-symmetry model. | Random-permutation execution model is optional refinement. |
| Chapter 6, Sections 6.1-6.5 | The array heap layer, fuelled recursive `MAX-HEAPIFY`, bottom-up `BUILD-MAX-HEAP`, in-place heapsort sorted-suffix invariant, top-level heapsort correctness, and array-level priority-queue state theorems are proved. | Line-by-line RAM cost model. |
| Chapter 7, Sections 7.1-7.3 | Stable functional partition classification, scan-state partition-loop correctness, returned pivot-index partition postconditions, adjacent-swap trace, permutation preservation, functional quicksort sortedness/permutation preservation, deterministic quadratic comparison-count bounds, and the expected-comparison recurrence with named closed form and harmonic bounds are proved. | Index-level mutable-array `PARTITION`, explicit pivot probability space, sharp `n log n` tail/lower-bound packaging. |
| Chapter 8, Sections 8.2-8.4 | Stable counting-sort bucket/permutation correctness, count-table lengths, cumulative boundaries, per-key reverse-scan refinement, abstract radix-sort ordering/permutation correctness plus complete digit-signature stability, a concrete base-`b` natural-key radix wrapper, key-order packaging, the bounded fixed-width arithmetic bridge, deterministic bucket-sort correctness, and the finite-uniform bucket-sort collision/second-moment core plus abstract `≤ 3n` expected-cost wrapper are proved. | Single mutable output-array refinement; full bucket-sort expected-time theorem over an explicit independent input distribution and concrete cost model. |
| Chapter 9, Sections 9.2-9.3 | Selection-by-rank correctness is proved for the specification selector, a pivot-style quickselect model, a pivot-parametric deterministic SELECT model, and an executable median-of-medians SELECT wrapper, using a count-based order-statistic certificate; the local five-element median certificate, executable grouping, full-input split-count core, `7n/10 + O(1)` partition-size wrapper, abstract linear recurrence theorem, and CLRS-facing SELECT recurrence wrapper are also proved. | Randomized SELECT expected time and concrete executable cost theorem. |
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
| Chapter 4 as a whole | The main local proof engines for maximum subarray, Strassen 2 by 2 algebra, substitution, recursion trees, exact-power Master cases, floor/ceiling exact-power extraction, all-input asymptotic transfer, adjacent-power sandwich generation, the discrete critical-power/log-critical/tail-dominated all-input wrappers, packaged floor/ceiling Master cases 1/2/3, natural-exponent polynomial/log-polynomial wrappers for cases 1/2, the real-log bridge and named wrappers for case 1, and the real-log-log bridge and named wrappers for case 2 exist. | Case-3 comparison scale and selected runtime/cost refinements. |
| Chapter 11, Section 11.2 | Deterministic chained-hash-table insert/delete/search facts for a fixed hash function are proved, and the finite-uniform bucket toolkit proves average additivity, nonnegativity, load-factor equality, and single-insert expected-cost changes. | Lift the finite-uniform bucket abstraction to a random key or random hash-function model with independence assumptions. |
| Chapter 12, Section 12.1 | Functional BST search, minimum/maximum, insertion, complete successor/predecessor `some`/`none` specifications, successor/predecessor existence wrappers, insertion/search and deletion/search wrappers, successor/predecessor-after-delete wrappers, deletion membership wrappers, missing-key deletion identity, and ordering preservation are proved. | Parent-pointer procedures, transplant, and imperative mutation refinement. |
| Chapter 13, Section 13.1 | Local red-black tree rotations, recoloring, red-red repair certificates, black-height, shape facts, four local insertion-fixup case certificates, and the executable Okasaki-style `RBTree.insert` are proved, with membership, red-black shape, and black-height theorems. | Prove `RB-DELETE`, `RB-DELETE-FIXUP`, and the logarithmic-height theorem. |
| Chapter 14, Section 14.1 | Order-statistic tree size augmentation, size-field recomputation, key preservation, size/rank-preserving local rotations, cached-root-size preservation, augmented rank selection, and recompute-then-rotate selector preservation are proved for a functional tree. | Connect the functional rotations to red-black balancing, plus interval trees and the general augmentation theorem. |
| Chapter 15, Sections 15.1, 15.2, 15.4, and 15.5 | Rod-cutting Bellman recurrence facts, finite bottom-up table-prefix correctness, and an executable recurrence-valued rod-cutting function are proved; matrix-chain parenthesization optimality plus split-table reconstruction certificates and reconstructed-plan cost equality, LCS certificate optimality plus table-recurrence reconstruction certificates/wrappers including matching/nonmatching recurrence consequences, and optimal-BST plan optimality plus an executable recurrence-valued OBST function are also proved. | Mutable-array/memoized rod cutting and executable matrix-chain, LCS, and OBST reconstruction algorithms. |
| Chapter 17, Sections 17.1-17.4 | Finite-prefix aggregate/accounting/potential theorems, `MULTIPOP`, executable binary-counter one-step and multi-step trace bounds, and size-level dynamic-table potential nonnegativity plus insertion/deletion cost and capacity-choice case specs, exact zero/positive deletion-cost wrappers, premise-light deletion-cost branch wrappers, positive-cost lower bounds, cost upper bounds, capacity feasibility/direction facts, post-state field equations, post-state allocation-size case specs, stored-count direction facts, positive insertion/deletion count/capacity wrappers, post-state capacity corollaries, post-transition potential nonnegativity, concrete amortized-cost unfolding, resize-branch capacity wrappers, and transition wrappers are proved. | Mutable-array copying, allocator/RAM cost semantics, and sharper load-factor potential refinements. |
| Chapter 18, Sections 18.1-18.3 | A mathematical B-tree model, search correctness, direct base search success/failure wrappers, minimum-key height expression base/positivity facts plus recurrence and monotonicity, split-child preservation plus direct validity, membership/search preservation, direct split old-key corollaries, insertion/deletion membership theorems, Prop-level deletion membership/search success and direct wrappers, direct insertion/deletion validity short-name wrappers, equality-key update-query wrappers, successful and unsuccessful search-after-update specs, membership-driven search-after-update wrappers, and direct inserted/deleted-key, old-key query preservation, old failed-search preservation, failed membership corollaries, and direct failed-membership preservation wrappers are proved. | Full separator/same-depth invariant stack, node-level deletion repair, disk-page and mutation refinement. |
| Chapter 19, Section 19.1 | Abstract Fibonacci-heap finite-set operations, make-heap/minimum/extract/decrease/delete specs including empty minimum/extract-min cases, direct minimum/extract-min empty-result and nonempty-result wrappers, direct minimum membership/lower-bound wrappers, insert/union/extract-min-remaining/decrease-key/delete minimum direct membership/lower-bound wrappers, remaining/delete minimum nonempty-result wrappers, direct operation-result validity wrappers, direct insert/union/extract-min/decrease-key/delete membership facts, operation-key, replaced-key query, old-key preservation, failed membership corollaries, and direct failed-membership preservation wrappers, returned minimum-after-update positive and empty-result specs, heap potential zero/nonnegativity and telescoping facts, Fibonacci lower-bound recurrence/positivity/monotonicity and even/half-index power-of-two growth facts, conditional degree-to-log wrappers, and conservative degree budget are proved. | Pointer forest, handles, cascading cuts, consolidation arrays, subtree-size induction, and true Fibonacci logarithmic degree theorem. |
| Chapter 20, Sections 20.1-20.2 | vEB high/low/index arithmetic, bounded recomposition facts, and finite-set specs for member/min/max/successor/predecessor, including successful-query universe bounds, empty extrema/successor/predecessor cases, plus insert/delete, membership/extrema/neighbor-query-after-update positive and no-neighbor specs, extrema empty-after-update specs, direct extrema empty-result wrappers, direct base extrema/neighbor nonempty-result wrappers, direct updated-neighbor nonempty-result wrappers, direct deletion-extrema nonempty-result wrappers, direct extrema membership/lower- and upper-bound wrappers, direct insertion-query old-key membership wrappers, direct extrema-after-update membership/order wrappers, direct base/insert/delete neighbor membership/order wrappers, direct updated-key, old-key preservation, failed member-query corollaries, direct failed member-query preservation wrappers, direct no-neighbor query wrappers, premise-light no-neighbor wrappers over old represented sets, update-query universe-bound corollaries, and operation-depth recurrence/monotonicity wrappers are proved. | Recursive summary/cluster representation, word-RAM base cases, and `O(log log u)` asymptotic bridge. |
| Chapter 23, Sections 23.1-23.2 | The cut property, safe-edge theorem, exact-component Kruskal scan facts, forest/spanning wrappers, and certificate-based Kruskal optimality interfaces exist. | Automatic simple path/cycle exchange extraction, fully prefix-local sorted-lightness wrapper, and Prim's theorem interface. |

## Missing Core Theorem

These items should not be counted as completed proof work.  They either have no
section file yet, only enough scaffolding to identify the intended theorem, or
a meaningful model that still lacks the next textbook-level refinement.

| Scope | Missing theorem target |
| --- | --- |
| Chapter 4 concrete Master-theorem instantiation | Add the case-3 comparison-scale statement. |
| Chapter 7 remaining quicksort refinements | Index-level mutable-array partition refinement, explicit probability-space interpretation for random pivots, and sharp `n log n` tail/lower-bound packaging. |
| Chapter 9 randomized SELECT and executable cost | Pivot-parametric deterministic SELECT, executable median-of-medians SELECT, the local five-element median certificate, executable grouping, the full-input split-count core, the `7n/10 + O(1)` partition-size wrapper, the abstract linear recurrence theorem, and the CLRS-facing recurrence wrapper are proved; randomized expected-time analysis and concrete executable runtime proof remain. |
| Chapter 11, expected hashing analysis | Extend the finite-uniform bucket toolkit to chained hashing under a formal random key or random hash-function model. |
| Chapter 12 pointer-level BST layer | CLRS parent-pointer search/min/max/successor/predecessor/transplant/delete refinement. |
| Chapter 13 full red-black algorithms | Prove `RB-DELETE`/`RB-DELETE-FIXUP` and the logarithmic-height theorem; executable insertion is already in place. |
| Chapter 14 remaining augmentation targets | Connect the proved size/rank-preserving rotations to red-black balancing; add interval trees and the general augmentation theorem. |
| Chapter 15 remaining dynamic-programming targets | Mutable-array/memoized rod cutting and executable matrix-chain, LCS, and OBST table/reconstruction algorithms. |
| Chapter 17 dynamic-table refinements | Mutable-array copying, allocator/RAM cost semantics, and sharper load-factor potential refinements. |
| Chapter 18 B-tree refinements | Full separator/same-depth invariant stack, node-level deletion repair, disk-page and mutation refinement. |
| Chapter 19 Fibonacci-heap refinements | Pointer forest, handles, cascading cuts, consolidation arrays, subtree-size induction, and true Fibonacci logarithmic degree theorem. |
| Chapter 20 van Emde Boas refinements | Recursive summary/cluster representation, word-RAM base cases, and `O(log log u)` asymptotic bridge. |
| Chapter 21 | Not yet represented in the current Lean tree. |
| Chapter 22, Section 22.1 | A finite directed-graph model with walks, paths, cycles, reachability, connected components, and undirected-graph symmetry is established. | BFS/DFS correctness, topological sort, and strongly connected components. |
| Chapter 23 Prim | Prim's algorithm theorem interface and proof have not been added yet. |
| Chapter 24 onward | Not yet represented in the current Lean tree. |

## Next Proof Plan

The next work should focus on removing central theorem gaps, not on reworking
chapters that already have their advertised main theorem.  The intended order is:

| Priority | Target | Concrete deliverable |
| --- | --- | --- |
| 1 | Chapter 12, Section 12.1 | Keep the functional BST theorem boundary explicit and strengthen successor/predecessor/delete wrappers where they make the public model clearer. |
| 2 | Chapter 14, Section 14.1 | Use the proved size-preserving rotations as the bridge toward Chapter 13 balancing, then prepare interval-tree and augmentation-theorem interfaces. |
| 3 | Chapter 15, Sections 15.2/15.4 plus 15.1 refinements | Advance DP table and reconstruction theorems, prioritizing matrix-chain executable reconstruction and LCS table/reconstruction after the new 15.1 table-certificate layer. |
| 4 | Chapter 11, Section 11.2 | Clarify and extend the finite-uniform hashing toolkit before committing to a full random key/hash-function model. |
| 5 | Chapter 13, Section 13.1 | Shift from insertion to red-black deletion fixup and the logarithmic-height theorem; keep the functional certificate layer. |
| 6 | Chapter 1--10 cleanup pass | After the 11--15 branch scope is stable, return to Ch4 final Master packaging, Ch7/9 randomized expectation, and Ch8 bucket expected time. |

## Extreme-Difficulty Queue

These are the places that are likely to require concentrated proof-design work
rather than ordinary lemma filling.

| Difficulty | Scope | Why it is hard | Suggested attack |
| --- | --- | --- | --- |
| Extreme | Randomized expected-time analysis in Chapters 7, 8, 9, and 11 | We need a reusable finite probability model, expectation algebra, and asymptotic bounds over random choices, not just deterministic correctness.  Chapter 11 now has a finite-uniform bucket toolkit, but not yet the full random key/hash-function model. | Generalize the Chapter 11 finite-uniform average layer into a reusable probability toolkit, then use it for one randomized theorem end-to-end before broadening. |
| Extreme | Full red-black insertion/deletion fixup | The proof is a large state-machine invariant with rotations, recoloring, black-height preservation, and parent/shape constraints. | Keep the functional certificate layer, prove each fixup case as a separate theorem, then compose them only after the case lemmas stabilize. |
| High | Chapter 23 automatic MST exchange certificate | The textbook proof hides a path/cycle boundary-edge extraction argument that must be made explicit in finite graphs. | Introduce a reusable path/walk API, prove a cut-crossing boundary-edge lemma, then plug it into the existing cut-property theorem. |
| High | Chapter 4 final all-input Master theorem | The main bridge, natural-exponent case-1/2 polynomial wrappers, real-log case-1 wrappers, and real-log-log case-2 wrappers now exist, but the final theorem still needs the case-3 comparison scale. | Isolate the case-3 forcing comparison as the remaining analytic target. |
| High | Full RAM/pseudocode semantics | It would replace many current mathematical specifications with executable imperative-state refinement proofs. | Treat this as a separate project layer after the mathematical theorem interface is stable. |

## Near-Term Scheduling Rule

When choosing the next task on this branch, prefer the highest-value item in
Chapters 11--15 over repeatedly polishing a completed first-bucket section.
Chapter 6 should now receive only audit, documentation, or RAM-cost refinement
unless a concrete gap is found.  The next 1--10 cleanup pass should target
Chapter 4 final Master packaging, Chapter 7/9 randomized expectation, and the
remaining Chapter 8 full input-distribution cost model after the 11--15 track is
stable.
