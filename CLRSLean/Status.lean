/-!
# Proof Status

This page is the public status ledger for the web site.  It mirrors the longer
maintainer notes in {lit}`docs/proof-map.md`, but is written for readers who are
navigating the deployed pages.

## Status Labels

* {lit}`proved`: the named section theorem is proved in Lean for the current
  specification.
* {lit}`expository`: a reader-facing guide page with no theorem target.
* {lit}`partial`: important theorem infrastructure exists, but the full textbook
  claim is not complete.
* {lit}`statement`: the intended theorem interface exists, but proof work has not
  started.
* {lit}`blocked-design`: progress depends on choosing a stable representation.
* {lit}`blocked-mathlib`: progress depends on missing or inconvenient Mathlib
  infrastructure.
* {lit}`deferred-implementation`: the mathematical proof is in scope, but a
  low-level implementation proof is postponed.
* {lit}`future-work`: exercises, chapter-end problems, or strengthening passes
  outside the current main track.

## Planning Board

This board is deliberately coarser than the theorem ledger below.  It answers
the scheduling question: which areas already have their advertised main proof,
which areas have useful Lean structure but still need a central theorem, and
which areas should not yet be counted as proof-complete.

### Main Proof Completed

* Chapter 2, Sections 2.1-2.3: insertion sort, insertion-sort quadratic
  comparison bound, merge-sort correctness, and the power-of-two merge-sort
  recurrence are proved for the current models.
* Chapter 3, Section 3.1: CLRS-facing asymptotic notation wrappers and basic
  algebraic facts are proved.
* Chapter 4, Sections 4.1-4.6, current models: maximum-subarray correctness,
  Strassen 2 by 2 block algebra, substitution-method bounds, recursion-tree
  additive expansions, exact-power Master-method cases, floor/ceiling
  exact-power extraction, the all-input transfer bridge, adjacent-power
  sandwich generation from one-step scale bounds, and discrete all-input
  scale wrappers with packaged floor/ceiling Master cases 1, 2, and 3 are
  proved; the critical-power scale is also connected to the textbook
  {lit}`n^(log_b a)` scale by a real-log bridge, and the case-2 scale is
  connected to {lit}`n^(log_b a) log n`; named wrappers expose both textbook
  scales directly.
* Chapter 5, Section 5.1: the hiring problem is proved in the finite
  rank-symmetry model.
* Chapter 6, Sections 6.1-6.5: the indexed array heap layer, recursive
  {lit}`MAX-HEAPIFY`, bottom-up {lit}`BUILD-MAX-HEAP`, in-place heapsort
  sorted-suffix invariant, top-level heapsort correctness, and array-level
  priority-queue state theorems are proved.
* Chapter 7, Sections 7.1-7.3: stable functional partition classification,
  scan-state partition-loop correctness, a returned pivot-index partition
  wrapper with an explicit adjacent-swap trace, functional quicksort
  sortedness/permutation preservation, a deterministic quadratic
  comparison-count bound, and the randomized-quicksort expected-comparison
  recurrence with a named closed form and harmonic bounds are proved for the
  current models.
* Chapter 8, Sections 8.2-8.4: stable counting-sort bucket correctness,
  abstract radix-sort correctness plus complete digit-signature stability from
  stable digit passes, a concrete base-{lit}`b` natural-key radix wrapper, a
  key-order correctness wrapper with the bounded fixed-width arithmetic bridge
  discharged, deterministic bucket-sort correctness, and the finite-uniform
  collision/second-moment core plus an abstract linear expected-cost wrapper
  for bucket-sort expected time are proved.
* Chapter 9, Sections 9.2-9.3: selection-by-rank correctness is proved for the
  specification selector, a pivot-style quickselect model, and a
  pivot-parametric deterministic SELECT model with a count-based
  order-statistic certificate; the median-of-medians pivot/select wrapper, the
  local five-element median certificate, executable five-element grouping plus
  the grouped split-count core for the median-of-medians argument, the
  CLRS-style partition-size bound, the abstract linear recurrence wrapper, and
  the CLRS-facing SELECT recurrence wrapper are also proved.
* Chapter 10, Sections 10.1-10.2: functional stack, queue, and linked-list
  operation specifications are proved.
* Chapter 11, Section 11.1: direct-address table insert/search/delete behavior
  is proved.
* Chapter 16, Sections 16.1 and 16.3: activity selection has a recursive
  greedy optimality theorem, and Huffman V2 has frequency-table optimality and
  minimum-cost wrappers.

### Structured But Not Complete

* Chapter 3, Section 3.2: many standard-function asymptotic facts are proved,
  but the full CLRS table is not complete.
* Chapter 4 as a whole: the local proof engines are strong and the first
  discrete all-input Master wrappers are proved, including floor/ceiling
  recurrence packaging for exact-power Master cases 1, 2, and 3, plus
  natural-exponent polynomial wrappers for cases 1 and 2 when
  {lit}`a = b^p`, a real-log comparison bridge from the discrete
  critical-power scale to {lit}`n^(log_b a)`, named case-1 wrappers in that
  textbook scale, a real-log-log bridge from the discrete case-2 scale to
  {lit}`n^(log_b a) log n`, and named case-2 wrappers in that textbook scale.
  The case-3 comparison layer and selected runtime refinements remain.
* Chapter 11, Section 11.2: deterministic chained-hash-table operations are
  proved for a fixed hash function, and the finite-uniform bucket interface
  proves expected chain length equals load factor, nonnegativity facts, and
  single-insert load-factor/unsuccessful-search cost changes; a full random
  key/hash function model remains.
* Chapter 12, Section 12.1: the functional BST theorem boundary is proved for
  search, min/max, insertion, complete successor/predecessor specifications,
  successor/predecessor existence wrappers, search-after-insert/delete wrappers,
  deletion wrappers, and successor/predecessor-after-delete wrappers; parent
  pointers, transplant, and mutation remain.
* Chapter 13, Section 13.1: local red-black rotation/recoloring invariants,
  the four local insertion-fixup membership/black-height/shape certificates,
  and the executable `RBTree.insert` with its membership, red-black shape, and
  black-height theorems are proved; proving {lit}`RB-DELETE`, {lit}`RB-DELETE-FIXUP`, and
  the logarithmic-height theorem remains.
* Chapter 22, Section 22.1: a finite directed-graph model with adjacency,
  walks, paths, cycles, reachability, connected components, and undirected-graph
  symmetry is established.
* Chapter 22, Section 22.2: a fuelled breadth-first-search procedure and a
  soundness proof that every visited vertex is reachable are in place;
  completeness and shortest-path distance lemmas remain.
* Chapter 22, Section 22.3: a functional depth-first-search model with
  discovery/finish times and parent pointers is in place, together with the
  basic color invariants ({lit}`dfsVisit_blackens_u`, {lit}`dfsVisit_preserves_black`,
  {lit}`dfsVisit_no_new_gray`) and the global soundness lemma {lit}`dfs_all_black`, which
  states that every graph vertex is black after {lit}`dfs`; the parenthesis theorem,
  white-path theorem, and edge classification remain.
* Chapter 22, Section 22.4: Kahn's algorithm for topological sorting is
  implemented and {lit}`topologicalSort_isTopologicalOrder` proves that it returns a
  valid topological order for every DAG; strongly connected components remain.
* Chapter 22, Section 22.5: Kosaraju's two-pass SCC algorithm is implemented and
  the returned components are proved to be a nonempty partition of the vertex set
  ({lit}`kosarajuComponents_subset`, {lit}`kosarajuComponents_pairwise_disjoint`,
  {lit}`kosarajuComponents_cover`, {lit}`kosarajuComponents_nonempty`, and
  {lit}`kosarajuComponents_isSCCPartition`); the strong-connectivity and maximality
  core is reduced to a DFS finish-time ordering lemma and is currently admitted
  with {lit}`sorry`.
* Chapter 14, Section 14.1: order-statistic tree size augmentation,
  recomputation, key preservation, size/rank-preserving local rotations, and
  rank-selection correctness are proved for a functional augmented tree; the
  recompute-then-rotate bridge is also proved for future balancing refinements.
  Connecting those rotation wrappers to full red-black balancing, interval
  trees, and the general augmentation theorem remain.
* Chapter 15, Sections 15.1, 15.2, and 15.4: rod-cutting Bellman recurrence
  facts plus finite bottom-up table-prefix correctness and an executable
  recurrence-valued function, matrix-chain parenthesization optimality plus
  split-table reconstruction certificates, and LCS certificate optimality plus
  table-recurrence reconstruction certificates and recurrence wrappers are
  proved, including matching-head and nonmatching-head recurrence consequences;
  mutable-array/memoized execution, executable reconstruction procedures, and
  optimal binary search trees remain.
* Chapter 17, Sections 17.1-17.4: finite-prefix aggregate/accounting/potential
  theorems plus {lit}`MULTIPOP`, executable binary-counter one-step potential
  bound, executable multi-step counter trace bounds, and size-level
  dynamic-table potential nonnegativity, capacity feasibility/direction facts,
  post-state field equations, stored-count direction facts, actual-cost and
  capacity-choice case specs, positive/zero deletion-cost exact wrappers,
  premise-light deletion-cost branch wrappers, positive-cost lower bounds, upper bounds,
  positive insertion/deletion count/capacity wrappers, post-state capacity
  corollaries, post-transition potential nonnegativity,
  concrete amortized-cost unfolding, resize-branch capacity wrappers, and
  insertion/deletion wrappers are proved;
  allocator and RAM refinements remain.
* Chapter 18, Sections 18.1-18.3: a mathematical B-tree model has search,
  direct base search success/failure wrappers, minimum-key height-expression
  base/positivity facts, recurrence, and monotonicity, split-child
  preservation, direct split validity, split-child direct
  membership/search preservation, insertion/deletion membership, and successful
  and unsuccessful search-after-update theorem surfaces plus direct
  insertion/deletion validity short-name wrappers, equality-key update-query
  wrappers, Prop-level deletion success wrappers, membership-driven
  search-after-update wrappers, direct inserted/deleted-key, old-key query
  preservation, and failed membership
  corollaries plus direct failed-membership preservation wrappers; full
  separator/same-depth, node-level-deletion, and disk-page refinements remain.
* Chapter 19, Section 19.1: abstract Fibonacci-heap finite-set operations,
  empty-heap construction, direct operation-result validity wrappers,
  empty-result query specs, direct
  insert/union/extract-min/decrease-key/delete membership facts plus
  operation-key, old-key preservation, failed membership corollaries, and
  direct failed-membership preservation wrappers, minimum-after-update
  positive/empty specifications plus
  direct minimum/extract-min empty-result and nonempty-result wrappers,
  remaining/delete minimum nonempty-result wrappers, and
  insert/union/extract-min-remaining/decrease-key/delete minimum direct
  membership/lower-bound wrappers, heap-potential zero/nonnegativity and
  telescoping facts, and Fibonacci
  lower-bound recurrence/positivity/monotonicity and even/half-index
  power-of-two growth facts plus conditional degree-to-log wrappers are
  proved; pointer
  handles, cascading cuts, and the true Fibonacci logarithmic degree theorem
  remain.
* Chapter 20, Sections 20.1-20.2: vEB high/low/index arithmetic, bounded
  recomposition facts, and finite-set operation specs, including
  extrema/successor/predecessor positive and empty-result cases, successful
  query universe-bound corollaries, membership-, extrema-, and
  neighbor-query-after-update positive/no-neighbor specs, extrema
  empty-after-update specs, direct extrema membership/lower- and upper-bound
  wrappers, direct extrema-after-update membership/order wrappers, direct
  base/insert/delete neighbor membership/order wrappers, direct member-query
  preservation and failure corollaries, direct failed member-query
  preservation wrappers, direct no-neighbor query wrappers, premise-light
  no-neighbor wrappers over old represented sets, direct extrema empty-result
  wrappers, direct base extrema/neighbor nonempty-result wrappers,
  direct updated-neighbor nonempty-result wrappers,
  direct deletion-extrema nonempty-result wrappers,
  update-query universe-bound corollaries, and
  operation-depth recurrence/monotonicity specs, are proved; recursive cluster
  representation
  and the {lit}`O(log log u)` bridge remain.
* Chapter 23, Sections 23.1-23.2: the cut property, safe-edge theorem,
  exact-component Kruskal scan facts, forest/spanning wrappers, and
  certificate-based Kruskal optimality interfaces exist; automatic simple
  path/cycle exchange extraction, fully prefix-local sorted-lightness wrapping,
  and Prim remain.

### Missing Core Theorem

* Chapter 4 full Master-theorem instantiation: add the case-3 forcing
  comparison scale.
* Chapter 7 remaining refinements: index-level mutable-array partition
  refinement, an explicit probability space for pivot choices, sharp
  {lit}`n log n` tail bounds, and lower-bound packaging.
* Chapter 9 randomized SELECT and executable cost refinements:
  pivot-parametric deterministic SELECT, executable median-of-medians SELECT,
  the local five-element median certificate, executable grouping, the
  grouped/full-input split-count core, {lit}`7n/10` partition-size packaging,
  the abstract linear recurrence theorem, and the CLRS-facing recurrence wrapper
  are proved; randomized expected time and the concrete executable runtime
  theorem remain.
* Chapter 11 expected hashing analysis: extend the finite-uniform bucket
  interface to a formal random key or random hash-function model with
  independence assumptions.
* Chapter 12 pointer-level BST layer: CLRS parent-pointer procedures,
  transplant, and mutation refinement.
* Chapter 13 full red-black algorithms: prove {lit}`RB-DELETE`/{lit}`RB-DELETE-FIXUP`
  and the logarithmic-height theorem; executable insertion is already in place.
* Chapter 22 graph algorithms: complete BFS (reachability completeness and
  unweighted shortest-path distances), complete DFS (parenthesis theorem,
  white-path theorem, edge classification), and strongly connected components on
  top of the Section 22.1 graph model; topological sorting is already in place.
* Chapter 14 remaining augmentation targets: connect the proved
  size/rank-preserving rotations to red-black balancing, then add interval
  trees and the general augmentation theorem.
* Chapter 15 remaining dynamic-programming targets: mutable-array and memoized
  rod cutting, executable matrix-chain and LCS table/reconstruction algorithms,
  and optimal binary search trees.
* Chapter 17 dynamic-table refinements: mutable-array copying, allocator/RAM
  cost semantics, and sharper load-factor potential refinements.
* Chapter 18 B-tree refinements: full occupancy/separator/same-depth invariant
  stack, node-level deletion repair, and disk-page/mutation semantics.
* Chapter 19 Fibonacci-heap refinements: pointer forest, handles, cascading
  cuts, consolidation arrays, subtree-size induction, and true Fibonacci
  logarithmic degree theorem.
* Chapter 20 van Emde Boas refinements: recursive summary/cluster
  representation, word-RAM base cases, and the explicit {lit}`O(log log u)`
  asymptotic bridge.
* Chapter 21 disjoint sets: not yet represented.
* Chapter 23 Prim: theorem interface and proof have not been added.
* Chapter 24 onward: not yet represented.

Near-term rule: do not return to a completed main-proof area, especially
Chapter 6, without a concrete audit or refinement target.  On the current
branch, the proof-heavy targets are Chapters 11--15: strengthen the functional
BST boundary, connect order-statistic rotations to later balancing work,
advance dynamic-programming reconstruction/table interfaces, clarify the
finite-uniform hashing toolkit, and keep red-black insertion-fixup progress
case-by-case.  Chapter 4, Chapter 7, Chapter 8, and Chapter 9 refinements are
the next cleanup pass after this 11--15 track.

## Proved

* 4.1 Maximum-subarray specification:
  {lit}`CLRS.Chapter04.mem_nonemptySubarrays_iff`,
  {lit}`CLRS.Chapter04.mem_crossingSubarrays_iff`,
  {lit}`CLRS.Chapter04.bestCandidate_correct`,
  {lit}`CLRS.Chapter04.maxCrossingSubarray_correct`,
  {lit}`CLRS.Chapter04.maxCrossingSubarray_isNonemptySubarray_append`,
  {lit}`CLRS.Chapter04.subarray_append_left_or_right_or_crossing`,
  {lit}`CLRS.Chapter04.subarray_append_optimal_of_cases`,
  {lit}`CLRS.Chapter04.maxSubarrayDivideStep_correct`,
  {lit}`CLRS.Chapter04.maxSubarrayDivideTree_correct`,
  {lit}`CLRS.Chapter04.maxSubarrayDivideFuel_correct`,
  {lit}`CLRS.Chapter04.maxSubarray_exists_of_ne_nil`,
  {lit}`CLRS.Chapter04.maxSubarray_correct`.
* 4.2 Strassen 2-by-2 block algebra:
  {lit}`CLRS.Chapter04.Matrix2.strassen_eq_mul` and
  {lit}`CLRS.Chapter04.strassen2x2_correct`.
* 3.1 Asymptotic notation:
  {lit}`CLRS.Chapter03.isBigO_iff`,
  {lit}`CLRS.Chapter03.isLittleO_iff`,
  {lit}`CLRS.Chapter03.isBigOmega_iff`,
  {lit}`CLRS.Chapter03.isLittleOmega_iff`,
  {lit}`CLRS.Chapter03.isBigTheta_trans`.
* 4.5 Master method, exact-power model:
  {lit}`CLRS.Chapter04.h_formula`,
  {lit}`CLRS.Chapter04.master_case1_geometric`,
  {lit}`CLRS.Chapter04.master_case2_constant_forcing`,
  {lit}`CLRS.Chapter04.master_case3_tail_dominated`.
* 4.6 Master theorem, all-input recurrence and transfer bridge:
  {lit}`CLRS.Chapter04.FloorDivideRecurrence`,
  {lit}`CLRS.Chapter04.CeilDivideRecurrence`,
  {lit}`CLRS.Chapter04.exactPowerRecurrence_of_floorDivideRecurrence`,
  {lit}`CLRS.Chapter04.exactPowerRecurrence_of_ceilDivideRecurrence`,
  {lit}`CLRS.Chapter04.powerInterval_of_pos`,
  {lit}`CLRS.Chapter04.eventuallyPowerUpperSandwich_of_powerStep`,
  {lit}`CLRS.Chapter04.eventuallyPowerLowerSandwich_of_powerStep`,
  {lit}`CLRS.Chapter04.allInput_bigO_of_power_upper_sandwich`,
  {lit}`CLRS.Chapter04.allInput_bigOmega_of_power_lower_sandwich`,
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_power_sandwich`, and
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_powerStep`,
  {lit}`CLRS.Chapter04.criticalPowerScale`,
  {lit}`CLRS.Chapter04.criticalPowerScale_monotoneAbs`,
  {lit}`CLRS.Chapter04.criticalPowerScale_powerStepBound`, and
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_criticalPowerScale`,
  {lit}`CLRS.Chapter04.criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.criticalPowerLogScale_monotoneAbs`,
  {lit}`CLRS.Chapter04.criticalPowerLogScale_powerStepBound`, and
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.tailDominatedScale`,
  {lit}`CLRS.Chapter04.tailDominatedScale_exactPower`, and
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_tailDominatedScale`,
  {lit}`CLRS.Chapter04.polynomialScale`,
  {lit}`CLRS.Chapter04.polynomialLogScale`,
  {lit}`CLRS.Chapter04.criticalPowerScale_isBigTheta_polynomialScale`, and
  {lit}`CLRS.Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale`,
  {lit}`CLRS.Chapter04.realLogExponent`,
  {lit}`CLRS.Chapter04.realLogScale`,
  {lit}`CLRS.Chapter04.criticalPowerScale_isBigTheta_realLogScale`,
  {lit}`CLRS.Chapter04.realLogLogScale`,
  {lit}`CLRS.Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_criticalPowerScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_criticalPowerScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_criticalPowerScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_realLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_realLogScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_realLogScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_polynomialScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_polynomialScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_polynomialScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase2_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase2_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase2_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase2_realLogLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase2_realLogLogScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase2_realLogLogScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase2_polynomialLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase2_polynomialLogScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase2_polynomialLogScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase3_tailDominatedScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase3_tailDominatedScale`,
  and {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase3_tailDominatedScale`.
* 4.3 Substitution method, one-step recurrence model:
  {lit}`CLRS.Chapter04.substitution_upper_bound`,
  {lit}`CLRS.Chapter04.substitution_lower_bound`,
  {lit}`CLRS.Chapter04.substitution_sandwich`,
  {lit}`CLRS.Chapter04.linear_substitution_upper_bound`,
  {lit}`CLRS.Chapter04.geometric_substitution_upper_bound`.
* 4.4 Recursion-tree method, additive level-cost model:
  {lit}`CLRS.Chapter04.recursion_tree_additive_unroll`,
  {lit}`CLRS.Chapter04.recursion_tree_additive_upper_envelope`,
  {lit}`CLRS.Chapter04.recursion_tree_additive_lower_envelope`,
  {lit}`CLRS.Chapter04.recursion_tree_constant_level_cost`.
* 5.1 Hiring problem, finite rank-symmetry model:
  {lit}`CLRS.Chapter05.uniformAverage_indicator_singleton`,
  {lit}`CLRS.Chapter05.hireProbability_eq`,
  {lit}`CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`,
  {lit}`CLRS.Chapter05.expectedHires_eq_harmonic`,
  {lit}`CLRS.Chapter05.harmonic_isBigTheta_log`, and
  {lit}`CLRS.Chapter05.expectedHires_isBigTheta_log`.
* 6.1 Heaps, indexed heap predicate and root maximum:
  {lit}`CLRS.Chapter06.parent_lt_self`,
  {lit}`CLRS.Chapter06.eq_left_or_right_parent`,
  {lit}`CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`, and
  {lit}`CLRS.Chapter06.orderedDesc_arrayMaxHeap`; localized predicate bridge:
  {lit}`CLRS.Chapter06.ArrayMaxHeapFrom.to_global`.
* 6.2 Maintaining the heap property, fuelled array heapify repair:
  {lit}`CLRS.Chapter06.swapAt_perm`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_perm`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_valAt_of_heapSize_le`,
  {lit}`CLRS.Chapter06.valAt_i_le_maxChildIndex`, and
  {lit}`CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`;
  recursive repair:
  {lit}`CLRS.Chapter06.maxHeapifyFuel_child_repair_after_swap`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_swap_branch_repair`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_repair_subtree` and
  {lit}`CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap`.
* 6.3 Building a heap, bottom-up repeated heapify:
  {lit}`CLRS.Chapter06.ArrayMaxHeapFrom.of_half`,
  {lit}`CLRS.Chapter06.buildMaxHeapLoop_isMaxHeap`,
  {lit}`CLRS.Chapter06.buildMaxHeapLoop_perm`,
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap`, and
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_correct`.
* 6.4 The heapsort algorithm, in-place loop refinement:
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_length`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_perm`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_length`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_perm`,
  {lit}`CLRS.Chapter06.HeapSortLoopInvariant.initial`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_suffix_head_eq_root`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_suffix_head_bounds_prefix`,
  {lit}`CLRS.Chapter06.HeapSortLoopInvariant.step`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_shrink_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_terminal_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_terminal_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_orderedAsc`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_terminal_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_orderedAsc`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_exact_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSort_terminal_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSort_eq_arrayHeapSortInPlace`,
  {lit}`CLRS.Chapter06.arrayHeapSort_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSort_exact_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSort_orderedAsc`, and
  {lit}`CLRS.Chapter06.arrayHeapSort_correct`.
* 6.5 Priority queues, functional heap interface:
  {lit}`CLRS.Chapter06.heapInsert_orderedDesc`,
  {lit}`CLRS.Chapter06.heapInsert_perm`,
  {lit}`CLRS.Chapter06.heapInsert_max`,
  {lit}`CLRS.Chapter06.heapIncreaseKey_orderedDesc`,
  {lit}`CLRS.Chapter06.heapIncreaseKey_perm`,
  {lit}`CLRS.Chapter06.heapDelete_orderedDesc`, and
  {lit}`CLRS.Chapter06.heapDelete_perm`.
* 6.5 Array-level heap maximum, full fuelled increase-key, extract-max, and
  delete:
  {lit}`CLRS.Chapter06.ArrayMaxHeap.getElem_le_root` and
  {lit}`CLRS.Chapter06.arrayHeapMaximum?_max`,
  {lit}`CLRS.Chapter06.ArrayMaxHeap.set_increased_except_up`,
  {lit}`CLRS.Chapter06.ArrayMaxHeapExceptUp.bubble_step`,
  {lit}`CLRS.Chapter06.ArrayMaxHeapExceptUp.bubbleUpFuel_global`,
  {lit}`CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapIncreaseKeyNoBubble?_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapExtractMax?_state_correct`, and
  {lit}`CLRS.Chapter06.arrayHeapDelete?_state_correct`.
* 7.1 Description of quicksort, functional-list and scan-state loop model:
  {lit}`CLRS.Chapter07.partitionAround_left_eq_filter`,
  {lit}`CLRS.Chapter07.partitionAround_right_eq_filter`,
  {lit}`CLRS.Chapter07.mem_partitionAround_left_iff`,
  {lit}`CLRS.Chapter07.mem_partitionAround_right_iff`,
  {lit}`CLRS.Chapter07.partitionAround_correct`,
  {lit}`CLRS.Chapter07.partitionAround_perm`,
  {lit}`CLRS.Chapter07.partitionAround_left_allLeUpper`,
  {lit}`CLRS.Chapter07.partitionAround_right_allGt`,
  {lit}`CLRS.Chapter07.AdjacentSwapTrace.to_perm`,
  {lit}`CLRS.Chapter07.AdjacentSwapTrace.of_perm`,
  {lit}`CLRS.Chapter07.partitionLoop_invariant`,
  {lit}`CLRS.Chapter07.partitionLoop_correct`,
  {lit}`CLRS.Chapter07.clrsPartition_correct`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_pivot`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_left_bound`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_right_bound`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_perm`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_swapTrace`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_correct`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_correct_with_trace`,
  {lit}`CLRS.Chapter07.quickSort_perm`,
  {lit}`CLRS.Chapter07.quickSort_ordered`, and
  {lit}`CLRS.Chapter07.quickSort_correct`.
* 7.2 Performance of quicksort, deterministic comparison-count model:
  {lit}`CLRS.Chapter07.partitionAround_length_add`,
  {lit}`CLRS.Chapter07.quickSortComparisonsFuel_quadratic`, and
  {lit}`CLRS.Chapter07.quickSortComparisons_quadratic`.
* 7.3 Randomized quicksort recurrence model:
  {lit}`CLRS.Chapter07.harmonic_succ`,
  {lit}`CLRS.Chapter07.sum_mul_harmonic_eq`,
  {lit}`CLRS.Chapter07.sum_expectedComparisons_eq`,
  {lit}`CLRS.Chapter07.expectedComparisons_closed_form`,
  {lit}`CLRS.Chapter07.expectedComparisons_recurrence`,
  {lit}`CLRS.Chapter07.expectedComparisons_telescope`,
  {lit}`CLRS.Chapter07.expectedComparisons_clrs_harmonic_bound`,
  {lit}`CLRS.Chapter07.expectedComparisons_harmonic_bound`,
  {lit}`CLRS.Chapter07.expectedComparisons_quadratic`, and
  {lit}`CLRS.Chapter07.expectedComparisons_monotone`.
* 8.2 Counting sort, stable bucket specification:
  {lit}`CLRS.Chapter08.countingSortBy_ordered`,
  {lit}`CLRS.Chapter08.countingSortBy_bucket_eq`,
  {lit}`CLRS.Chapter08.countingSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.countingSortBy_perm`, and
  {lit}`CLRS.Chapter08.countingSortBy_correct`.
* 8.3 Radix sort, abstract stable digit-pass model with complete
  digit-signature stability, concrete base-{lit}`b` digit extraction, and
  bounded key-order packaging:
  {lit}`CLRS.Chapter08.radixPass_orderedRel`,
  {lit}`CLRS.Chapter08.radixSortBy_ordered`,
  {lit}`CLRS.Chapter08.radixSortBy_stable`,
  {lit}`CLRS.Chapter08.radixSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.radixSortBy_perm`,
  {lit}`CLRS.Chapter08.radixSortBy_correct_stable`,
  {lit}`CLRS.Chapter08.baseDigitsLow_allDigitsLe`,
  {lit}`CLRS.Chapter08.radixSortNatBy_correct_stable`,
  {lit}`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_digitOrder`,
  {lit}`CLRS.Chapter08.radixDigitOrderRespectsKey_of_bounded`, and
  {lit}`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_bounded`.
* 8.4 Bucket sort, deterministic bucket-index model:
  {lit}`CLRS.Chapter08.bucketSortBy_ordered`,
  {lit}`CLRS.Chapter08.bucketSortBy_perm`,
  {lit}`CLRS.Chapter08.bucketSortBy_correct`,
  {lit}`CLRS.Chapter08.bucketSortByRank_correct`,
  {lit}`CLRS.Chapter08.uniformAverageFin_indicator_singleton`,
  {lit}`CLRS.Chapter08.uniformAverageFin2_collision`,
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_eq`,
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`,
  {lit}`CLRS.Chapter08.expectedBucketSortCost_self_eq`, and
  {lit}`CLRS.Chapter08.expectedBucketSortCost_linear_bound`.
* 9.2 Selection by rank, specification selector and pivot-style quickselect:
  {lit}`CLRS.Chapter09.sortedCopy_perm`,
  {lit}`CLRS.Chapter09.sortedCopy_pairwise`,
  {lit}`CLRS.Chapter09.gtCount_eq_length_sub_leCount`,
  {lit}`CLRS.Chapter09.selectByRank?_mem`,
  {lit}`CLRS.Chapter09.selectByRank?_rankCorrect`, and
  {lit}`CLRS.Chapter09.selectByRank?_correct`;
  {lit}`CLRS.Chapter09.quickSelect?_mem`,
  {lit}`CLRS.Chapter09.quickSelect?_rankCorrect`, and
  {lit}`CLRS.Chapter09.quickSelect?_correct`.
* 9.3 Deterministic selection, pivot-parametric interface:
  {lit}`CLRS.Chapter09.selectWithPivot?_mem`,
  {lit}`CLRS.Chapter09.selectWithPivot?_rankCorrect`,
  {lit}`CLRS.Chapter09.selectWithPivot?_correct`,
  {lit}`CLRS.Chapter09.medianOfFive?_certificate`,
  {lit}`CLRS.Chapter09.medianOfFive?_isSome_of_length_eq_five`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_lengths`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_length_mul_five_le`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_length_near`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_flatten_sublist`,
  {lit}`CLRS.Chapter09.leCount_le_of_sublist`,
  {lit}`CLRS.Chapter09.geCount_le_of_sublist`,
  {lit}`CLRS.Chapter09.medianOfFiveGroups?_certificates`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianGroupCertificates`,
  {lit}`CLRS.Chapter09.medianGroupCertificates_leCount_lower_bound`,
  {lit}`CLRS.Chapter09.medianGroupCertificates_geCount_lower_bound`,
  {lit}`CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_selectPivot_split_counts`,
  {lit}`CLRS.Chapter09.medianOfFiveGroups?_mem_flatten`,
  {lit}`CLRS.Chapter09.medianOfFiveGroups?_isSome_of_all_lengths`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianOfFiveGroups?_isSome`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_split_counts`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_fullInput_split_counts`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_lengths`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_size_bound`,
  {lit}`CLRS.Chapter09.selectRecurrence_linear_step`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_recursive_branch_size_bound`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_low_branch_linear_work_step`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_high_branch_linear_work_step`,
  {lit}`CLRS.Chapter09.selectRecurrence_linear_induction`,
  {lit}`CLRS.Chapter09.medianOfMedians_linear_bound`,
  {lit}`CLRS.Chapter09.clrsSelectRecurrence_linear_bound`,
  {lit}`CLRS.Chapter09.deterministicSelect?_mem`,
  {lit}`CLRS.Chapter09.deterministicSelect?_rankCorrect`, and
  {lit}`CLRS.Chapter09.deterministicSelect?_correct`;
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_mem`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`,
  {lit}`CLRS.Chapter09.medianOfMediansSelect?_mem`,
  {lit}`CLRS.Chapter09.medianOfMediansSelect?_rankCorrect`, and
  {lit}`CLRS.Chapter09.medianOfMediansSelect?_correct`.
* 2.1 Insertion sort:
  {lit}`CLRS.Chapter02.insertionSort_sorted`,
  {lit}`CLRS.Chapter02.insertionSort_perm`.
* 2.2 Analyzing algorithms:
  {lit}`CLRS.Chapter02.insertionSortWorstComparisons_quadratic`.
* 2.3 Designing algorithms:
  {lit}`CLRS.Chapter02.mergeSort_sortedLE`,
  {lit}`CLRS.Chapter02.mergeSort_perm`,
  {lit}`CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`.
* 16.3 Huffman codes:
  {lit}`CLRS.HuffmanV2.optimum_huffman_freqs`,
  {lit}`CLRS.HuffmanV2.huffmanOfFreqs_correct`, and
  {lit}`CLRS.HuffmanV2.huffmanOfFreqs_cost_le`.
* 16.1 Activity selection, finite sorted-list model:
  {lit}`CLRS.ActivitySelection.earliest_finish_minFinish`,
  {lit}`CLRS.ActivitySelection.finishSorted_head_minFinish`,
  {lit}`CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`,
  {lit}`CLRS.ActivitySelection.activitySelection`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_eq`,
  {lit}`CLRS.ActivitySelection.greedySelect_cons_eq`,
  {lit}`CLRS.ActivitySelection.greedySelect_sublist`,
  {lit}`CLRS.ActivitySelection.greedySelect_feasible`,
  {lit}`CLRS.ActivitySelection.greedySelect_after_maxCardinality`,
  {lit}`CLRS.ActivitySelection.greedySelect_cons_maxCardinality`,
  {lit}`CLRS.ActivitySelection.greedySelect_maxCardinality`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_maxCardinality`,
  {lit}`CLRS.ActivitySelection.activitySelection_maxCardinality`,
  {lit}`CLRS.ActivitySelection.greedySelect_optimal_length`,
  {lit}`CLRS.ActivitySelection.greedySelect_cons_recursive_correct`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_recursive_correct`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_correct`, and
  {lit}`CLRS.ActivitySelection.activitySelection_correct`.
* 10.1 Stacks and queues:
  {lit}`CLRS.Chapter10.pop_push`,
  {lit}`CLRS.Chapter10.dequeue_enqueue_empty`,
  {lit}`CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists:
  {lit}`CLRS.Chapter10.listSearch_sound`,
  {lit}`CLRS.Chapter10.mem_listInsert_self`,
  {lit}`CLRS.Chapter10.mem_listDeleteAll_iff`.
* 11.1 Direct-address tables:
  {lit}`CLRS.Chapter11.search_insert_same`,
  {lit}`CLRS.Chapter11.search_insert_other`,
  {lit}`CLRS.Chapter11.search_delete_same`,
  {lit}`CLRS.Chapter11.search_delete_other`.

## Partial

* 3.2 Standard functions:
  current results {lit}`CLRS.Chapter03.isLittleO_pow_pow`,
  {lit}`CLRS.Chapter03.isBigO_pow_pow`,
  {lit}`CLRS.Chapter03.isLittleO_pow_const_exp`,
  {lit}`CLRS.Chapter03.isLittleO_log_rpow`,
  {lit}`CLRS.Chapter03.isLittleO_log_pow_rpow`,
  {lit}`CLRS.Chapter03.isBigO_log_pow_rpow`,
  {lit}`CLRS.Chapter03.isLittleO_exp_exp_of_lt`,
  {lit}`CLRS.Chapter03.isEquivalent_harmonic_log`,
  {lit}`CLRS.Chapter03.isBigTheta_harmonic_log`,
  {lit}`CLRS.Chapter03.isBigTheta_nat_floor_coerce`,
  {lit}`CLRS.Chapter03.isBigTheta_nat_ceil_coerce`,
  {lit}`CLRS.Chapter03.isBigTheta_nat_floor_half_coerce`,
  {lit}`CLRS.Chapter03.isBigTheta_nat_ceil_half_coerce`,
  {lit}`CLRS.Chapter03.factorial_upper_bound`,
  {lit}`CLRS.Chapter03.factorial_lower_bound_offset`,
  {lit}`CLRS.Chapter03.factorial_lower_bound_half_pow`,
  {lit}`CLRS.Chapter03.isLittleO_exp_vs_factorial`, and
  {lit}`CLRS.Chapter03.isLittleO_factorial_pow_self`;
  remaining gap: add the full CLRS table of standard growth comparisons,
  especially remaining logarithm/exponential variants not yet wrapped with
  CLRS-facing theorem names.
* 11.2 Chained hash tables:
  current results {lit}`CLRS.Chapter11.hashSearch_hashInsert_self`,
  {lit}`CLRS.Chapter11.hashSearch_hashInsert_iff`,
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_self`,
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_iff`,
  {lit}`CLRS.Chapter11.uniformAverageFin_add`,
  {lit}`CLRS.Chapter11.uniformAverageFin_nonneg`,
  {lit}`CLRS.Chapter11.uniformAverageFin_indicator_singleton`,
  {lit}`CLRS.Chapter11.finiteHashLoadFactor_nonneg`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_eq_loadFactor`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_nonneg`,
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor`,
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_ge_one`,
  {lit}`CLRS.Chapter11.totalBucketLength_finiteHashInsert`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_finiteHashInsert`,
  {lit}`CLRS.Chapter11.finiteHashLoadFactor_finiteHashInsert`, and
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_finiteHashInsert`;
  remaining gap: lift the finite-uniform bucket abstraction to a probability
  model over random keys or random hash functions.
* 12.1 Binary search trees:
  current results {lit}`CLRS.Chapter12.BSTree.search_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_inTree`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.maximum?_inTree`,
  {lit}`CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.successor?_least_greater`,
  {lit}`CLRS.Chapter12.BSTree.successor?_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_isSome_iff_exists_greater`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_isSome_iff_exists_less`,
  {lit}`CLRS.Chapter12.BSTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter12.BSTree.search_insert_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.insert_ordered`,
  {lit}`CLRS.Chapter12.BSTree.inTree_delete_iff`,
  {lit}`CLRS.Chapter12.BSTree.delete_ordered`,
  {lit}`CLRS.Chapter12.BSTree.not_inTree_delete_self`,
  {lit}`CLRS.Chapter12.BSTree.delete_eq_self_of_not_inTree`,
  {lit}`CLRS.Chapter12.BSTree.search_delete_self_eq_false`,
  {lit}`CLRS.Chapter12.BSTree.search_delete_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_delete_eq_some_iff`,
  {lit}`CLRS.Chapter12.BSTree.successor?_delete_eq_none_iff`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_delete_eq_some_iff`, and
  {lit}`CLRS.Chapter12.BSTree.predecessor?_delete_eq_none_iff`;
  remaining gap: parent-pointer successor/predecessor procedures, transplant,
  and pointer-level mutation remain future section targets.
* 13.1 Red-black trees:
  current results {lit}`CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_rotateRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`,
  {lit}`CLRS.Chapter13.RBTree.noRedRed_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_repaintRoot`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_leftLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_leftRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_rightLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_rightRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_leftLeft`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_leftRight`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_rightLeft`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_rightRight`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftLeft`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftRight`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightLeft`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightRight`,
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_leftLeft_certificate`,
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_leftRight_certificate`,
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_rightLeft_certificate`, and
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_rightRight_certificate`;
  remaining gap: compose these local insertion-fixup certificates into the
  executable insertion algorithm; deletion fixup is not yet mechanized.
* 14.1 Order-statistic trees:
  current results {lit}`CLRS.Chapter14.OSTree.storedSize_eq_realSize_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.keys_recomputeSizes`,
  {lit}`CLRS.Chapter14.OSTree.keys_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.keys_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.realSize_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.realSize_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.storedSize_rotateLeft_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.storedSize_rotateRight_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.rotateLeft_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rotateRight_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_eq_rankSelect?_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateLeft_eq_rankSelect?_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateRight_eq_rankSelect?_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_recomputeSizes_eq_rankSelect?`,
  {lit}`CLRS.Chapter14.OSTree.realSize_recomputeSizes`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_recomputeSizes`,
  {lit}`CLRS.Chapter14.OSTree.rotateLeft_recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rotateRight_recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateLeft_recomputeSizes_eq_rankSelect?`, and
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateRight_recomputeSizes_eq_rankSelect?`;
  remaining gap: connect the functional rotations to red-black balancing,
  interval trees, and the general augmentation theorem.
* 15.1 Rod cutting:
  current results {lit}`CLRS.Chapter15.firstCutValue_le_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.rodRevenue_le_of_firstCutValue_bounds`,
  {lit}`CLRS.Chapter15.price_le_revenue_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.bottomUpRodRevenue_zero`,
  {lit}`CLRS.Chapter15.bottomUpRodRevenue_succ`,
  {lit}`CLRS.Chapter15.bottomUpRodRevenue_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.rodCutTableRecurrence_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.bottomUpRodRevenue_rodCutTableRecurrence`,
  {lit}`CLRS.Chapter15.firstCutValue_le_of_rodCutTableRecurrence`,
  {lit}`CLRS.Chapter15.rodTableValue_le_of_firstCutValue_bounds`,
  {lit}`CLRS.Chapter15.price_le_table_of_rodCutTableRecurrence`,
  {lit}`CLRS.Chapter15.planValue_le_table_of_rodCutTableRecurrence`,
  {lit}`CLRS.Chapter15.planValue_le_bottomUpRodRevenue`,
  {lit}`CLRS.Chapter15.planValue_le_revenue_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.planValue_le_optimalPlanValue_of_same_length`,
  {lit}`CLRS.Chapter15.planValue_le_tablePlanValue_of_same_length`, and
  {lit}`CLRS.Chapter15.planValue_le_bottomUpRodPlanValue_of_same_length`;
* 15.2 Matrix-chain multiplication:
  current results {lit}`CLRS.Chapter15.ChainPlan.start_le_end`,
  {lit}`CLRS.Chapter15.MatrixChainLowerBound`,
  {lit}`CLRS.Chapter15.MatrixChainSplitOptimal`,
  {lit}`CLRS.Chapter15.matrixChain_opt_le_planCost`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_eq`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_optimal`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_le_planCost`, and
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_eq_of_reconstructed`;
  remaining gap: concrete bottom-up cost-table construction and executable
  split reconstruction.
* 15.4 Longest common subsequence:
  current results {lit}`CLRS.Chapter15.IsCommonSubsequence`,
  {lit}`CLRS.Chapter15.LCSCertificate.commonSubsequence_length_le`,
  {lit}`CLRS.Chapter15.LCSCertificate.length_eq_of_certificates`, and
  {lit}`CLRS.Chapter15.isCommonSubsequence_comm`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons_self`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.diagonal_lt_cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.drop_left_le_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.drop_right_le_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.nil_left`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.nil_right`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_self`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.diagonal_lt_cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.drop_left_le_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.drop_right_le_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.commonSubsequence_length_le`,
  {lit}`CLRS.Chapter15.lcsTable_reconstruction_optimal`, and
  {lit}`CLRS.Chapter15.lcsCertificate_of_table_reconstruction_length`;
  remaining gap: concrete dynamic-programming length-table construction and
  executable reconstruction.
* Chapter 15 remaining target:
  optimal binary search trees are not yet represented.
* 17.1-17.4 Amortized analysis:
  current results {lit}`CLRS.Chapter17.aggregate_bound_of_prefix_bound`,
  {lit}`CLRS.Chapter17.accounting_totalCost_eq_totalCharge_sub_delta`,
  {lit}`CLRS.Chapter17.accounting_totalCost_le_totalCharge`,
  {lit}`CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta`,
  {lit}`CLRS.Chapter17.potential_totalCost_le_totalAmortized`,
  {lit}`CLRS.Chapter17.multiPop_totalCost_le`,
  {lit}`CLRS.Chapter17.binaryCounter_increment_potential_le_two`,
  {lit}`CLRS.Chapter17.binaryCounter_trace_potential_le`,
  {lit}`CLRS.Chapter17.binaryCounter_trace_totalFlips_le`,
  {lit}`CLRS.Chapter17.binaryCounter_totalFlips_le`,
  {lit}`CLRS.Chapter17.dynamicPotential_nonneg`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_potential_nonneg`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_potential_nonneg`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_pos`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_le_num_succ`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_of_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_of_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_ge_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_ge_double_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_valid`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_size_of_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_size_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_pos`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_gt`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_ge`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_pos`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_ge_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_ge_double_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_amortizedCost_eq`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_amortizedBound`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_pos_of_nonempty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_pos_iff_nonempty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_zero_iff_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_le_num`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_eq_num_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_eq_one_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_fits`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_le_size`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_le_half_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_valid`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_size`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_size_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_size_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_le`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_pos_of_one_lt`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_lt_of_nonempty`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_fits`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_pos_of_one_lt`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_le_size`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_le_half_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_amortizedCost_eq`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_amortizedBound`, and
  {lit}`CLRS.Chapter17.dynamicTable_amortizedBound`;
  remaining gap: mutable-array copying, RAM/allocation constants, and sharper
  CLRS load-factor potential refinements.
* 18.1-18.3 B-trees:
  current results {lit}`CLRS.Chapter18.BTree.search_correct`,
  {lit}`CLRS.Chapter18.BTree.search_true_iff`,
  {lit}`CLRS.Chapter18.BTree.search_true_of_mem`,
  {lit}`CLRS.Chapter18.BTree.mem_of_search_true`,
  {lit}`CLRS.Chapter18.BTree.search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.search_false_of_not_mem`,
  {lit}`CLRS.Chapter18.BTree.not_mem_of_search_false`,
  {lit}`CLRS.Chapter18.BTree.minKeys_zero`,
  {lit}`CLRS.Chapter18.BTree.minKeys_pos`,
  {lit}`CLRS.Chapter18.BTree.one_le_minKeys`,
  {lit}`CLRS.Chapter18.BTree.minKeys_lower_bound`,
  {lit}`CLRS.Chapter18.BTree.minKeys_succ`,
  {lit}`CLRS.Chapter18.BTree.minKeys_le_succ`,
  {lit}`CLRS.Chapter18.BTree.minKeys_monotone_height`,
  {lit}`CLRS.Chapter18.BTree.splitChild_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.splitChild_valid`,
  {lit}`CLRS.Chapter18.BTree.splitChild_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_mem_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_not_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_not_mem_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_of_mem`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_false_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_false_of_not_mem`,
  {lit}`CLRS.Chapter18.BTree.insert_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.insert_valid`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_search_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_self`,
  {lit}`CLRS.Chapter18.BTree.insert_search_self`,
  {lit}`CLRS.Chapter18.BTree.insert_search_of_eq`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_old`,
  {lit}`CLRS.Chapter18.BTree.insert_search_old`,
  {lit}`CLRS.Chapter18.BTree.insert_search_of_mem`,
  {lit}`CLRS.Chapter18.BTree.insert_not_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_not_mem_of_ne`,
  {lit}`CLRS.Chapter18.BTree.insert_search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_search_false_of_ne`,
  {lit}`CLRS.Chapter18.BTree.insert_search_false_of_not_mem_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.delete_valid`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_iff_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_search_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_search_iff_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem`,
  {lit}`CLRS.Chapter18.BTree.delete_search_deleted_false`,
  {lit}`CLRS.Chapter18.BTree.delete_search_false_of_eq`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_of_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_of_ne_prop`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_ne_prop`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_mem_ne`,
  {lit}`CLRS.Chapter18.BTree.delete_search_of_mem_ne_prop`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem_old`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem_of_eq`,
  {lit}`CLRS.Chapter18.BTree.delete_search_false_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_search_false_old`, and
  {lit}`CLRS.Chapter18.BTree.delete_search_false_of_not_mem`;
  remaining gap: full occupancy/separator/same-depth invariants, node-level
  deletion repair, and disk-page/mutation semantics.
* 19.1 Fibonacci heaps:
  current results {lit}`CLRS.Chapter19.FibHeap.makeHeap_correct`,
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_valid`,
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_minimum_none`,
  {lit}`CLRS.Chapter19.FibHeap.potential_makeHeap`,
  {lit}`CLRS.Chapter19.FibHeap.potential_nonneg`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_le`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_ne_none_of_nonempty`,
  {lit}`CLRS.Chapter19.FibHeap.insert_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_valid`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_self`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.insert_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_le_inserted`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_ne_none`,
  {lit}`CLRS.Chapter19.FibHeap.union_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_valid`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_right`,
  {lit}`CLRS.Chapter19.FibHeap.union_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_not_mem_of_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_le_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_le_right`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_right`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_valid`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_ne_none_of_nonempty`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_of_all_eq`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne_none_of_remaining`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_valid`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_new`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_oldKey_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_oldKey_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_new`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_ne_none`,
  {lit}`CLRS.Chapter19.FibHeap.delete_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_valid`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_of_eq`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_ne`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_none_of_all_eq`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_ne_none_of_remaining`,
  {lit}`CLRS.Chapter19.FibHeap.heapPotential_telescope`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_step`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_pos`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_le_succ`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_monotone`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_add_two_ge_double`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_even_lower_bound`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_half_lower_bound`,
  {lit}`CLRS.Chapter19.FibHeap.degreeIndex_half_le_log_card`,
  {lit}`CLRS.Chapter19.FibHeap.degreeIndex_le_twice_log_card_add_one`, and
  {lit}`CLRS.Chapter19.FibHeap.degree_bound_log`;
  remaining gap: pointer handles, cascading cuts, consolidation arrays, and
  the subtree-size induction leading to the true Fibonacci logarithmic degree
  proof.
* 20.1-20.2 van Emde Boas trees:
  current results {lit}`CLRS.Chapter20.VEB.index_high_low`,
  {lit}`CLRS.Chapter20.VEB.high_index`,
  {lit}`CLRS.Chapter20.VEB.low_index`,
  {lit}`CLRS.Chapter20.VEB.index_lt`,
  {lit}`CLRS.Chapter20.VEB.high_lt`,
  {lit}`CLRS.Chapter20.VEB.low_lt`,
  {lit}`CLRS.Chapter20.VEB.member_correct`,
  {lit}`CLRS.Chapter20.VEB.member_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.minimum_mem`,
  {lit}`CLRS.Chapter20.VEB.minimum_le`,
  {lit}`CLRS.Chapter20.VEB.minimum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.minimum_none_of_empty`,
  {lit}`CLRS.Chapter20.VEB.minimum_ne_none_of_nonempty`,
  {lit}`CLRS.Chapter20.VEB.maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.maximum_mem`,
  {lit}`CLRS.Chapter20.VEB.le_maximum`,
  {lit}`CLRS.Chapter20.VEB.maximum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.maximum_none_of_empty`,
  {lit}`CLRS.Chapter20.VEB.maximum_ne_none_of_nonempty`,
  {lit}`CLRS.Chapter20.VEB.successor_correct`,
  {lit}`CLRS.Chapter20.VEB.successor_mem`,
  {lit}`CLRS.Chapter20.VEB.successor_gt`,
  {lit}`CLRS.Chapter20.VEB.successor_le`,
  {lit}`CLRS.Chapter20.VEB.successor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.successor_none_of_no_gt`,
  {lit}`CLRS.Chapter20.VEB.successor_ne_none_of_exists_gt`,
  {lit}`CLRS.Chapter20.VEB.predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.predecessor_mem`,
  {lit}`CLRS.Chapter20.VEB.predecessor_lt`,
  {lit}`CLRS.Chapter20.VEB.le_predecessor`,
  {lit}`CLRS.Chapter20.VEB.predecessor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.predecessor_none_of_no_lt`,
  {lit}`CLRS.Chapter20.VEB.predecessor_ne_none_of_exists_lt`,
  {lit}`CLRS.Chapter20.VEB.insert_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_member_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_member_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_member_self`,
  {lit}`CLRS.Chapter20.VEB.insert_member_old`,
  {lit}`CLRS.Chapter20.VEB.insert_member_false_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_member_false_of_ne`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_mem`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_mem_old_of_ne`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_le_inserted`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_le_old`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_ne_none`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_mem`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_mem_old_of_ne`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_inserted_le`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_old_le`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_ne_none`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_mem`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_mem_old_of_ne`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_gt`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_le`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_none_of_no_gt`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_none_of_insert_le_old_no_gt`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_ne_none_of_insert_gt`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_ne_none_of_old_gt`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_mem`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_mem_old_of_ne`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_lt`,
  {lit}`CLRS.Chapter20.VEB.insert_le_predecessor`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_none_of_no_lt`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_none_of_query_le_insert_old_no_lt`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_ne_none_of_insert_lt`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_ne_none_of_old_lt`,
  {lit}`CLRS.Chapter20.VEB.delete_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_member_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_member_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_member_deleted_false`,
  {lit}`CLRS.Chapter20.VEB.delete_member_of_ne`,
  {lit}`CLRS.Chapter20.VEB.delete_member_false_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_member_false_old`,
  {lit}`CLRS.Chapter20.VEB.delete_member_false_of_eq`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_ne`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_mem`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_le_old`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_none_of_all_eq`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_ne_none_of_remaining`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_ne`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_mem`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_old_le`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_none_of_all_eq`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_ne_none_of_remaining`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_mem`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_gt`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_le`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_none_of_no_gt`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_none_of_old_no_gt`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_ne_none_of_remaining_gt`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_mem`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_lt`,
  {lit}`CLRS.Chapter20.VEB.delete_le_predecessor`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_lt_univ`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_none_of_no_lt`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_none_of_old_no_lt`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_ne_none_of_remaining_lt`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_zero`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_succ`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_linear`,
  {lit}`CLRS.Chapter20.VEB.operationDepth_monotone`, and
  {lit}`CLRS.Chapter20.VEB.operationDepth_strict_mono`;
  remaining gap: recursive summary/cluster state, word-RAM base cases, and the
  explicit {lit}`O(log log u)` asymptotic bridge.
* 23.1 Growing a minimum spanning tree:
  current results {lit}`CLRS.MST.Graph.connected_crosses_cut`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`, and
  {lit}`CLRS.MST.safe_edge_of_lightest_crossing`;
  remaining gap: Section 23.2 proves replacement from an explicit
  {lit}`ExchangePath`; the next step is deriving that certificate automatically
  from a canonical finite simple path or cycle representation.
* 23.2 Kruskal and Prim:
  current results {lit}`CLRS.MST.Graph.ExchangePath`,
  {lit}`CLRS.MST.Graph.InsertedEdgeConnection`,
  {lit}`CLRS.MST.Graph.exchangePath_connected_insert`,
  {lit}`CLRS.MST.Graph.insertedEdgeConnection_of_exchangePath`,
  {lit}`CLRS.MST.Graph.exchangePath_of_insert_connected`,
  {lit}`CLRS.MST.Graph.exchangePath_iff_insertedEdgeConnection`,
  {lit}`CLRS.MST.FiniteGraph.exchangePath_of_insert_connects_erased_edge`,
  {lit}`CLRS.MST.FiniteGraph.exchangePath_iff_insertedEdgeConnection_of_spanningTree`,
  {lit}`CLRS.MST.FiniteGraph.spanningTree_exchange_of_path_certificate`,
  {lit}`CLRS.MST.FiniteGraph.cut_exchange_certificate`,
  {lit}`CLRS.MST.FiniteGraph.exists_replacement_spanning_tree_of_cut`,
  {lit}`CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing`,
  {lit}`CLRS.MST.lightest_crossing_of_sorted_prefix`,
  {lit}`CLRS.MST.cut_certificate_of_component_oracle_sorted_prefix`,
  {lit}`CLRS.MST.processed_edge_mem_or_connected_of_exact_component_kruskal`,
  {lit}`CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`,
  {lit}`CLRS.MST.lightest_crossing_of_exact_component_kruskal_prefix`,
  {lit}`CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_subset_edges`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_forest_of_exact_component`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_spans_of_complete_exact_component`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`,
  {lit}`CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_cycle_test`, and
  {lit}`CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_complete_exact_component_empty`;
  remaining gap: refine exact components to executable union-find if needed,
  derive the inserted-edge connection automatically from a canonical finite
  simple path/cycle API, discharge the prefix-local sorted-lightness proof in the full
  recursive optimality wrapper, and add Prim's theorem interface.

## Deferred or Blocked

* Union-find correctness: {lit}`deferred-implementation`.
  Reason: not needed for the mathematical MST proof.
* Automatic MST exchange-path extraction: {lit}`blocked-design`.
  Reason: the cut-crossing tree-edge, prefix-preservation lemma, and
  certificate-based replacement spanning-tree theorem are proved; deriving
  the inserted-edge connection automatically still needs a stable finite simple
  path/cycle API.
* Full RAM semantics: {lit}`future-work`.
  Reason: requires a separate imperative machine and cost model.
* Chapter 4 full Master Theorem instantiation:
  {lit}`future-work`.
  Reason: exact powers, floor/ceiling exact-power extraction, the generic
  all-input transfer bridge, and adjacent-power sandwich generation from
  one-step comparison-scale bounds are proved; the discrete
  {lit}`criticalPowerScale`, {lit}`criticalPowerLogScale`, and
  {lit}`tailDominatedScale` all-input
  wrappers are also proved, including floor/ceiling recurrence packaging for
  exact-power Master cases 1, 2, and 3.  The real-log comparison bridge for
  the critical-power scale is proved, and the real-log-log comparison bridge
  for the case-2 scale is proved; what remains is the case-3 forcing
  comparison scale.
* Chapter 4 Strassen recursive refinement:
  {lit}`future-work`.
  Reason: the 2 by 2 block algebra is proved; recursive splitting,
  dimension bookkeeping, and runtime analysis remain separate refinements.
* Chapter 4 maximum-subarray runtime analysis: {lit}`future-work`.
  Reason: the exhaustive-search specification, crossing-helper optimality,
  executable left/right/crossing combine step, and recursive split-tree/fuelled
  selector correctness are proved; the runtime recurrence and RAM-cost
  refinement remain future work.
* Chapter 6 priority-queue RAM costs: {lit}`deferred-implementation`.
  Reason: the functional heap specification, recursive {lit}`MAX-HEAPIFY`
  repair, bottom-up {lit}`BUILD-MAX-HEAP` refinement, in-place heapsort loop
  scaffold, exact-shrink invariant, loop permutation/length facts, root-to-
  suffix-head step theorem, shrinking-prefix sorted-suffix invariant
  preservation, bundled state-correctness theorem, and in-place
  sortedness proof are proved; array-level {lit}`HEAP-MAXIMUM`, full fuelled
  {lit}`HEAP-INCREASE-KEY`, {lit}`HEAP-EXTRACT-MAX`, and index-based
  {lit}`HEAP-DELETE` state correctness are also proved.  The remaining
  implementation layer is the line-by-line RAM-cost model.
* Chapter 7 mutable-array partition and probability refinements:
  {lit}`future-work`.
  Reason: Sections 7.1-7.3 prove the pure partition/quicksort correctness
  spine, a scan-state partition-loop invariant, a returned pivot-index wrapper
  with an adjacent-swap trace, deterministic comparison-count bounds, and the
  expected-comparison recurrence with harmonic bounds.  The harder refinements
  are the index-level CLRS array {lit}`PARTITION` loop and an explicit
  probability-space interpretation for random pivot choices.
* Chapter 4 concrete all-input Master-theorem instantiations: {lit}`future-work`.
  Reason: the discrete critical-power, log-critical, and tail-dominated scales
  now have all-input wrappers for cases 1, 2, and 3, and the natural-exponent
  special case {lit}`a = b^p` has polynomial and polynomial-log wrappers for
  cases 1 and 2.  The real-log bridge
  {lit}`criticalPowerScale_isBigTheta_realLogScale` is proved, and case 1 now
  has named exact/floor/ceiling wrappers stated directly against
  {lit}`realLogScale`; case 2 also has a named
  {lit}`criticalPowerLogScale_isBigTheta_realLogLogScale` bridge and
  exact/floor/ceiling wrappers stated directly against
  {lit}`realLogLogScale`.  The remaining comparison work is the case-3 forcing
  scale.
* General merge-sort recurrence: {lit}`future-work`.
  Reason: needs floor and ceiling arithmetic for all input sizes.
* CLRS exercises and chapter-end problems: {lit}`future-work`.
  Reason: kept separate from the first main-theorem pass.

## Reader Contract

The status table is intentionally conservative.  A section is not marked
{lit}`proved` merely because the algorithm idea is clear; it needs a named Lean
theorem that compiles for the stated model.  A section marked {lit}`partial` should
say exactly which mathematical or representation layer remains.
-/
