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
  proved.
* Chapter 5, Section 5.1: the hiring problem is proved in the finite
  rank-symmetry model.
* Chapter 6, Sections 6.1-6.5: the indexed array heap layer, recursive
  {lit}`MAX-HEAPIFY`, bottom-up {lit}`BUILD-MAX-HEAP`, in-place heapsort
  sorted-suffix invariant, top-level heapsort correctness, and array-level
  priority-queue state theorems are proved.
* Chapter 7, Section 7.1: stable functional partition classification,
  scan-state partition-loop correctness, a returned pivot-index partition
  wrapper with an explicit adjacent-swap trace, and functional quicksort
  sortedness/permutation preservation are proved.
* Chapter 8, Sections 8.2-8.4: stable counting-sort bucket correctness,
  abstract radix-sort correctness plus complete digit-signature stability from
  stable digit passes, a concrete base-{lit}`b` natural-key radix wrapper, a
  key-order correctness wrapper with the bounded fixed-width arithmetic bridge
  discharged, and deterministic bucket-sort correctness are proved.
* Chapter 9, Sections 9.2-9.3: selection-by-rank correctness is proved for the
  specification selector, a pivot-style quickselect model, and a
  pivot-parametric deterministic SELECT model with a count-based
  order-statistic certificate; the median-of-medians pivot/select wrapper, the
  local five-element median certificate, executable five-element grouping plus
  the grouped split-count core for the median-of-medians argument, and the
  CLRS-style partition-size bound are also proved.
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
  {lit}`a = b^p`.  The general {lit}`n^(log_b a)` and case-3 comparison
  layers, plus selected runtime refinements, remain.
* Chapter 11, Section 11.2: deterministic chained-hash-table operations are
  proved for a fixed hash function; expected-time hashing remains.
* Chapter 12, Section 12.1: functional BST operations are proved; parent
  pointers, transplant, and mutation remain.
* Chapter 13, Section 13.1: local red-black rotation/recoloring invariants are
  proved; full insertion and deletion fixup algorithms remain.
* Chapter 17, Sections 17.1-17.4: finite-prefix aggregate/accounting/potential
  theorems plus {lit}`MULTIPOP`, executable binary-counter one-step potential
  bound, executable multi-step counter trace bounds, and size-level
  dynamic-table potential nonnegativity, capacity feasibility/direction facts,
  stored-count direction facts, actual-cost case specs and upper bounds,
  post-state capacity corollaries, and insertion/deletion wrappers are proved;
  allocator and RAM refinements remain.
* Chapter 18, Sections 18.1-18.3: a mathematical B-tree model has search,
  minimum-key height-expression recurrence and monotonicity, split-child preservation,
  split-child direct membership/search preservation, insertion/deletion membership, and
  search-after-update theorem surfaces plus direct inserted/deleted-key and
  old-key query preservation corollaries; full separator/same-depth,
  node-level-deletion, and disk-page refinements remain.
* Chapter 19, Section 19.1: abstract Fibonacci-heap finite-set operations,
  empty-heap construction, empty-result query specs, direct
  insert/union/extract-min/decrease-key/delete membership facts plus
  operation-key and old-key preservation membership corollaries,
  minimum-after-update positive/empty specifications, heap-potential
  zero/nonnegativity and telescoping facts, and Fibonacci
  lower-bound recurrence/positivity/monotonicity and even/half-index
  power-of-two growth facts plus conditional degree-to-log wrappers are
  proved; pointer
  handles, cascading cuts, and the true Fibonacci logarithmic degree theorem
  remain.
* Chapter 20, Sections 20.1-20.2: vEB high/low/index arithmetic, bounded
  recomposition facts, and finite-set operation specs, including
  extrema/successor/predecessor positive and empty-result cases plus
  membership-, extrema-, and neighbor-query-after-update positive/no-neighbor
  specs, extrema empty-after-update specs, direct member-query preservation
  corollaries, and operation-depth recurrence/monotonicity specs, are proved;
  recursive cluster representation and the {lit}`O(log log u)` bridge remain.
* Chapter 23, Sections 23.1-23.2: the cut property, safe-edge theorem,
  exact-component Kruskal scan facts, forest/spanning wrappers, and
  certificate-based Kruskal optimality interfaces exist; automatic simple
  path/cycle exchange extraction, fully prefix-local sorted-lightness wrapping,
  and Prim remain.

### Missing Core Theorem

* Chapter 4 full Master-theorem instantiation: extend the comparison-scale
  layer beyond the proved natural-exponent case-1 and case-2 wrappers to the
  general all-input floor/ceiling Master cases.
* Chapter 7, Sections 7.2-7.4: index-level mutable-array partition refinement,
  performance recurrence, randomized quicksort, and expected-time theorem.
* Chapter 9 linear-time SELECT refinements: pivot-parametric deterministic
  SELECT, the local five-element median certificate, executable grouping, and
  the grouped/full-input split-count core plus {lit}`7n/10` partition-size
  packaging are proved; randomized expected time and the runtime theorem
  remain.
* Chapter 11 expected hashing analysis: expected-time theorem under a formal
  probability model.
* Chapter 12 pointer-level BST layer: CLRS parent-pointer procedures,
  transplant, and mutation refinement.
* Chapter 13 full red-black algorithms: insertion/deletion fixup correctness
  and height theorem.
* Chapters 14-15 and 21-22: not yet represented.
* Chapter 23 Prim: theorem interface and proof have not been added.
* Chapter 24 onward: not yet represented.

Near-term rule: do not return to a completed main-proof area, especially
Chapter 6, without a concrete audit or refinement target.  The next
proof-heavy targets are Chapter 4 all-input recurrence bridging, Chapter 23
exchange-path automation, and remaining Chapter 8/9 algorithm refinements.

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
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_criticalPowerScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_criticalPowerScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_criticalPowerScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_polynomialScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_polynomialScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_polynomialScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase2_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase2_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase2_criticalPowerLogScale`,
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
  {lit}`CLRS.Chapter08.bucketSortBy_correct`, and
  {lit}`CLRS.Chapter08.bucketSortByRank_correct`.
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
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_self`, and
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_iff`;
  remaining gap: expected search time under simple uniform hashing needs a
  probability model over keys or hash functions.
* 12.1 Binary search trees:
  current results {lit}`CLRS.Chapter12.BSTree.search_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_inTree`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.maximum?_inTree`,
  {lit}`CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  {lit}`CLRS.Chapter12.BSTree.successor?_least_greater`,
  {lit}`CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  {lit}`CLRS.Chapter12.BSTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter12.BSTree.insert_ordered`,
  {lit}`CLRS.Chapter12.BSTree.inTree_delete_iff`, and
  {lit}`CLRS.Chapter12.BSTree.delete_ordered`;
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
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`, and
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_black`;
  remaining gap: full RB insertion/deletion fixup algorithms are not yet
  mechanized.
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
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_le_num_succ`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_of_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_ge_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_valid`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_gt`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_ge`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_ge_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_amortizedBound`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_le_num`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_fits`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_le_size`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_valid`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_le`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_lt_of_nonempty`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_fits`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_le_size`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_amortizedBound`, and
  {lit}`CLRS.Chapter17.dynamicTable_amortizedBound`;
  remaining gap: mutable-array copying, RAM/allocation constants, and sharper
  CLRS load-factor potential refinements.
* 18.1-18.3 B-trees:
  current results {lit}`CLRS.Chapter18.BTree.search_correct`,
  {lit}`CLRS.Chapter18.BTree.minKeys_lower_bound`,
  {lit}`CLRS.Chapter18.BTree.minKeys_succ`,
  {lit}`CLRS.Chapter18.BTree.minKeys_le_succ`,
  {lit}`CLRS.Chapter18.BTree.minKeys_monotone_height`,
  {lit}`CLRS.Chapter18.BTree.splitChild_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.splitChild_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_mem_old`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_iff`,
  {lit}`CLRS.Chapter18.BTree.splitChild_search_old`,
  {lit}`CLRS.Chapter18.BTree.insert_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_search_iff`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_self`,
  {lit}`CLRS.Chapter18.BTree.insert_search_self`,
  {lit}`CLRS.Chapter18.BTree.insert_mem_old`,
  {lit}`CLRS.Chapter18.BTree.insert_search_old`,
  {lit}`CLRS.Chapter18.BTree.delete_preserves_model`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_search_iff`,
  {lit}`CLRS.Chapter18.BTree.delete_not_mem`,
  {lit}`CLRS.Chapter18.BTree.delete_search_deleted_false`,
  {lit}`CLRS.Chapter18.BTree.delete_mem_of_ne`, and
  {lit}`CLRS.Chapter18.BTree.delete_search_of_ne`;
  remaining gap: full occupancy/separator/same-depth invariants, node-level
  deletion repair, and disk-page/mutation semantics.
* 19.1 Fibonacci heaps:
  current results {lit}`CLRS.Chapter19.FibHeap.makeHeap_correct`,
  {lit}`CLRS.Chapter19.FibHeap.potential_makeHeap`,
  {lit}`CLRS.Chapter19.FibHeap.potential_nonneg`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_self`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_right`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_new`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_none_iff`,
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
  {lit}`CLRS.Chapter20.VEB.minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.successor_correct`,
  {lit}`CLRS.Chapter20.VEB.successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_member_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_member_self`,
  {lit}`CLRS.Chapter20.VEB.insert_member_old`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.insert_predecessor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_member_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_member_deleted_false`,
  {lit}`CLRS.Chapter20.VEB.delete_member_of_ne`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_minimum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_maximum_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_successor_none_iff`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_correct`,
  {lit}`CLRS.Chapter20.VEB.delete_predecessor_none_iff`,
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
  exact-power Master cases 1, 2, and 3.  Analytic comparison scales still need
  to be packaged for the textbook-facing statements.
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
* Chapter 7 mutable-array partition and randomized analysis: {lit}`future-work`.
  Reason: Section 7.1 now proves the pure partition/quicksort correctness
  spine, a scan-state partition-loop invariant, and a returned pivot-index
  wrapper with an adjacent-swap trace; the harder refinements are the
  index-level CLRS array {lit}`PARTITION` loop, recurrence analysis, randomized
  quicksort, and expected running time.
* Chapter 4 concrete all-input Master-theorem instantiations: {lit}`future-work`.
  Reason: the discrete critical-power, log-critical, and tail-dominated scales
  now have all-input wrappers for cases 1, 2, and 3, and the natural-exponent
  special case {lit}`a = b^p` has polynomial and polynomial-log wrappers for
  cases 1 and 2.  The remaining comparison work is the general
  {lit}`n^(log_b a)` layer, real-log packaging, and the case-3 forcing scale.
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
