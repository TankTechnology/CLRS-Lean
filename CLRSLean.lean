import CLRSLean.Chapter_01
import CLRSLean.Chapter_02
import CLRSLean.Chapter_03
import CLRSLean.Chapter_04
import CLRSLean.Chapter_05
import CLRSLean.Chapter_06
import CLRSLean.Chapter_07
import CLRSLean.Chapter_08
import CLRSLean.Chapter_09
import CLRSLean.Chapter_10
import CLRSLean.Chapter_11
import CLRSLean.Chapter_12
import CLRSLean.Chapter_13
import CLRSLean.Chapter_14
import CLRSLean.Chapter_15
import CLRSLean.Chapter_16
import CLRSLean.Chapter_23
import CLRSLean.Progress
import CLRSLean.Status
import CLRSLean.Workflow

/-!
# CLRS-Lean

CLRS-Lean is a Lean 4 companion to CLRS-style algorithm proofs.  The project is
organized as a readable online book: each chapter has a short guide page, and
each selected textbook section has a literate Lean page containing the formal
model, the public theorem interface, and the proof.

## Project Aim

The goal is not to mechanically translate pseudocode line by line.  The first
target is the mathematical proof content of the textbook: loop invariants,
exchange arguments, cut properties, recurrences, and optimal-substructure
claims.  Low-level implementation proofs, such as union-find or heap
correctness, are added only when they are needed for the main theorem.

This keeps the site useful for three kinds of readers:

* algorithm readers who want the proof idea before reading Lean code;
* Lean readers who want stable theorem names and proof patterns;
* contributors who need an honest map of what is proved, partial, or deferred.

## Reading Route

Start with the chapter pages in the sidebar.

* Chapter 1 - Algorithms: the project reading contract and the way CLRS-Lean
  turns textbook claims into Lean definitions plus theorems.
* Chapter 2 - Getting Started: sorting correctness, a lightweight runtime bound,
  and a merge-sort recurrence.
* Chapter 3 - Growth of Functions: CLRS-style wrappers around Mathlib
  asymptotics plus selected standard growth facts.
* Chapter 4 - Divide-and-Conquer: maximum-subarray specification correctness,
  recurrence proof infrastructure for the substitution and recursion-tree
  methods, Strassen's 2 by 2 block algebra correctness, plus the proved
  exact-power Master method core, floor/ceiling exact-power extraction, and
  all-input transfer bridge with adjacent-power sandwich generation, discrete
  Master-scale wrappers, natural-exponent polynomial wrappers for Master cases
  1 and 2, the real-log bridge from {lit}`a^(⌊log_b n⌋)` to
  {lit}`n^(log_b a)`, and named case-1/case-2 wrappers in textbook
  {lit}`n^(log_b a)` and {lit}`n^(log_b a) log n` scales.
* Chapter 5 - Probabilistic Analysis: the finite rank-symmetry proof for the
  hiring problem and its logarithmic expected-hires bound.
* Chapter 6 - Heapsort: recursive {lit}`MAX-HEAPIFY` repair, bottom-up
  {lit}`BUILD-MAX-HEAP`, the in-place heapsort loop with a proved sorted-suffix
  invariant and sortedness theorem, an indexed array heap proof spine, and
  priority-queue operation specifications.
* Chapter 7 - Quicksort: stable functional partition classification,
  scan-state partition-loop correctness, a returned pivot-index partition
  wrapper with an explicit adjacent-swap trace, functional quicksort
  sortedness/permutation preservation, a deterministic quadratic
  comparison-count bound, and the expected-comparison recurrence with harmonic
  bounds for the current randomized-quicksort model.
* Chapter 8 - Sorting in Linear Time: stable counting-sort bucket correctness,
  abstract radix-sort correctness and complete digit-signature stability from
  stable digit passes, a concrete base-{lit}`b` digit wrapper for natural-key
  radix sort, a key-order correctness wrapper with the one-digit arithmetic
  case discharged, deterministic bucket-sort correctness, and the
  finite-uniform collision/second-moment core for bucket-sort expected time.
* Chapter 9 - Medians and Order Statistics: selection-by-rank correctness for
  the specification selector, pivot-style quickselect, and pivot-parametric
  deterministic SELECT via a count-based order-statistic certificate, plus an
  executable median-of-medians pivot/select wrapper, the local five-element
  median certificate, executable five-element grouping, median-of-medians
  partition-size bounds, and the abstract linear recurrence wrapper.
* Chapter 10 - Elementary Data Structures: functional stack, queue, and
  linked-list operation proofs.
* Chapter 11 - Hash Tables: direct-address table correctness, deterministic
  chained-hash-table insert/delete/search facts, and a finite-uniform bucket
  interface proving expected chain length equals the load factor.
* Chapter 12 - Binary Search Trees: search, minimum/maximum, insertion,
  complete functional successor/predecessor specifications, Boolean search
  wrappers after insertion/deletion, and functional deletion correctness for an
  inductive BST model.
* Chapter 13 - Red-Black Trees: local rotation, recoloring, red-red repair,
  four insertion-fixup case certificates, and red-black shape invariant lemmas.
* Chapter 14 - Augmenting Data Structures: order-statistic tree size
  augmentation, size/rank-preserving local rotations, and rank-selection
  correctness for the current functional model.
* Chapter 15 - Dynamic Programming: rod-cutting Bellman recurrence facts,
  matrix-chain parenthesization optimality plus split-table reconstruction, and
  LCS certificate optimality plus table-recurrence reconstruction certificates
  and recurrence wrappers.
* Chapter 16 - Greedy Algorithms: activity-selection exchange infrastructure
  and the complete Huffman optimality proof, currently the flagship greedy case
  study.
* Chapter 23 - Minimum Spanning Trees: the MST cut property, the mathematical
  Kruskal skeleton, and finite-graph MST wrappers.
* Progress Dashboard: a compact, generated chapter-by-chapter view of current
  coverage, backed by {lit}`docs/clrs-proof-progress.csv`.
* Proof Status: a planning board plus a compact ledger of proved, partial,
  blocked, and deferred work.
* Workflow: the contribution loop for adding or strengthening a CLRS section.

## Current Coverage

* Chapter 1: {lit}`expository`.
  No theorem target; this page explains the project conventions.
* 2.1 Insertion sort: {lit}`proved`.
  Public results: {lit}`CLRS.Chapter02.insertionSort_sorted`,
  {lit}`CLRS.Chapter02.insertionSort_perm`.
* 2.2 Analyzing algorithms: {lit}`proved`.
  Public result: {lit}`CLRS.Chapter02.insertionSortWorstComparisons_quadratic`.
* 2.3 Designing algorithms: {lit}`proved`.
  Public results: {lit}`CLRS.Chapter02.mergeSort_sortedLE`,
  {lit}`CLRS.Chapter02.mergeSort_perm`,
  {lit}`CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`.
* 3.1 Asymptotic notation: {lit}`proved`.
  Public results: {lit}`CLRS.Chapter03.isBigO_iff`,
  {lit}`CLRS.Chapter03.isLittleO_iff`,
  {lit}`CLRS.Chapter03.isBigTheta_trans`.
* 3.2 Standard functions: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter03.isLittleO_pow_pow`,
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
  {lit}`CLRS.Chapter03.isLittleO_exp_vs_factorial`,
  {lit}`CLRS.Chapter03.isLittleO_factorial_pow_self`.
* 4.1 Maximum subarray: {lit}`proved` for the exhaustive-search specification,
  crossing helper, and left/right/crossing combine interface.
  Public results: {lit}`CLRS.Chapter04.mem_nonemptySubarrays_iff`,
  {lit}`CLRS.Chapter04.bestCandidate_correct`,
  {lit}`CLRS.Chapter04.mem_crossingSubarrays_iff`,
  {lit}`CLRS.Chapter04.maxCrossingSubarray_correct`,
  {lit}`CLRS.Chapter04.maxCrossingSubarray_isNonemptySubarray_append`,
  {lit}`CLRS.Chapter04.subarray_append_left_or_right_or_crossing`,
  {lit}`CLRS.Chapter04.subarray_append_optimal_of_cases`,
  {lit}`CLRS.Chapter04.maxSubarray_exists_of_ne_nil`,
  {lit}`CLRS.Chapter04.maxSubarray_correct`.
* 4.2 Strassen's algorithm: {lit}`proved` for 2 by 2 block algebra.
  Public result: {lit}`CLRS.Chapter04.strassen2x2_correct`.
* 4.3 Substitution method: {lit}`proved` for one-step recurrence bounds.
  Public results: {lit}`CLRS.Chapter04.substitution_upper_bound`,
  {lit}`CLRS.Chapter04.substitution_lower_bound`,
  {lit}`CLRS.Chapter04.linear_substitution_upper_bound`,
  {lit}`CLRS.Chapter04.geometric_substitution_upper_bound`.
* 4.4 Recursion-tree method: {lit}`proved` for additive level-cost expansions.
  Public results: {lit}`CLRS.Chapter04.recursion_tree_additive_unroll`,
  {lit}`CLRS.Chapter04.recursion_tree_additive_upper_envelope`,
  {lit}`CLRS.Chapter04.recursion_tree_constant_level_cost`.
* 4.5 Master method: {lit}`proved` for exact-power recurrences.
  Public results: {lit}`CLRS.Chapter04.master_case1_geometric`,
  {lit}`CLRS.Chapter04.master_case2_constant_forcing`,
  {lit}`CLRS.Chapter04.master_case3_tail_dominated`.
* 4.6 Proof of the master theorem: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter04.FloorDivideRecurrence`,
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
  {lit}`CLRS.Chapter04.criticalPowerScale`, and
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_criticalPowerScale`,
  {lit}`CLRS.Chapter04.criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.tailDominatedScale`,
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_tailDominatedScale`,
  {lit}`CLRS.Chapter04.polynomialScale`,
  {lit}`CLRS.Chapter04.polynomialLogScale`,
  {lit}`CLRS.Chapter04.criticalPowerScale_isBigTheta_polynomialScale`,
  {lit}`CLRS.Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale`,
  {lit}`CLRS.Chapter04.realLogExponent`,
  {lit}`CLRS.Chapter04.realLogScale`,
  {lit}`CLRS.Chapter04.criticalPowerScale_isBigTheta_realLogScale`,
  {lit}`CLRS.Chapter04.realLogLogScale`,
  {lit}`CLRS.Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale`,
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_criticalPowerScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_criticalPowerScale`, and
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_criticalPowerScale`;
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_realLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_realLogScale`, and
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_realLogScale`;
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase1_polynomialScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase1_polynomialScale`, and
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase1_polynomialScale`;
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase2_criticalPowerLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase2_criticalPowerLogScale`,
  and {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase2_criticalPowerLogScale`;
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase2_realLogLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase2_realLogLogScale`, and
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase2_realLogLogScale`;
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase2_polynomialLogScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase2_polynomialLogScale`, and
  {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase2_polynomialLogScale`;
  {lit}`CLRS.Chapter04.exactPower_allInput_masterCase3_tailDominatedScale`,
  {lit}`CLRS.Chapter04.floorDivide_allInput_masterCase3_tailDominatedScale`,
  and {lit}`CLRS.Chapter04.ceilDivide_allInput_masterCase3_tailDominatedScale`.
  Remaining target: the case-3 comparison scale for the forcing-dominated
  Master statement.
* 5.1 Hiring problem: {lit}`proved` for the finite rank-symmetry model.
  Public results: {lit}`CLRS.Chapter05.hireProbability_eq`,
  {lit}`CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`,
  {lit}`CLRS.Chapter05.expectedHires_isBigTheta_log`.
* 6.1 Heaps: {lit}`proved` for the indexed heap predicate and root maximum.
  Public results: {lit}`CLRS.Chapter06.parent_lt_self`,
  {lit}`CLRS.Chapter06.eq_left_or_right_parent`,
  {lit}`CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`,
  {lit}`CLRS.Chapter06.orderedDesc_arrayMaxHeap`.
* 6.2 Maintaining the heap property: {lit}`proved` for fuelled {lit}`MAX-HEAPIFY`
  recursive repair.
  Public results: {lit}`CLRS.Chapter06.swapAt_perm`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_perm`,
  {lit}`CLRS.Chapter06.valAt_i_le_maxChildIndex`,
  {lit}`CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_swap_branch_repair`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_repair_subtree`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap`.
* 6.3 Building a heap: {lit}`proved` for bottom-up repeated heapify.
  Public results: {lit}`CLRS.Chapter06.buildMaxHeapLoop_isMaxHeap`,
  {lit}`CLRS.Chapter06.buildMaxHeapLoop_perm`,
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap`,
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_correct`.
* 6.4 The heapsort algorithm: {lit}`proved` for the in-place CLRS loop refinement.
  Public results: {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_perm`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_length`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_perm`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_length`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_suffix_head_eq_root`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_suffix_head_bounds_prefix`,
  {lit}`CLRS.Chapter06.HeapSortLoopInvariant.step`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_state_correct`,
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
  {lit}`CLRS.Chapter06.arrayHeapSort_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSort_exact_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSort_orderedAsc`,
  {lit}`CLRS.Chapter06.arrayHeapSort_perm`,
  {lit}`CLRS.Chapter06.arrayHeapSort_correct`.
* 6.5 Priority queues: {lit}`proved` for the functional heap interface plus
  array-level {lit}`HEAP-MAXIMUM`, full fuelled {lit}`HEAP-INCREASE-KEY`, and
  {lit}`HEAP-EXTRACT-MAX` / {lit}`HEAP-DELETE`.
  Public results: {lit}`CLRS.Chapter06.heapInsert_orderedDesc`,
  {lit}`CLRS.Chapter06.heapInsert_perm`,
  {lit}`CLRS.Chapter06.heapIncreaseKey_orderedDesc`,
  {lit}`CLRS.Chapter06.heapDelete_orderedDesc`,
  {lit}`CLRS.Chapter06.arrayHeapMaximum?_max`,
  {lit}`CLRS.Chapter06.ArrayMaxHeap.set_increased_except_up`,
  {lit}`CLRS.Chapter06.ArrayMaxHeapExceptUp.bubble_step`,
  {lit}`CLRS.Chapter06.ArrayMaxHeapExceptUp.bubbleUpFuel_global`,
  {lit}`CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapIncreaseKeyNoBubble?_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapExtractMax?_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapDelete?_state_correct`.
* 7.1 Description of quicksort: {lit}`proved` for the functional-list model,
  scan-state partition loop, and returned pivot-index wrapper with an explicit
  adjacent-swap trace.
  Public results: {lit}`CLRS.Chapter07.partitionAround_left_eq_filter`,
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
  {lit}`CLRS.Chapter07.quickSort_perm`, {lit}`CLRS.Chapter07.quickSort_ordered`,
  {lit}`CLRS.Chapter07.quickSort_correct`.
* 7.2 Performance of quicksort: {lit}`proved` for the current deterministic
  comparison-count model.
  Public results: {lit}`CLRS.Chapter07.partitionAround_length_add`,
  {lit}`CLRS.Chapter07.quickSortComparisonsFuel_quadratic`, and
  {lit}`CLRS.Chapter07.quickSortComparisons_quadratic`.
* 7.3 Randomized quicksort: {lit}`proved` for the expected-comparison
  recurrence, closed-form telescope, and harmonic upper bound in the current
  recurrence model.
  Public results: {lit}`CLRS.Chapter07.expectedComparisons_recurrence`,
  {lit}`CLRS.Chapter07.expectedComparisons_telescope`,
  {lit}`CLRS.Chapter07.expectedComparisons_harmonic_bound`,
  {lit}`CLRS.Chapter07.expectedComparisons_quadratic`, and
  {lit}`CLRS.Chapter07.expectedComparisons_monotone`.
* 7.4 Quicksort analysis refinements: {lit}`future-work`.
  Planned targets: index-level mutable-array {lit}`PARTITION`, an explicit
  probability space for pivot choices, sharper {lit}`n log n` tail bounds, and
  lower-bound packaging.
* 8.2 Counting sort: {lit}`proved` for the stable bucket specification.
  Public results: {lit}`CLRS.Chapter08.countingSortBy_ordered`,
  {lit}`CLRS.Chapter08.countingSortBy_bucket_eq`,
  {lit}`CLRS.Chapter08.countingSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.countingSortBy_perm`, and
  {lit}`CLRS.Chapter08.countingSortBy_correct`.
* 8.3 Radix sort: {lit}`proved` for the abstract stable digit-pass model with
  complete digit-signature stability plus a concrete base-{lit}`b` natural-key
  wrapper, including key-order packaging and the bounded fixed-width arithmetic
  bridge.
  Public results: {lit}`CLRS.Chapter08.radixPass_orderedRel`,
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
* 8.4 Bucket sort: {lit}`proved` for deterministic bucket-index correctness.
  Public results: {lit}`CLRS.Chapter08.bucketSortBy_ordered`,
  {lit}`CLRS.Chapter08.bucketSortBy_perm`,
  {lit}`CLRS.Chapter08.bucketSortBy_correct`, and
  {lit}`CLRS.Chapter08.bucketSortByRank_correct`;
  finite-uniform expected-cost results:
  {lit}`CLRS.Chapter08.uniformAverageFin_indicator_singleton`,
  {lit}`CLRS.Chapter08.uniformAverageFin2_collision`,
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_eq`, and
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`.
* 9.2 Selection by rank: {lit}`proved` for the specification selector and
  pivot-style quickselect.
  Public results: {lit}`CLRS.Chapter09.selectByRank?_mem`,
  {lit}`CLRS.Chapter09.selectByRank?_rankCorrect`,
  {lit}`CLRS.Chapter09.selectByRank?_correct`,
  {lit}`CLRS.Chapter09.quickSelect?_mem`,
  {lit}`CLRS.Chapter09.quickSelect?_rankCorrect`,
  {lit}`CLRS.Chapter09.quickSelect?_correct`.
* 9.3 Deterministic selection: {lit}`proved` for a pivot-parametric SELECT interface,
  the five-element median certificate, executable five-element grouping,
  grouped split-count bounds, deterministic median-pivot instance,
  median-of-medians pivot/select wrapper, and the abstract linear recurrence
  wrapper.
  Public results: {lit}`CLRS.Chapter09.selectWithPivot?_correct`,
  {lit}`CLRS.Chapter09.medianOfFive?_certificate`,
  {lit}`CLRS.Chapter09.medianOfFive?_isSome_of_length_eq_five`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianGroupCertificates`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_split_counts`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_fullInput_split_counts`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_size_bound`,
  {lit}`CLRS.Chapter09.selectRecurrence_linear_step`,
  {lit}`CLRS.Chapter09.selectRecurrence_linear_induction`,
  {lit}`CLRS.Chapter09.medianOfMedians_linear_bound`,
  {lit}`CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`,
  {lit}`CLRS.Chapter09.medianOfFiveGroups?_mem_flatten`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianOfFiveGroups?_isSome`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_mem`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`,
  {lit}`CLRS.Chapter09.medianOfMediansSelect?_correct`.
* 9.3-9.4 Linear-time selection refinements: {lit}`future-work`.
  Planned target: connect the executable {lit}`medianOfMediansSelect?` cost
  semantics to the proved abstract linear recurrence theorem.
* 10.1 Stacks and queues: {lit}`proved` for the functional-list model.
  Public results: {lit}`CLRS.Chapter10.pop_push`,
  {lit}`CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists: {lit}`proved` for the functional-list model.
  Public results: {lit}`CLRS.Chapter10.listSearch_sound`,
  {lit}`CLRS.Chapter10.mem_listDeleteAll_iff`.
* 11.1 Direct-address tables: {lit}`proved` for the functional table model.
  Public results: {lit}`CLRS.Chapter11.search_insert_same`,
  {lit}`CLRS.Chapter11.search_delete_same`.
* 11.2 Chained hash tables: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter11.hashSearch_hashInsert_self`,
  {lit}`CLRS.Chapter11.hashSearch_hashInsert_iff`,
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_self`,
  {lit}`CLRS.Chapter11.hashSearch_hashDelete_iff`,
  {lit}`CLRS.Chapter11.uniformAverageFin_indicator_singleton`,
  {lit}`CLRS.Chapter11.expectedSearchChainLength_eq_loadFactor`,
  {lit}`CLRS.Chapter11.expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor`,
  {lit}`CLRS.Chapter11.totalBucketLength_finiteHashInsert`, and
  {lit}`CLRS.Chapter11.expectedSearchChainLength_finiteHashInsert`.
* 12.1 Binary search trees: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter12.BSTree.search_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
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
  {lit}`CLRS.Chapter12.BSTree.not_inTree_delete_self`,
  {lit}`CLRS.Chapter12.BSTree.delete_eq_self_of_not_inTree`,
  {lit}`CLRS.Chapter12.BSTree.search_delete_self_eq_false`,
  {lit}`CLRS.Chapter12.BSTree.search_delete_eq_true_iff`,
  {lit}`CLRS.Chapter12.BSTree.delete_ordered`.
* 13.1 Red-black trees: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`,
  {lit}`CLRS.Chapter13.RBTree.noRedRed_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_leftLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_leftRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_rightLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_rightRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftLeft`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftRight`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightLeft`, and
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightRight`.
* 14.1 Order-statistic trees: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter14.OSTree.storedSize_eq_realSize_of_wellSized`,
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
  and {lit}`CLRS.Chapter14.OSTree.osSelect?_recomputeSizes_eq_rankSelect?`.
* 15.1 Rod cutting: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter15.firstCutValue_le_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.rodRevenue_le_of_firstCutValue_bounds`,
  {lit}`CLRS.Chapter15.price_le_revenue_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.planValue_le_revenue_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.planValue_le_optimalPlanValue_of_same_length`.
* 15.2 Matrix-chain multiplication: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter15.ChainPlan.start_le_end`,
  {lit}`CLRS.Chapter15.MatrixChainLowerBound`,
  {lit}`CLRS.Chapter15.MatrixChainSplitOptimal`,
  {lit}`CLRS.Chapter15.matrixChain_opt_le_planCost`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_eq`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_optimal`, and
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_le_planCost`.
* 15.4 Longest common subsequence: {lit}`partial`.
  Current results: {lit}`CLRS.Chapter15.IsCommonSubsequence`,
  {lit}`CLRS.Chapter15.LCSCertificate.commonSubsequence_length_le`,
  {lit}`CLRS.Chapter15.LCSCertificate.length_eq_of_certificates`, and
  {lit}`CLRS.Chapter15.isCommonSubsequence_comm`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.nil_left`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.nil_right`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.commonSubsequence_length_le`,
  {lit}`CLRS.Chapter15.lcsTable_reconstruction_optimal`, and
  {lit}`CLRS.Chapter15.lcsCertificate_of_table_reconstruction_length`.
* 16.1 Activity selection: {lit}`proved` for finite sorted lists.
  Current results: {lit}`CLRS.ActivitySelection.earliest_finish_minFinish`,
  {lit}`CLRS.ActivitySelection.finishSorted_head_minFinish`,
  {lit}`CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`,
  {lit}`CLRS.ActivitySelection.activitySelection`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_eq`,
  {lit}`CLRS.ActivitySelection.greedySelect_cons_eq`,
  {lit}`CLRS.ActivitySelection.greedySelect_sublist`,
  {lit}`CLRS.ActivitySelection.greedySelect_feasible`,
  {lit}`CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`,
  {lit}`CLRS.ActivitySelection.greedySelect_after_maxCardinality`,
  {lit}`CLRS.ActivitySelection.greedySelect_cons_maxCardinality`,
  {lit}`CLRS.ActivitySelection.greedySelect_maxCardinality`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_maxCardinality`,
  {lit}`CLRS.ActivitySelection.activitySelection_maxCardinality`,
  {lit}`CLRS.ActivitySelection.greedySelect_optimal_length`,
  {lit}`CLRS.ActivitySelection.greedySelect_cons_recursive_correct`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_recursive_correct`,
  {lit}`CLRS.ActivitySelection.activitySelection_cons_correct`,
  {lit}`CLRS.ActivitySelection.activitySelection_correct`.
* 16.3 Huffman codes: {lit}`proved`.
  Public results: {lit}`CLRS.HuffmanV2.optimum_huffman_freqs`,
  {lit}`CLRS.HuffmanV2.huffmanOfFreqs_correct`, and
  {lit}`CLRS.HuffmanV2.huffmanOfFreqs_cost_le`.
* 23.1 Growing a minimum spanning tree: {lit}`partial`.
  Current results:
  {lit}`CLRS.MST.Graph.connected_crosses_cut`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`,
  {lit}`CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`,
  {lit}`CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`, and
  {lit}`CLRS.MST.safe_edge_of_lightest_crossing`.
* 23.2 Kruskal and Prim: {lit}`partial`.
  Current results:
  {lit}`CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`,
  {lit}`CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`,
  {lit}`CLRS.MST.Graph.InsertedEdgeConnection`,
  {lit}`CLRS.MST.Graph.exchangePath_connected_insert`,
  {lit}`CLRS.MST.Graph.exchangePath_of_insert_connected`,
  {lit}`CLRS.MST.Graph.exchangePath_iff_insertedEdgeConnection`,
  {lit}`CLRS.MST.FiniteGraph.exchangePath_of_insert_connects_erased_edge`,
  {lit}`CLRS.MST.FiniteGraph.exchangePath_iff_insertedEdgeConnection_of_spanningTree`,
  {lit}`CLRS.MST.kruskal_optimal`, and
  {lit}`CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_cycle_test`.

## Status Policy

The site uses explicit status labels instead of hiding incomplete work.

* {lit}`proved`: the named theorem is proved in Lean without relying on {lit}`sorry`.
* {lit}`expository`: the page is a reader guide rather than a theorem-bearing
  section.
* {lit}`partial`: important theorem infrastructure exists, but the full textbook
  section is not yet complete.
* {lit}`blocked-design`: progress needs a representation decision, such as paths,
  walks, heaps, arrays, or cost semantics.
* {lit}`deferred-implementation`: a low-level implementation proof is useful but not
  required for the current mathematical theorem.
* {lit}`future-work`: valuable extensions, exercises, or chapter-end problems.

## Build and Deployment

The deployed site is generated from the Lean source by Verso:

* {lit}`lake build` compiles the Lean library.
* {lit}`lake build :literateHtml` generates the website.

GitHub Actions runs the same pipeline and publishes the generated {lit}`_site`
directory to GitHub Pages.

Repository: [TankTechnology/CLRS-Lean](https://github.com/TankTechnology/CLRS-Lean)
-/
