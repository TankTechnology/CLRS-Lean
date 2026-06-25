/-!
# Proof Status

This page is the public status ledger for the web site.  It mirrors the longer
maintainer notes in `docs/proof-map.md`, but is written for readers who are
navigating the deployed pages.

## Status Labels

* `proved`: the named section theorem is proved in Lean for the current
  specification.
* `expository`: a reader-facing guide page with no theorem target.
* `partial`: important theorem infrastructure exists, but the full textbook
  claim is not complete.
* `statement`: the intended theorem interface exists, but proof work has not
  started.
* `blocked-design`: progress depends on choosing a stable representation.
* `blocked-mathlib`: progress depends on missing or inconvenient Mathlib
  infrastructure.
* `deferred-implementation`: the mathematical proof is in scope, but a
  low-level implementation proof is postponed.
* `future-work`: exercises, chapter-end problems, or strengthening passes
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
  exact-power extraction, and the all-input transfer bridge are proved.
* Chapter 5, Section 5.1: the hiring problem is proved in the finite
  rank-symmetry model.
* Chapter 6, Sections 6.1-6.5: the indexed array heap layer, recursive
  {lit}`MAX-HEAPIFY`, bottom-up {lit}`BUILD-MAX-HEAP`, in-place heapsort
  sorted-suffix invariant, top-level heapsort correctness, and array-level
  priority-queue state theorems are proved.
* Chapter 7, Section 7.1: stable functional partition classification,
  scan-state partition-loop correctness, and functional quicksort
  sortedness/permutation preservation are proved.
* Chapter 8, Sections 8.2-8.4: stable counting-sort bucket correctness,
  abstract radix-sort correctness from stable digit passes, and deterministic
  bucket-sort correctness are proved.
* Chapter 9, Sections 9.2-9.3: selection-by-rank correctness is proved for the
  specification selector, a pivot-style quickselect model, and a
  pivot-parametric deterministic SELECT model with a count-based
  order-statistic certificate.
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
* Chapter 4 as a whole: the local proof engines are strong, but concrete
  floor/ceiling Master-theorem instantiations and selected runtime refinements
  remain.
* Chapter 11, Section 11.2: deterministic chained-hash-table operations are
  proved for a fixed hash function; expected-time hashing remains.
* Chapter 12, Section 12.1: functional BST operations are proved; parent
  pointers, transplant, and mutation remain.
* Chapter 13, Section 13.1: local red-black rotation/recoloring invariants are
  proved; full insertion and deletion fixup algorithms remain.
* Chapter 23, Sections 23.1-23.2: the cut property, safe-edge theorem,
  exact-component Kruskal scan facts, forest/spanning wrappers, and
  certificate-based Kruskal optimality interfaces exist; automatic simple
  path/cycle exchange extraction, fully prefix-local sorted-lightness wrapping,
  and Prim remain.

### Missing Core Theorem

* Chapter 4 full Master-theorem instantiation: discharge the all-input transfer
  bridge's power-sandwich hypotheses for floor/ceiling recurrences.
* Chapter 7, Sections 7.2-7.4: mutable-array partition refinement,
  performance recurrence, randomized quicksort, and expected-time theorem.
* Chapter 9 linear-time SELECT refinements: pivot-parametric deterministic
  SELECT is proved; randomized expected time and the CLRS median-of-medians
  split-size/runtime theorem remain.
* Chapter 11 expected hashing analysis: expected-time theorem under a formal
  probability model.
* Chapter 12 pointer-level BST layer: CLRS parent-pointer procedures,
  transplant, and mutation refinement.
* Chapter 13 full red-black algorithms: insertion/deletion fixup correctness
  and height theorem.
* Chapters 14-15 and 17-22: not yet represented.
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
  `CLRS.Chapter03.isBigO_iff`,
  `CLRS.Chapter03.isLittleO_iff`,
  `CLRS.Chapter03.isBigOmega_iff`,
  `CLRS.Chapter03.isLittleOmega_iff`,
  `CLRS.Chapter03.isBigTheta_trans`.
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
  {lit}`CLRS.Chapter04.allInput_bigO_of_power_upper_sandwich`,
  {lit}`CLRS.Chapter04.allInput_bigOmega_of_power_lower_sandwich`, and
  {lit}`CLRS.Chapter04.allInput_bigTheta_of_power_sandwich`.
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
  {lit}`CLRS.Chapter07.partitionLoop_invariant`,
  {lit}`CLRS.Chapter07.partitionLoop_correct`,
  {lit}`CLRS.Chapter07.clrsPartition_correct`,
  {lit}`CLRS.Chapter07.quickSort_perm`,
  {lit}`CLRS.Chapter07.quickSort_ordered`, and
  {lit}`CLRS.Chapter07.quickSort_correct`.
* 8.2 Counting sort, stable bucket specification:
  {lit}`CLRS.Chapter08.countingSortBy_ordered`,
  {lit}`CLRS.Chapter08.countingSortBy_bucket_eq`,
  {lit}`CLRS.Chapter08.countingSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.countingSortBy_perm`, and
  {lit}`CLRS.Chapter08.countingSortBy_correct`.
* 8.3 Radix sort, abstract stable digit-pass model:
  {lit}`CLRS.Chapter08.radixPass_orderedRel`,
  {lit}`CLRS.Chapter08.radixSortBy_ordered`,
  {lit}`CLRS.Chapter08.radixSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.radixSortBy_perm`, and
  {lit}`CLRS.Chapter08.radixSortBy_correct`.
* 8.4 Bucket sort, deterministic bucket-index model:
  {lit}`CLRS.Chapter08.bucketSortBy_ordered`,
  {lit}`CLRS.Chapter08.bucketSortBy_perm`,
  {lit}`CLRS.Chapter08.bucketSortBy_correct`, and
  {lit}`CLRS.Chapter08.bucketSortByRank_correct`.
* 9.2 Selection by rank, specification selector and pivot-style quickselect:
  {lit}`CLRS.Chapter09.sortedCopy_perm`,
  {lit}`CLRS.Chapter09.sortedCopy_pairwise`,
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
  {lit}`CLRS.Chapter09.deterministicSelect?_mem`,
  {lit}`CLRS.Chapter09.deterministicSelect?_rankCorrect`, and
  {lit}`CLRS.Chapter09.deterministicSelect?_correct`.
* 2.1 Insertion sort:
  `CLRS.Chapter02.insertionSort_sorted`,
  `CLRS.Chapter02.insertionSort_perm`.
* 2.2 Analyzing algorithms:
  `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`.
* 2.3 Designing algorithms:
  `CLRS.Chapter02.mergeSort_sortedLE`,
  `CLRS.Chapter02.mergeSort_perm`,
  `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`.
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
  `CLRS.Chapter10.pop_push`,
  `CLRS.Chapter10.dequeue_enqueue_empty`,
  `CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists:
  `CLRS.Chapter10.listSearch_sound`,
  `CLRS.Chapter10.mem_listInsert_self`,
  `CLRS.Chapter10.mem_listDeleteAll_iff`.
* 11.1 Direct-address tables:
  `CLRS.Chapter11.search_insert_same`,
  `CLRS.Chapter11.search_insert_other`,
  `CLRS.Chapter11.search_delete_same`,
  `CLRS.Chapter11.search_delete_other`.

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

* Union-find correctness: `deferred-implementation`.
  Reason: not needed for the mathematical MST proof.
* Automatic MST exchange-path extraction: `blocked-design`.
  Reason: the cut-crossing tree-edge, prefix-preservation lemma, and
  certificate-based replacement spanning-tree theorem are proved; deriving
  the inserted-edge connection automatically still needs a stable finite simple
  path/cycle API.
* Full RAM semantics: `future-work`.
  Reason: requires a separate imperative machine and cost model.
* Chapter 4 full Master Theorem instantiation:
  `future-work`.
  Reason: exact powers, floor/ceiling exact-power extraction, and the generic
  all-input transfer bridge are proved; concrete comparison-scale sandwich
  hypotheses still need to be discharged for final Master-theorem statements.
* Chapter 4 Strassen recursive refinement:
  `future-work`.
  Reason: the 2 by 2 block algebra is proved; recursive splitting,
  dimension bookkeeping, and runtime analysis remain separate refinements.
* Chapter 4 maximum-subarray runtime analysis: `future-work`.
  Reason: the exhaustive-search specification, crossing-helper optimality,
  executable left/right/crossing combine step, and recursive split-tree/fuelled
  selector correctness are proved; the runtime recurrence and RAM-cost
  refinement remain future work.
* Chapter 6 priority-queue RAM costs: `deferred-implementation`.
  Reason: the functional heap specification, recursive {lit}`MAX-HEAPIFY`
  repair, bottom-up {lit}`BUILD-MAX-HEAP` refinement, in-place heapsort loop
  scaffold, exact-shrink invariant, loop permutation/length facts, root-to-
  suffix-head step theorem, shrinking-prefix sorted-suffix invariant
  preservation, bundled state-correctness theorem, and in-place
  sortedness proof are proved; array-level {lit}`HEAP-MAXIMUM`, full fuelled
  {lit}`HEAP-INCREASE-KEY`, {lit}`HEAP-EXTRACT-MAX`, and index-based
  {lit}`HEAP-DELETE` state correctness are also proved.  The remaining
  implementation layer is the line-by-line RAM-cost model.
* Chapter 7 mutable-array partition and randomized analysis: `future-work`.
  Reason: Section 7.1 now proves the pure partition/quicksort correctness
  spine and a scan-state partition-loop invariant; the harder refinements are
  the CLRS array `PARTITION` swap model, recurrence analysis, randomized
  quicksort, and expected running time.
* Chapter 4 concrete all-input Master-theorem instantiations: `future-work`.
  Reason: needs concrete comparison-scale sandwiching on top of the proved
  floor/ceiling extraction and all-input transfer bridge.
* General merge-sort recurrence: `future-work`.
  Reason: needs floor and ceiling arithmetic for all input sizes.
* CLRS exercises and chapter-end problems: `future-work`.
  Reason: kept separate from the first main-theorem pass.

## Reader Contract

The status table is intentionally conservative.  A section is not marked
`proved` merely because the algorithm idea is clear; it needs a named Lean
theorem that compiles for the stated model.  A section marked `partial` should
say exactly which mathematical or representation layer remains.
-/
