# CLRS-Lean

`CLRS-Lean` is a chapter-by-chapter Lean companion project for CLRS-style
algorithm correctness proofs.

The project is organized by the book order, not by implementation topic.  A
section file is named with both its CLRS number and a short human-readable
suffix:

```text
CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean
CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean
CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean
CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean
CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean
CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean
CLRSLean/Chapter_04/Section_04_2_Strassen_Algorithm.lean
CLRSLean/Chapter_04/Section_04_3_Substitution_Method.lean
CLRSLean/Chapter_04/Section_04_4_Recursion_Tree_Method.lean
CLRSLean/Chapter_04/Section_04_5_Master_Theorem.lean
CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean
CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean
CLRSLean/Chapter_06/Section_06_1_Heaps.lean
CLRSLean/Chapter_06/Section_06_2_Maintaining_Heap_Property.lean
CLRSLean/Chapter_06/Section_06_3_Building_A_Heap.lean
CLRSLean/Chapter_06/Section_06_4_Heapsort.lean
CLRSLean/Chapter_06/Section_06_5_Priority_Queues.lean
CLRSLean/Chapter_07/Section_07_1_Description_Of_Quicksort.lean
CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean
CLRSLean/Chapter_08/Section_08_3_Radix_Sort.lean
CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean
CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean
CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean
CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean
CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean
CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean
CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean
CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean
CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
```

In prose and on the future website, these appear as:

- Section 2.1 - Insertion sort
- Section 2.2 - Analyzing algorithms
- Section 2.3 - Designing algorithms
- Section 3.1 - Asymptotic notation
- Section 3.2 - Standard functions
- Section 4.1 - The maximum-subarray problem
- Section 4.2 - Strassen's algorithm
- Section 4.3 - The substitution method
- Section 4.4 - The recursion-tree method
- Section 4.5 - The master method
- Section 4.6 - Proof of the master theorem
- Section 5.1 - The hiring problem
- Section 6.1 - Heaps
- Section 6.2 - Maintaining the heap property
- Section 6.3 - Building a heap
- Section 6.4 - The heapsort algorithm
- Section 6.5 - Priority queues
- Section 7.1 - Description of quicksort
- Section 8.2 - Counting sort
- Section 8.3 - Radix sort
- Section 8.4 - Bucket sort
- Section 9.2 - Selection by rank
- Section 9.3 - Deterministic selection
- Section 10.1 - Stacks and queues
- Section 10.2 - Linked lists
- Section 11.1 - Direct-address tables
- Section 11.2 - Chained hash tables
- Section 12.1 - Binary search trees
- Section 13.1 - Red-black trees
- Section 16.1 - Activity selection
- Section 16.3 - Huffman codes
- Section 23.1 - Growing a minimum spanning tree
- Section 23.2 - Kruskal and Prim

The Lean filenames use underscores instead of hyphens because Lean module names
should remain import-friendly.

## Current Sections

| CLRS section | Lean source | Status | Main result |
| --- | --- | --- | --- |
| Section 2.1 - Insertion sort | `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean` | `proved` | `CLRS.Chapter02.insertionSort_sorted`, `CLRS.Chapter02.insertionSort_perm` |
| Section 2.2 - Analyzing algorithms | `CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean` | `proved` | `CLRS.Chapter02.insertionSortWorstComparisons_quadratic` |
| Section 2.3 - Designing algorithms | `CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean` | `proved` | `CLRS.Chapter02.mergeSort_sortedLE`, `CLRS.Chapter02.mergeSort_perm`, `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm` |
| Section 3.1 - Asymptotic notation | `CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean` | `proved` | `CLRS.Chapter03.isBigO_iff`, `CLRS.Chapter03.isLittleO_iff`, `CLRS.Chapter03.isBigTheta_trans` |
| Section 3.2 - Standard functions | `CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean` | `partial` | `CLRS.Chapter03.isLittleO_pow_pow`, `CLRS.Chapter03.isLittleO_log_rpow`, `CLRS.Chapter03.isLittleO_log_pow_rpow`, `CLRS.Chapter03.isBigO_log_pow_rpow`, `CLRS.Chapter03.isBigTheta_nat_floor_half_coerce`, `CLRS.Chapter03.isBigTheta_harmonic_log`, `CLRS.Chapter03.factorial_lower_bound_half_pow`, `CLRS.Chapter03.isLittleO_exp_vs_factorial`, `CLRS.Chapter03.isLittleO_factorial_pow_self` |
| Section 4.1 - Maximum subarray | `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean` | `proved` for the current functional correctness model | `CLRS.Chapter04.mem_nonemptySubarrays_iff`, `CLRS.Chapter04.mem_crossingSubarrays_iff`, `CLRS.Chapter04.maxCrossingSubarray_correct`, `CLRS.Chapter04.subarray_append_left_or_right_or_crossing`, `CLRS.Chapter04.subarray_append_optimal_of_cases`, `CLRS.Chapter04.maxSubarrayDivideStep_correct`, `CLRS.Chapter04.maxSubarrayDivideTree_correct`, `CLRS.Chapter04.maxSubarrayDivideFuel_correct`, `CLRS.Chapter04.maxSubarray_correct` |
| Section 4.2 - Strassen's algorithm | `CLRSLean/Chapter_04/Section_04_2_Strassen_Algorithm.lean` | `proved` for 2 by 2 block algebra | `CLRS.Chapter04.Matrix2.strassen_eq_mul`, `CLRS.Chapter04.strassen2x2_correct` |
| Section 4.3 - Substitution method | `CLRSLean/Chapter_04/Section_04_3_Substitution_Method.lean` | `proved` for one-step recurrence bounds | `CLRS.Chapter04.substitution_upper_bound`, `CLRS.Chapter04.linear_substitution_upper_bound`, `CLRS.Chapter04.geometric_substitution_upper_bound` |
| Section 4.4 - Recursion-tree method | `CLRSLean/Chapter_04/Section_04_4_Recursion_Tree_Method.lean` | `proved` for additive level-cost expansions | `CLRS.Chapter04.recursion_tree_additive_unroll`, `CLRS.Chapter04.recursion_tree_additive_upper_envelope`, `CLRS.Chapter04.recursion_tree_constant_level_cost` |
| Section 4.5 - The master method | `CLRSLean/Chapter_04/Section_04_5_Master_Theorem.lean` | `proved` for exact powers | `CLRS.Chapter04.master_case1_geometric`, `CLRS.Chapter04.master_case2_constant_forcing`, `CLRS.Chapter04.master_case3_tail_dominated` |
| Section 4.6 - Proof of the master theorem | `CLRSLean/Chapter_04/Section_04_6_Master_Theorem_All_Input.lean` | `partial` with floor/ceiling exact-power extraction, all-input transfer, adjacent-power sandwich generation, discrete critical-power scale wrapper, and packaged case 1 wrappers proved | `CLRS.Chapter04.FloorDivideRecurrence`, `CLRS.Chapter04.CeilDivideRecurrence`, `CLRS.Chapter04.exactPowerRecurrence_of_floorDivideRecurrence`, `CLRS.Chapter04.exactPowerRecurrence_of_ceilDivideRecurrence`, `CLRS.Chapter04.powerInterval_of_pos`, `CLRS.Chapter04.eventuallyPowerUpperSandwich_of_powerStep`, `CLRS.Chapter04.eventuallyPowerLowerSandwich_of_powerStep`, `CLRS.Chapter04.allInput_bigTheta_of_power_sandwich`, `CLRS.Chapter04.allInput_bigTheta_of_powerStep`, `CLRS.Chapter04.criticalPowerScale`, `CLRS.Chapter04.allInput_bigTheta_of_criticalPowerScale`, `CLRS.Chapter04.floorDivide_allInput_masterCase1_criticalPowerScale`, `CLRS.Chapter04.ceilDivide_allInput_masterCase1_criticalPowerScale` |
| Section 5.1 - The hiring problem | `CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean` | `proved` for finite rank symmetry | `CLRS.Chapter05.hireProbability_eq`, `CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`, `CLRS.Chapter05.expectedHires_isBigTheta_log` |
| Section 6.1 - Heaps | `CLRSLean/Chapter_06/Section_06_1_Heaps.lean` | `proved` for the indexed heap predicate and root maximum | `CLRS.Chapter06.parent_lt_self`, `CLRS.Chapter06.eq_left_or_right_parent`, `CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`, `CLRS.Chapter06.orderedDesc_arrayMaxHeap` |
| Section 6.2 - Maintaining the heap property | `CLRSLean/Chapter_06/Section_06_2_Maintaining_Heap_Property.lean` | `proved` for fuelled `MAX-HEAPIFY` repair | `CLRS.Chapter06.swapAt_perm`, `CLRS.Chapter06.maxHeapifyFuel_perm`, `CLRS.Chapter06.maxHeapifyFuel_valAt_of_heapSize_le`, `CLRS.Chapter06.maxHeapifyFuel_swap_branch_repair`, `CLRS.Chapter06.maxHeapifyFuel_repair_subtree`, `CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap` |
| Section 6.3 - Building a heap | `CLRSLean/Chapter_06/Section_06_3_Building_A_Heap.lean` | `proved` for bottom-up repeated heapify | `CLRS.Chapter06.buildMaxHeapLoop_isMaxHeap`, `CLRS.Chapter06.buildMaxHeapLoop_perm`, `CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap`, `CLRS.Chapter06.arrayBuildMaxHeap_correct` |
| Section 6.4 - The heapsort algorithm | `CLRSLean/Chapter_06/Section_06_4_Heapsort.lean` | `proved` for the in-place CLRS loop refinement | `CLRS.Chapter06.arrayHeapSortStep_suffix_head_eq_root`, `CLRS.Chapter06.arrayHeapSortStep_suffix_head_bounds_prefix`, `CLRS.Chapter06.HeapSortLoopInvariant.step`, `CLRS.Chapter06.arrayHeapSortStep_state_correct`, `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_shrink_invariant`, `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_terminal_invariant`, `CLRS.Chapter06.arrayHeapSortInPlaceLoop_terminal_invariant`, `CLRS.Chapter06.arrayHeapSortInPlaceLoop_orderedAsc`, `CLRS.Chapter06.arrayHeapSortInPlaceLoop_state_correct`, `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_state_correct`, `CLRS.Chapter06.arrayHeapSortInPlace_terminal_invariant`, `CLRS.Chapter06.arrayHeapSortInPlace_state_correct`, `CLRS.Chapter06.arrayHeapSortInPlace_exact_state_correct`, `CLRS.Chapter06.arrayHeapSortInPlace_correct`, `CLRS.Chapter06.arrayHeapSort_eq_arrayHeapSortInPlace`, `CLRS.Chapter06.arrayHeapSort_terminal_invariant`, `CLRS.Chapter06.arrayHeapSort_state_correct`, `CLRS.Chapter06.arrayHeapSort_exact_state_correct`, `CLRS.Chapter06.arrayHeapSort_correct` |
| Section 6.5 - Priority queues | `CLRSLean/Chapter_06/Section_06_5_Priority_Queues.lean` | `proved` for the functional heap interface plus array maximum/full fuelled increase-key/extract-max/delete | `CLRS.Chapter06.heapInsert_orderedDesc`, `CLRS.Chapter06.heapIncreaseKey_orderedDesc`, `CLRS.Chapter06.heapDelete_orderedDesc`, `CLRS.Chapter06.arrayHeapMaximum?_max`, `CLRS.Chapter06.ArrayMaxHeap.set_increased_except_up`, `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubble_step`, `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubbleUpFuel_global`, `CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct`, `CLRS.Chapter06.arrayHeapIncreaseKeyNoBubble?_state_correct`, `CLRS.Chapter06.arrayHeapExtractMax?_state_correct`, `CLRS.Chapter06.arrayHeapDelete?_state_correct` |
| Section 7.1 - Description of quicksort | `CLRSLean/Chapter_07/Section_07_1_Description_Of_Quicksort.lean` | `proved` for the functional-list model and scan-state partition loop | `CLRS.Chapter07.partitionAround_left_eq_filter`, `CLRS.Chapter07.partitionAround_right_eq_filter`, `CLRS.Chapter07.mem_partitionAround_left_iff`, `CLRS.Chapter07.mem_partitionAround_right_iff`, `CLRS.Chapter07.partitionAround_correct`, `CLRS.Chapter07.partitionAround_perm`, `CLRS.Chapter07.partitionAround_left_allLeUpper`, `CLRS.Chapter07.partitionAround_right_allGt`, `CLRS.Chapter07.partitionLoop_invariant`, `CLRS.Chapter07.partitionLoop_correct`, `CLRS.Chapter07.clrsPartition_correct`, `CLRS.Chapter07.quickSort_perm`, `CLRS.Chapter07.quickSort_ordered`, `CLRS.Chapter07.quickSort_correct` |
| Section 8.2 - Counting sort | `CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean` | `proved` for the stable bucket specification | `CLRS.Chapter08.countingSortBy_ordered`, `CLRS.Chapter08.countingSortBy_bucket_eq`, `CLRS.Chapter08.countingSortBy_mem_iff`, `CLRS.Chapter08.countingSortBy_perm`, `CLRS.Chapter08.countingSortBy_correct` |
| Section 8.3 - Radix sort | `CLRSLean/Chapter_08/Section_08_3_Radix_Sort.lean` | `proved` for the abstract stable digit-pass model, concrete base-`b` digit extraction, key-order packaging, and bounded fixed-width key correctness | `CLRS.Chapter08.radixPass_orderedRel`, `CLRS.Chapter08.radixSortBy_ordered`, `CLRS.Chapter08.radixSortBy_stable`, `CLRS.Chapter08.radixSortBy_mem_iff`, `CLRS.Chapter08.radixSortBy_perm`, `CLRS.Chapter08.radixSortBy_correct_stable`, `CLRS.Chapter08.baseDigitsLow_allDigitsLe`, `CLRS.Chapter08.radixSortNatBy_correct_stable`, `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_digitOrder`, `CLRS.Chapter08.radixDigitOrderRespectsKey_of_bounded`, `CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_bounded` |
| Section 8.4 - Bucket sort | `CLRSLean/Chapter_08/Section_08_4_Bucket_Sort.lean` | `proved` for deterministic bucket-index correctness | `CLRS.Chapter08.bucketSortBy_ordered`, `CLRS.Chapter08.bucketSortBy_perm`, `CLRS.Chapter08.bucketSortBy_correct`, `CLRS.Chapter08.bucketSortByRank_correct` |
| Section 9.2 - Selection by rank | `CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean` | `proved` for the specification selector and pivot-style quickselect | `CLRS.Chapter09.selectByRank?_mem`, `CLRS.Chapter09.selectByRank?_rankCorrect`, `CLRS.Chapter09.selectByRank?_correct`, `CLRS.Chapter09.quickSelect?_mem`, `CLRS.Chapter09.quickSelect?_rankCorrect`, `CLRS.Chapter09.quickSelect?_correct` |
| Section 9.3 - Deterministic selection | `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean` | `proved` for pivot-parametric deterministic SELECT correctness and executable median-of-medians partition-size bounds | `CLRS.Chapter09.selectWithPivot?_mem`, `CLRS.Chapter09.selectWithPivot?_rankCorrect`, `CLRS.Chapter09.selectWithPivot?_correct`, `CLRS.Chapter09.medianOfFive?_certificate`, `CLRS.Chapter09.gtCount_eq_length_sub_leCount`, `CLRS.Chapter09.fullGroupsOfFive_lengths`, `CLRS.Chapter09.fullGroupsOfFive_length_mul_five_le`, `CLRS.Chapter09.fullGroupsOfFive_length_near`, `CLRS.Chapter09.fullGroupsOfFive_flatten_sublist`, `CLRS.Chapter09.leCount_le_of_sublist`, `CLRS.Chapter09.geCount_le_of_sublist`, `CLRS.Chapter09.medianOfFiveGroups?_certificates`, `CLRS.Chapter09.fullGroupsOfFive_medianGroupCertificates`, `CLRS.Chapter09.medianGroupCertificates_leCount_lower_bound`, `CLRS.Chapter09.medianGroupCertificates_geCount_lower_bound`, `CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`, `CLRS.Chapter09.fullGroupsOfFive_selectPivot_split_counts`, `CLRS.Chapter09.fullGroupsOfFive_medianPivot_split_counts`, `CLRS.Chapter09.fullGroupsOfFive_medianPivot_fullInput_split_counts`, `CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_lengths`, `CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_size_bound`, `CLRS.Chapter09.deterministicSelect?_mem`, `CLRS.Chapter09.deterministicSelect?_rankCorrect`, `CLRS.Chapter09.deterministicSelect?_correct` |
| Section 10.1 - Stacks and queues | `CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean` | `proved` | `CLRS.Chapter10.pop_push`, `CLRS.Chapter10.dequeue_enqueue_nonempty` |
| Section 10.2 - Linked lists | `CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean` | `proved` | `CLRS.Chapter10.listSearch_sound`, `CLRS.Chapter10.mem_listDeleteAll_iff` |
| Section 11.1 - Direct-address tables | `CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean` | `proved` | `CLRS.Chapter11.search_insert_same`, `CLRS.Chapter11.search_delete_same` |
| Section 11.2 - Chained hash tables | `CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean` | `partial` | `CLRS.Chapter11.hashSearch_hashInsert_self`, `CLRS.Chapter11.hashSearch_hashInsert_iff`, `CLRS.Chapter11.hashSearch_hashDelete_self`, `CLRS.Chapter11.hashSearch_hashDelete_iff` |
| Section 12.1 - Binary search trees | `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean` | `partial` | `CLRS.Chapter12.BSTree.search_eq_true_iff`, `CLRS.Chapter12.BSTree.minimum?_le_of_ordered`, `CLRS.Chapter12.BSTree.le_maximum?_of_ordered`, `CLRS.Chapter12.BSTree.successor?_least_greater`, `CLRS.Chapter12.BSTree.predecessor?_greatest_less`, `CLRS.Chapter12.BSTree.insert_ordered`, `CLRS.Chapter12.BSTree.inTree_delete_iff`, `CLRS.Chapter12.BSTree.delete_ordered` |
| Section 13.1 - Red-black trees | `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean` | `partial` | `CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`, `CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`, `CLRS.Chapter13.RBTree.noRedRed_repaint_black`, `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`, `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`, `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`, `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`, `CLRS.Chapter13.RBTree.redBlackShape_repaint_black` |
| Section 16.1 - Activity selection | `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean` | `proved` for finite sorted lists | `CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`, `CLRS.ActivitySelection.activitySelection`, `CLRS.ActivitySelection.activitySelection_cons_eq`, `CLRS.ActivitySelection.greedySelect_cons_maxCardinality`, `CLRS.ActivitySelection.greedySelect_maxCardinality`, `CLRS.ActivitySelection.activitySelection_cons_maxCardinality`, `CLRS.ActivitySelection.activitySelection_maxCardinality`, `CLRS.ActivitySelection.greedySelect_optimal_length`, `CLRS.ActivitySelection.greedySelect_cons_recursive_correct`, `CLRS.ActivitySelection.activitySelection_cons_recursive_correct`, `CLRS.ActivitySelection.activitySelection_cons_correct`, `CLRS.ActivitySelection.activitySelection_correct` |
| Section 16.3 - Huffman codes | `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean` | `proved` | `CLRS.HuffmanV2.optimum_huffman_freqs`, `CLRS.HuffmanV2.huffmanOfFreqs_correct`, `CLRS.HuffmanV2.huffmanOfFreqs_cost_le` |
| Section 23.1 - Growing a minimum spanning tree | `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean` | `partial` | `CLRS.MST.Graph.connected_crosses_cut`, `CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`, `CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`, `CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`, `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`, `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`, `CLRS.MST.safe_edge_of_lightest_crossing` |
| Section 23.2 - Kruskal and Prim | `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean` | `partial` | `CLRS.MST.Graph.ExchangePath`, `CLRS.MST.Graph.InsertedEdgeConnection`, `CLRS.MST.Graph.exchangePath_connected_insert`, `CLRS.MST.Graph.exchangePath_of_insert_connected`, `CLRS.MST.Graph.exchangePath_iff_insertedEdgeConnection`, `CLRS.MST.FiniteGraph.exchangePath_of_insert_connects_erased_edge`, `CLRS.MST.FiniteGraph.exchangePath_iff_insertedEdgeConnection_of_spanningTree`, `CLRS.MST.FiniteGraph.spanningTree_exchange_of_path_certificate`, `CLRS.MST.FiniteGraph.cutCertificate_of_lightest_crossing`, `CLRS.MST.lightest_crossing_of_sorted_prefix`, `CLRS.MST.processed_prefix_excludes_of_exact_component_kruskal`, `CLRS.MST.cut_certificate_of_exact_component_kruskal_prefix`, `CLRS.MST.FiniteGraph.kruskal_spanning_tree_of_complete_exact_component`, `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_cycle_test`, `CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_complete_exact_component_empty` |

See [`proof-map.md`](proof-map.md) for the full status ledger.

For a faster planning view, see [`proof-status-board.md`](proof-status-board.md).
It groups the project into three buckets: main proof completed, structured but
not complete, and missing core theorem.  This is the page to check before
returning to a chapter that already has its advertised main theorem.

## Proof Pattern Notes

- [`Greedy exchange certificates`](proof-patterns/greedy-exchange-certificates.md)
  explains the shared Chapter 16 pattern behind activity selection and Huffman
  coding.

The public website is generated from the Lean files by Verso.  The landing page
is `CLRSLean.lean`; chapter guide pages live at `CLRSLean/Chapter_XX.lean`; the
status ledger and workflow page live at `CLRSLean/Status.lean` and
`CLRSLean/Workflow.lean`.

## Status Labels

- `proved`: the main theorem for this section is sorry-free.
- `partial`: important Lean theorems exist, but the full CLRS section is not
  complete.
- `statement`: theorem interfaces exist, but proofs have not started.
- `blocked-design`: progress depends on choosing a representation, such as
  graph paths, heaps, arrays, or probability spaces.
- `blocked-mathlib`: progress depends on missing or inconvenient Mathlib
  infrastructure.
- `deferred-implementation`: the mathematical proof is in scope, but a low-level
  implementation proof is intentionally postponed.
- `future-work`: useful extension work, such as exercises or chapter-end
  Problems, that is intentionally outside the first main-theorem pass.
- `out-of-scope`: the section is not a current project target.

## Near-Term Rule

For early CLRS work, implementation-level data structure proofs are optional.
For example, union-find correctness is recorded as
`deferred-implementation`; the main MST target is the mathematical CLRS proof
via cut certificates and Kruskal's safe-edge induction.
