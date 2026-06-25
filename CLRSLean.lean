import CLRSLean.Chapter_01
import CLRSLean.Chapter_02
import CLRSLean.Chapter_03
import CLRSLean.Chapter_04
import CLRSLean.Chapter_05
import CLRSLean.Chapter_06
import CLRSLean.Chapter_07
import CLRSLean.Chapter_10
import CLRSLean.Chapter_11
import CLRSLean.Chapter_12
import CLRSLean.Chapter_13
import CLRSLean.Chapter_16
import CLRSLean.Chapter_23
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
  exact-power Master method core.
* Chapter 5 - Probabilistic Analysis: the finite rank-symmetry proof for the
  hiring problem and its logarithmic expected-hires bound.
* Chapter 6 - Heapsort: recursive {lit}`MAX-HEAPIFY` repair, bottom-up
  {lit}`BUILD-MAX-HEAP`, the in-place heapsort loop with a proved sorted-suffix
  invariant and sortedness theorem, an indexed array heap proof spine, and
  priority-queue operation specifications.
* Chapter 7 - Quicksort: stable functional partition correctness and
  functional quicksort sortedness/permutation preservation.
* Chapter 10 - Elementary Data Structures: functional stack, queue, and
  linked-list operation proofs.
* Chapter 11 - Hash Tables: direct-address table correctness and deterministic
  chained-hash-table insert/delete/search facts.
* Chapter 12 - Binary Search Trees: search, minimum/maximum, insertion,
  functional successor/predecessor, and functional deletion correctness for an
  inductive BST model.
* Chapter 13 - Red-Black Trees: local rotation, recoloring, red-red repair, and
  red-black shape invariant lemmas.
* Chapter 16 - Greedy Algorithms: activity-selection exchange infrastructure
  and the complete Huffman optimality proof, currently the flagship greedy case
  study.
* Chapter 23 - Minimum Spanning Trees: the MST cut property, the mathematical
  Kruskal skeleton, and finite-graph MST wrappers.
* Proof Status: a planning board plus a compact ledger of proved, partial,
  blocked, and deferred work.
* Workflow: the contribution loop for adding or strengthening a CLRS section.

## Current Coverage

* Chapter 1: `expository`.
  No theorem target; this page explains the project conventions.
* 2.1 Insertion sort: `proved`.
  Public results: `CLRS.Chapter02.insertionSort_sorted`,
  `CLRS.Chapter02.insertionSort_perm`.
* 2.2 Analyzing algorithms: `proved`.
  Public result: `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`.
* 2.3 Designing algorithms: `proved`.
  Public results: `CLRS.Chapter02.mergeSort_sortedLE`,
  `CLRS.Chapter02.mergeSort_perm`,
  `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`.
* 3.1 Asymptotic notation: `proved`.
  Public results: `CLRS.Chapter03.isBigO_iff`,
  `CLRS.Chapter03.isLittleO_iff`,
  `CLRS.Chapter03.isBigTheta_trans`.
* 3.2 Standard functions: `partial`.
  Current results: `CLRS.Chapter03.isLittleO_pow_pow`,
  `CLRS.Chapter03.isLittleO_pow_const_exp`,
  `CLRS.Chapter03.isLittleO_log_rpow`,
  `CLRS.Chapter03.isLittleO_log_pow_rpow`,
  `CLRS.Chapter03.isBigO_log_pow_rpow`,
  `CLRS.Chapter03.isLittleO_exp_exp_of_lt`,
  `CLRS.Chapter03.isEquivalent_harmonic_log`,
  `CLRS.Chapter03.isBigTheta_harmonic_log`,
  `CLRS.Chapter03.isBigTheta_nat_floor_coerce`,
  `CLRS.Chapter03.isBigTheta_nat_ceil_coerce`,
  `CLRS.Chapter03.isBigTheta_nat_floor_half_coerce`,
  `CLRS.Chapter03.isBigTheta_nat_ceil_half_coerce`,
  `CLRS.Chapter03.factorial_upper_bound`,
  `CLRS.Chapter03.factorial_lower_bound_offset`,
  `CLRS.Chapter03.factorial_lower_bound_half_pow`,
  `CLRS.Chapter03.isLittleO_exp_vs_factorial`,
  `CLRS.Chapter03.isLittleO_factorial_pow_self`.
* 4.1 Maximum subarray: `proved` for the exhaustive-search specification,
  crossing helper, and left/right/crossing combine interface.
  Public results: `CLRS.Chapter04.mem_nonemptySubarrays_iff`,
  `CLRS.Chapter04.bestCandidate_correct`,
  `CLRS.Chapter04.mem_crossingSubarrays_iff`,
  `CLRS.Chapter04.maxCrossingSubarray_correct`,
  `CLRS.Chapter04.maxCrossingSubarray_isNonemptySubarray_append`,
  `CLRS.Chapter04.subarray_append_left_or_right_or_crossing`,
  `CLRS.Chapter04.subarray_append_optimal_of_cases`,
  `CLRS.Chapter04.maxSubarray_exists_of_ne_nil`,
  `CLRS.Chapter04.maxSubarray_correct`.
* 4.2 Strassen's algorithm: `proved` for 2 by 2 block algebra.
  Public result: `CLRS.Chapter04.strassen2x2_correct`.
* 4.3 Substitution method: `proved` for one-step recurrence bounds.
  Public results: `CLRS.Chapter04.substitution_upper_bound`,
  `CLRS.Chapter04.substitution_lower_bound`,
  `CLRS.Chapter04.linear_substitution_upper_bound`,
  `CLRS.Chapter04.geometric_substitution_upper_bound`.
* 4.4 Recursion-tree method: `proved` for additive level-cost expansions.
  Public results: `CLRS.Chapter04.recursion_tree_additive_unroll`,
  `CLRS.Chapter04.recursion_tree_additive_upper_envelope`,
  `CLRS.Chapter04.recursion_tree_constant_level_cost`.
* 4.5 Master method: `proved` for exact-power recurrences.
  Public results: `CLRS.Chapter04.master_case1_geometric`,
  `CLRS.Chapter04.master_case2_constant_forcing`,
  `CLRS.Chapter04.master_case3_tail_dominated`.
* 4.6 Proof of the master theorem: `future-work`.
  Planned target: extend the exact-power proof to all natural input sizes with
  floor/ceiling sandwiching.
* 5.1 Hiring problem: `proved` for the finite rank-symmetry model.
  Public results: `CLRS.Chapter05.hireProbability_eq`,
  `CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`,
  `CLRS.Chapter05.expectedHires_isBigTheta_log`.
* 6.1 Heaps: `proved` for the indexed heap predicate and root maximum.
  Public results: `CLRS.Chapter06.parent_lt_self`,
  `CLRS.Chapter06.eq_left_or_right_parent`,
  `CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`,
  `CLRS.Chapter06.orderedDesc_arrayMaxHeap`.
* 6.2 Maintaining the heap property: `proved` for fuelled `MAX-HEAPIFY`
  recursive repair.
  Public results: `CLRS.Chapter06.swapAt_perm`,
  `CLRS.Chapter06.maxHeapifyFuel_perm`,
  `CLRS.Chapter06.valAt_i_le_maxChildIndex`,
  `CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`,
  `CLRS.Chapter06.maxHeapifyFuel_swap_branch_repair`,
  `CLRS.Chapter06.maxHeapifyFuel_repair_subtree`,
  `CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap`.
* 6.3 Building a heap: `proved` for bottom-up repeated heapify.
  Public results: `CLRS.Chapter06.buildMaxHeapLoop_isMaxHeap`,
  `CLRS.Chapter06.buildMaxHeapLoop_perm`,
  `CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap`,
  `CLRS.Chapter06.arrayBuildMaxHeap_correct`.
* 6.4 The heapsort algorithm: `proved` for the in-place CLRS loop refinement.
  Public results: `CLRS.Chapter06.arrayHeapSortInPlaceLoop_perm`,
  `CLRS.Chapter06.arrayHeapSortInPlaceLoop_length`,
  `CLRS.Chapter06.arrayHeapSortInPlace_perm`,
  `CLRS.Chapter06.arrayHeapSortInPlace_length`,
  `CLRS.Chapter06.arrayHeapSortStep_suffix_head_eq_root`,
  `CLRS.Chapter06.arrayHeapSortStep_suffix_head_bounds_prefix`,
  `CLRS.Chapter06.HeapSortLoopInvariant.step`,
  `CLRS.Chapter06.arrayHeapSortStep_state_correct`,
  `CLRS.Chapter06.arrayHeapSortInPlaceLoop_terminal_invariant`,
  `CLRS.Chapter06.arrayHeapSortInPlaceLoop_orderedAsc`,
  `CLRS.Chapter06.arrayHeapSortInPlaceLoop_state_correct`,
  `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_state_correct`,
  `CLRS.Chapter06.arrayHeapSortInPlace_terminal_invariant`,
  `CLRS.Chapter06.arrayHeapSortInPlace_orderedAsc`,
  `CLRS.Chapter06.arrayHeapSortInPlace_state_correct`,
  `CLRS.Chapter06.arrayHeapSortInPlace_exact_state_correct`,
  `CLRS.Chapter06.arrayHeapSortInPlace_correct`,
  `CLRS.Chapter06.arrayHeapSort_terminal_invariant`,
  `CLRS.Chapter06.arrayHeapSort_state_correct`,
  `CLRS.Chapter06.arrayHeapSort_exact_state_correct`,
  `CLRS.Chapter06.arrayHeapSort_orderedAsc`,
  `CLRS.Chapter06.arrayHeapSort_perm`,
  `CLRS.Chapter06.arrayHeapSort_correct`.
* 6.5 Priority queues: `proved` for the functional heap interface plus
  array-level `HEAP-MAXIMUM`, full fuelled `HEAP-INCREASE-KEY`, and
  `HEAP-EXTRACT-MAX` / `HEAP-DELETE`.
  Public results: `CLRS.Chapter06.heapInsert_orderedDesc`,
  `CLRS.Chapter06.heapInsert_perm`,
  `CLRS.Chapter06.heapIncreaseKey_orderedDesc`,
  `CLRS.Chapter06.heapDelete_orderedDesc`,
  `CLRS.Chapter06.arrayHeapMaximum?_max`,
  `CLRS.Chapter06.ArrayMaxHeap.set_increased_except_up`,
  `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubble_step`,
  `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubbleUpFuel_global`,
  `CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct`,
  `CLRS.Chapter06.arrayHeapIncreaseKeyNoBubble?_state_correct`,
  `CLRS.Chapter06.arrayHeapExtractMax?_state_correct`,
  `CLRS.Chapter06.arrayHeapDelete?_state_correct`.
* 7.1 Description of quicksort: `proved` for the functional-list model.
  Public results: `CLRS.Chapter07.partitionAround_perm`,
  `CLRS.Chapter07.partitionAround_left_allLeUpper`,
  `CLRS.Chapter07.partitionAround_right_allGt`,
  `CLRS.Chapter07.quickSort_perm`, `CLRS.Chapter07.quickSort_ordered`,
  `CLRS.Chapter07.quickSort_correct`.
* 7.2-7.4 Quicksort performance and randomized quicksort: `future-work`.
  Planned targets: in-place `PARTITION`, deterministic recurrence analysis,
  randomized quicksort, and expected running time.
* 10.1 Stacks and queues: `proved` for the functional-list model.
  Public results: `CLRS.Chapter10.pop_push`,
  `CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists: `proved` for the functional-list model.
  Public results: `CLRS.Chapter10.listSearch_sound`,
  `CLRS.Chapter10.mem_listDeleteAll_iff`.
* 11.1 Direct-address tables: `proved` for the functional table model.
  Public results: `CLRS.Chapter11.search_insert_same`,
  `CLRS.Chapter11.search_delete_same`.
* 11.2 Chained hash tables: `partial`.
  Current results: `CLRS.Chapter11.hashSearch_hashInsert_self`,
  `CLRS.Chapter11.hashSearch_hashInsert_iff`,
  `CLRS.Chapter11.hashSearch_hashDelete_self`,
  `CLRS.Chapter11.hashSearch_hashDelete_iff`.
* 12.1 Binary search trees: `partial`.
  Current results: `CLRS.Chapter12.BSTree.search_eq_true_iff`,
  `CLRS.Chapter12.BSTree.minimum?_le_of_ordered`,
  `CLRS.Chapter12.BSTree.le_maximum?_of_ordered`,
  `CLRS.Chapter12.BSTree.successor?_least_greater`,
  `CLRS.Chapter12.BSTree.predecessor?_greatest_less`,
  `CLRS.Chapter12.BSTree.inTree_insert_iff`,
  `CLRS.Chapter12.BSTree.insert_ordered`,
  `CLRS.Chapter12.BSTree.inTree_delete_iff`,
  `CLRS.Chapter12.BSTree.delete_ordered`.
* 13.1 Red-black trees: `partial`.
  Current results: `CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`,
  `CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`,
  `CLRS.Chapter13.RBTree.noRedRed_repaint_black`,
  `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`,
  `CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`,
  `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`,
  `CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`,
  `CLRS.Chapter13.RBTree.redBlackShape_repaint_black`.
* 16.1 Activity selection: `proved` for finite sorted lists.
  Current results: `CLRS.ActivitySelection.earliest_finish_minFinish`,
  `CLRS.ActivitySelection.finishSorted_head_minFinish`,
  `CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`,
  `CLRS.ActivitySelection.activitySelection`,
  `CLRS.ActivitySelection.activitySelection_cons_eq`,
  `CLRS.ActivitySelection.greedySelect_cons_eq`,
  `CLRS.ActivitySelection.greedySelect_sublist`,
  `CLRS.ActivitySelection.greedySelect_feasible`,
  `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`,
  `CLRS.ActivitySelection.greedySelect_after_maxCardinality`,
  `CLRS.ActivitySelection.greedySelect_cons_maxCardinality`,
  `CLRS.ActivitySelection.greedySelect_maxCardinality`,
  `CLRS.ActivitySelection.activitySelection_cons_maxCardinality`,
  `CLRS.ActivitySelection.activitySelection_maxCardinality`,
  `CLRS.ActivitySelection.greedySelect_optimal_length`,
  `CLRS.ActivitySelection.greedySelect_cons_recursive_correct`,
  `CLRS.ActivitySelection.activitySelection_cons_recursive_correct`,
  `CLRS.ActivitySelection.activitySelection_cons_correct`,
  `CLRS.ActivitySelection.activitySelection_correct`.
* 16.3 Huffman codes: `proved`.
  Public results: `CLRS.HuffmanV2.optimum_huffman_freqs`,
  `CLRS.HuffmanV2.huffmanOfFreqs_correct`, and
  `CLRS.HuffmanV2.huffmanOfFreqs_cost_le`.
* 23.1 Growing a minimum spanning tree: `partial`.
  Current results:
  `CLRS.MST.Graph.connected_crosses_cut`,
  `CLRS.MST.FiniteGraph.minimumSpanningTree_of_mstExtending_empty`,
  `CLRS.MST.FiniteGraph.mstExtending_empty_of_minimumSpanningTree`,
  `CLRS.MST.FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`,
  `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_of_cut`,
  `CLRS.MST.FiniteGraph.exists_crossing_tree_edge_preserving_prefix`, and
  `CLRS.MST.safe_edge_of_lightest_crossing`.
* 23.2 Kruskal and Prim: `partial`.
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

* `proved`: the named theorem is proved in Lean without relying on `sorry`.
* `expository`: the page is a reader guide rather than a theorem-bearing
  section.
* `partial`: important theorem infrastructure exists, but the full textbook
  section is not yet complete.
* `blocked-design`: progress needs a representation decision, such as paths,
  walks, heaps, arrays, or cost semantics.
* `deferred-implementation`: a low-level implementation proof is useful but not
  required for the current mathematical theorem.
* `future-work`: valuable extensions, exercises, or chapter-end problems.

## Build and Deployment

The deployed site is generated from the Lean source by Verso:

```
lake build
lake build :literateHtml
```

GitHub Actions runs the same pipeline and publishes the generated `_site`
directory to GitHub Pages.

Repository: [TankTechnology/CLRS-Lean](https://github.com/TankTechnology/CLRS-Lean)
-/
