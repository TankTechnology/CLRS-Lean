import CLRSLean.Chapter_06.Section_06_1_Heaps
import CLRSLean.Chapter_06.Section_06_2_Maintaining_Heap_Property
import CLRSLean.Chapter_06.Section_06_3_Building_A_Heap
import CLRSLean.Chapter_06.Section_06_4_Heapsort
import CLRSLean.Chapter_06.Section_06_4_Heapsort.CostedExecution
import CLRSLean.Chapter_06.Section_06_5_Priority_Queues

/-!
# Chapter 6 - Heapsort

Chapter 6 introduces heaps, the heapsort algorithm, and max-priority queues.
The current CLRS-Lean pass has two layers.  The compact functional layer remains
as a small mathematical scaffold for sortedness and permutation facts.  The
reader-facing array layer now contains the zero-based CLRS child/parent
formulas, an indexed heap predicate, {lit}`MAX-HEAPIFY`'s recursive repair
theorem, bottom-up {lit}`BUILD-MAX-HEAP` by repeated heapify, the executable
in-place {lit}`HEAPSORT` loop with a proved sorted-suffix invariant and
sortedness theorem, and the array-level {lit}`HEAP-MAXIMUM` theorem.
The heapsort execution also has an erasure-linked unit control-step layer that
counts visited {lit}`MAX-HEAPIFY` frames and nontrivial extraction transitions.

## Sections

* 6.1 Heaps: {lit}`proved` for the indexed heap predicate and root maximum.
  Main results:
  {lit}`CLRS.Chapter06.parent_lt_self`,
  {lit}`CLRS.Chapter06.eq_left_or_right_parent`,
  {lit}`CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`, and
  {lit}`CLRS.Chapter06.orderedDesc_arrayMaxHeap`; localized predicates:
  {lit}`CLRS.Chapter06.ArrayMaxHeapFrom.to_global` and
  {lit}`CLRS.Chapter06.ArrayMaxHeapExceptFrom.to_global`.
* 6.2 Maintaining the heap property: {lit}`proved` for fuelled
  {lit}`MAX-HEAPIFY` recursive repair.  Main results:
  {lit}`CLRS.Chapter06.swapAt_perm`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_perm`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_valAt_of_heapSize_le`, and
  {lit}`CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`;
  recursive repair:
  {lit}`CLRS.Chapter06.maxHeapifyFuel_child_repair_after_swap`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_swap_branch_repair`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_repair_subtree` and
  {lit}`CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap`.
* 6.3 Building a heap: {lit}`proved` for the bottom-up repeated
  {lit}`MAX-HEAPIFY` builder.  Main results:
  {lit}`CLRS.Chapter06.ArrayMaxHeapFrom.of_half`,
  {lit}`CLRS.Chapter06.buildMaxHeapLoop_isMaxHeap`,
  {lit}`CLRS.Chapter06.buildMaxHeapLoop_perm`,
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap` and
  {lit}`CLRS.Chapter06.arrayBuildMaxHeap_correct`.
* 6.4 The heapsort algorithm: {lit}`proved` for the in-place CLRS loop
  refinement.  Loop facts:
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_length`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_perm`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_length`, and
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_perm`; invariant facts:
  {lit}`CLRS.Chapter06.HeapSortLoopInvariant.initial`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_suffix_head_eq_root`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_suffix_head_bounds_prefix`,
  {lit}`CLRS.Chapter06.HeapSortLoopInvariant.step`,
  {lit}`CLRS.Chapter06.arrayHeapSortStep_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_shrink_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_terminal_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_terminal_invariant`, and
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_orderedAsc`; state package:
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_state_correct` and
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_state_correct`.  Main
  specification results:
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_terminal_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_orderedAsc`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_exact_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlace_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSort_eq_arrayHeapSortInPlace`,
  {lit}`CLRS.Chapter06.arrayHeapSort_terminal_invariant`,
  {lit}`CLRS.Chapter06.arrayHeapSort_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSort_exact_state_correct`, and
  {lit}`CLRS.Chapter06.arrayHeapSort_correct`.
  Costed-execution results:
  {lit}`CLRS.Chapter06.maxHeapifyFuelWithCost_result`,
  {lit}`CLRS.Chapter06.arrayBuildMaxHeapWithCost_correct`,
  {lit}`CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_cost`,
  {lit}`CLRS.Chapter06.maxHeapifyControlBound_isBigO_n`,
  {lit}`CLRS.Chapter06.buildMaxHeapControlBound_isBigO_nsq`, and
  {lit}`CLRS.Chapter06.heapSortControlBound_isBigO_nsq`.
* 6.5 Priority queues: {lit}`proved` for the functional heap interface, with
  array-level {lit}`HEAP-MAXIMUM`, full fuelled
  {lit}`HEAP-INCREASE-KEY`, {lit}`HEAP-EXTRACT-MAX`, and
  {lit}`HEAP-DELETE` state theorems.
  Main results:
  {lit}`CLRS.Chapter06.heapInsert_orderedDesc`,
  {lit}`CLRS.Chapter06.heapInsert_perm`,
  {lit}`CLRS.Chapter06.heapIncreaseKey_orderedDesc`, and
  {lit}`CLRS.Chapter06.heapDelete_orderedDesc`; array result:
  {lit}`CLRS.Chapter06.arrayHeapMaximum?_max`,
  {lit}`CLRS.Chapter06.ArrayMaxHeap.set_increased_except_up`,
  {lit}`CLRS.Chapter06.ArrayMaxHeapExceptUp.bubble_step`,
  {lit}`CLRS.Chapter06.ArrayMaxHeapExceptUp.bubbleUpFuel_global`,
  {lit}`CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapIncreaseKeyNoBubble?_state_correct`,
  {lit}`CLRS.Chapter06.arrayHeapExtractMax?_state_correct`, and
  {lit}`CLRS.Chapter06.arrayHeapDelete?_state_correct`.

## Current Gaps

The proved metric is deliberately coarse: build orchestration is free, while
visited heapify frames and nontrivial extraction transitions are charged.
Tight textbook {lit}`O(log n)`, {lit}`O(n)`, and {lit}`O(n log n)` bounds,
the costs of guards and list operations, and an imperative RAM refinement
remain open.
-/

namespace CLRS
namespace Chapter06
end Chapter06
end CLRS
