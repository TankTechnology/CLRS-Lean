# Chapter 6 - Heapsort

Chapter 6 now has one public file per CLRS section.  The implementation still
has a compact functional heap scaffold, but the reader-facing layer separates
the array heap predicate, recursive `MAX-HEAPIFY` repair, bottom-up
`BUILD-MAX-HEAP`, the in-place heapsort loop with a proved sorted-suffix
invariant and sortedness theorem, an erasure-linked unit control-step model,
and priority-queue operations.

## Completed

- Section 6.1, heaps:
  - `CLRS.Chapter06.parent_lt_self`
  - `CLRS.Chapter06.eq_left_or_right_parent`
  - `CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`
  - `CLRS.Chapter06.ArrayMaxHeapFrom.to_global`
  - `CLRS.Chapter06.ArrayMaxHeapExceptFrom.to_global`
  - `CLRS.Chapter06.orderedDesc_arrayMaxHeap`
- Section 6.2, maintaining the heap property:
  - `CLRS.Chapter06.swapAt_perm`
  - `CLRS.Chapter06.maxHeapifyFuel_perm`
  - `CLRS.Chapter06.valAt_i_le_maxChildIndex`
  - `CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`
  - `CLRS.Chapter06.arrayMaxHeapFrom_of_exceptFrom_of_maxChildIndex_self`
  - `CLRS.Chapter06.maxChildIndex_eq_left_or_right_of_ne`
  - `CLRS.Chapter06.heapSize_sub_maxChildIndex_lt_of_ne`
  - `CLRS.Chapter06.arrayMaxHeapExceptFrom_after_swap_at_root`
  - `CLRS.Chapter06.arrayMaxHeapFrom_of_maxHeapifyFuel_succ`
  - `CLRS.Chapter06.arrayMaxHeapExceptFrom_after_swap_path`
  - `CLRS.Chapter06.badChildrenLeParent_after_swap`
  - `CLRS.Chapter06.arrayMaxHeapFrom_of_maxHeapifyFuel`
  - `CLRS.Chapter06.maxHeapifyFuel_child_repair_after_swap`
  - `CLRS.Chapter06.maxHeapifyFuel_swap_branch_repair`
  - `CLRS.Chapter06.maxHeapifyFuel_repair_subtree`
  - `CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap`
  - `CLRS.Chapter06.maxHeapifyFuel_valAt_of_heapSize_le`
- Section 6.3, building a heap:
  - `CLRS.Chapter06.ArrayMaxHeapFrom.of_half`
  - `CLRS.Chapter06.buildMaxHeapLoop_isMaxHeap`
  - `CLRS.Chapter06.buildMaxHeapLoop_perm`
  - `CLRS.Chapter06.arrayBuildMaxHeap_isMaxHeap`
  - `CLRS.Chapter06.arrayBuildMaxHeap_perm`
  - `CLRS.Chapter06.arrayBuildMaxHeap_correct`
- Section 6.4, the heapsort algorithm:
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_length`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_perm`
  - `CLRS.Chapter06.arrayHeapSortInPlace_length`
  - `CLRS.Chapter06.arrayHeapSortInPlace_perm`
  - `CLRS.Chapter06.HeapSortLoopInvariant.initial`
  - `CLRS.Chapter06.arrayHeapSortStep_suffix_head_eq_root`
  - `CLRS.Chapter06.arrayHeapSortStep_suffix_head_bounds_prefix`
  - `CLRS.Chapter06.HeapSortLoopInvariant.step`
  - `CLRS.Chapter06.arrayHeapSortStep_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_shrink_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_orderedAsc`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlaceLoop_exact_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlace_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSortInPlace_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlace_exact_state_correct`
  - `CLRS.Chapter06.arrayHeapSortInPlace_orderedAsc`
  - `CLRS.Chapter06.arrayHeapSortInPlace_correct`
  - `CLRS.Chapter06.arrayHeapSort_eq_arrayHeapSortInPlace`
  - `CLRS.Chapter06.arrayHeapSort_terminal_invariant`
  - `CLRS.Chapter06.arrayHeapSort_state_correct`
  - `CLRS.Chapter06.arrayHeapSort_exact_state_correct`
  - `CLRS.Chapter06.arrayHeapSort_orderedAsc`
  - `CLRS.Chapter06.arrayHeapSort_perm`
  - `CLRS.Chapter06.arrayHeapSort_correct`
  - Costed execution and erasure:
    - `CLRS.Chapter06.maxHeapifyFuelWithCost_result`
    - `CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_fuel`
    - `CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_controlBound`
    - `CLRS.Chapter06.buildMaxHeapLoopWithCost_result`
    - `CLRS.Chapter06.buildMaxHeapLoopWithCost_cost_le`
    - `CLRS.Chapter06.arrayBuildMaxHeapWithCost_result`
    - `CLRS.Chapter06.arrayBuildMaxHeapWithCost_correct`
    - `CLRS.Chapter06.arrayBuildMaxHeapWithCost_cost_le`
    - `CLRS.Chapter06.arrayHeapSortStepWithCost_result`
    - `CLRS.Chapter06.arrayHeapSortStepWithCost_cost_le_heapSize`
    - `CLRS.Chapter06.arrayHeapSortInPlaceLoopWithCost_result`
    - `CLRS.Chapter06.arrayHeapSortInPlaceLoopWithCost_cost_le`
    - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_result`
    - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_cost_le`
    - `CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_cost`
    - `CLRS.Chapter06.maxHeapifyControlBound_isBigO_n`
    - `CLRS.Chapter06.buildMaxHeapControlBound_isBigO_nsq`
    - `CLRS.Chapter06.heapSortControlBound_isBigO_nsq`
- Section 6.5, priority queues:
  - `CLRS.Chapter06.heapInsert_orderedDesc`
  - `CLRS.Chapter06.heapInsert_perm`
  - `CLRS.Chapter06.heapInsert_max`
  - `CLRS.Chapter06.heapIncreaseKey_orderedDesc`
  - `CLRS.Chapter06.heapIncreaseKey_perm`
  - `CLRS.Chapter06.heapDelete_orderedDesc`
  - `CLRS.Chapter06.heapDelete_perm`
  - `CLRS.Chapter06.arrayHeapMaximum?_max`
  - `CLRS.Chapter06.ArrayMaxHeap.set_increased_except_up`
  - `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubble_step`
  - `CLRS.Chapter06.ArrayMaxHeapExceptUp.bubbleUpFuel_global`
  - `CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct`
  - `CLRS.Chapter06.arrayHeapIncreaseKeyNoBubble?_state_correct`
  - `CLRS.Chapter06.arrayHeapExtractMax?_state_correct`
  - `CLRS.Chapter06.arrayHeapDelete?_state_correct`

## Open Refinements

- The costed execution counts visited `MAX-HEAPIFY` frames and one
  extraction/swap transition for every nontrivial heapsort step.  The
  bottom-up build loop only sums heapify-frame counts; its orchestration is not
  charged separately.  Guards, `List` reads/writes, allocation, and calls are
  also outside this metric.
- The current connected envelopes intentionally prove only `O(n)` for the
  heapify fuel bound and `O(n^2)` for both build-heap and heapsort.  Tight
  textbook `O(log n)`, `O(n)`, and `O(n log n)` bounds remain open.
- Add an imperative array/RAM refinement that charges concrete list or array
  operations and connects those charges to the textbook bounds.
