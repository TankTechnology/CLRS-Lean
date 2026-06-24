import CLRSLean.Chapter_06.Section_06_1_Heapsort
import CLRSLean.Chapter_06.Section_06_1_Array_Heaps
import CLRSLean.Chapter_06.Section_06_5_Priority_Queues

/-!
# Chapter 6 - Heapsort

Chapter 6 introduces heaps, the heapsort algorithm, and max-priority queues.
The current CLRS-Lean pass has two layers.  The compact functional layer proves
the mathematical heapsort specification: heap construction preserves elements,
the heap maximum is genuinely maximal, and heapsort returns an ascending
permutation.  The array layer adds the zero-based CLRS child/parent formulas,
an indexed heap predicate, `MAX-HEAPIFY`'s `largest` choice facts, no-swap
repair, swap permutation/read lemmas, and the array-level `HEAP-MAXIMUM`
theorem.

## Sections

* 6.1-6.4 Heaps and heapsort: {lit}`proved` for the functional descending-list
  model and {lit}`partial` for the CLRS array refinement.  Main results:
  {lit}`CLRS.Chapter06.buildMaxHeap_orderedDesc`,
  {lit}`CLRS.Chapter06.buildMaxHeap_perm`,
  {lit}`CLRS.Chapter06.buildMaxHeap_max`,
  {lit}`CLRS.Chapter06.heapSort_orderedAsc`, and
  {lit}`CLRS.Chapter06.heapSort_perm`; array-layer results include
  {lit}`CLRS.Chapter06.ArrayMaxHeap.getElem_le_root`,
  {lit}`CLRS.Chapter06.maxHeapifyFuel_perm`, and
  {lit}`CLRS.Chapter06.arrayMaxHeap_of_except_of_maxChildIndex_self`.
* 6.5 Priority queues: {lit}`proved` for the functional heap interface, with an
  array-level maximum theorem.  Main results:
  {lit}`CLRS.Chapter06.heapInsert_orderedDesc`,
  {lit}`CLRS.Chapter06.heapInsert_perm`,
  {lit}`CLRS.Chapter06.heapIncreaseKey_orderedDesc`, and
  {lit}`CLRS.Chapter06.heapDelete_orderedDesc`; array result:
  {lit}`CLRS.Chapter06.arrayHeapMaximum?_max`.

## Current Gaps

The full recursive repair theorem for the swap branch of {lit}`MAX-HEAPIFY`,
bottom-up {lit}`BUILD-MAX-HEAP` as repeated heapify, the in-place heapsort loop
with shrinking heap prefix and sorted suffix, index-based {lit}`HEAP-INCREASE-KEY`
and {lit}`HEAP-DELETE`, and runtime/RAM semantics remain refinement targets.
-/

namespace CLRS
namespace Chapter06
end Chapter06
end CLRS
