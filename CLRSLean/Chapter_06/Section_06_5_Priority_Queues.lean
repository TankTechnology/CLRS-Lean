import CLRSLean.Chapter_06.Section_06_1_Array_Heaps

/-!
# CLRS Section 6.5 - Priority Queues

This file gives a functional priority-queue interface on top of the Chapter 6
descending-list heap model.  The operations rebuild or maintain the abstract
heap invariant directly; array positions, parent/child index updates, and
imperative key mutation are left as refinement targets.

Main results:

- Theorem {lit}`heapInsert_orderedDesc`: inserting into a heap preserves the
  heap invariant.
- Theorem {lit}`heapInsert_perm`: insertion adds exactly the inserted key.
- Theorem {lit}`heapIncreaseKey_orderedDesc`: increasing one occurrence and
  rebuilding produces a heap.
- Theorem {lit}`heapDelete_orderedDesc`: deleting one occurrence and rebuilding
  produces a heap.
- Theorem {lit}`arrayHeapMaximum?_max`: the root returned by the array-level
  maximum operation bounds every key in the heap prefix.

Current gaps:

- The CLRS index-based {lit}`HEAP-INCREASE-KEY` and {lit}`HEAP-DELETE`
  procedures are not yet refined to array updates.
- Runtime bounds and RAM semantics are deferred.
-/

namespace CLRS
namespace Chapter06

/-! ## Functional priority-queue operations -/

/-- Insert a key into the functional max-priority queue. -/
def heapInsert (x : Nat) (h : List Nat) : List Nat :=
  insertDesc x h

/--
Increase one occurrence of {lit}`old` to {lit}`new`, then rebuild the abstract heap.
If {lit}`old` is absent this inserts {lit}`new`; this total behavior avoids exceptions in
the mathematical interface.
-/
def heapIncreaseKey (old new : Nat) (h : List Nat) : List Nat :=
  buildMaxHeap (new :: h.erase old)

/-- Delete one occurrence of {lit}`key`, then rebuild the abstract heap. -/
def heapDelete (key : Nat) (h : List Nat) : List Nat :=
  buildMaxHeap (h.erase key)

/-! ## Correctness theorems -/

/-- Priority-queue insertion preserves the heap invariant. -/
theorem heapInsert_orderedDesc {x : Nat} {h : List Nat}
    (hh : OrderedDesc h) : OrderedDesc (heapInsert x h) := by
  exact insertDesc_orderedDesc hh

/-- Priority-queue insertion adds exactly the inserted key. -/
theorem heapInsert_perm (x : Nat) (h : List Nat) :
    (heapInsert x h).Perm (x :: h) := by
  exact insertDesc_perm x h

/-- The maximum after insertion is maximal among the old keys and the new key. -/
theorem heapInsert_max {x m : Nat} {h : List Nat}
    (hh : OrderedDesc h) (hmax : heapMaximum? (heapInsert x h) = some m) :
    ∀ y ∈ x :: h, y ≤ m := by
  intro y hy
  have hyheap : y ∈ heapInsert x h :=
    (List.Perm.mem_iff (heapInsert_perm x h)).2 hy
  exact heapMaximum?_max (heapInsert_orderedDesc hh) hmax y hyheap

/-- Increasing a key and rebuilding returns a heap. -/
theorem heapIncreaseKey_orderedDesc (old new : Nat) (h : List Nat) :
    OrderedDesc (heapIncreaseKey old new h) := by
  exact buildMaxHeap_orderedDesc (new :: h.erase old)

/-- Increasing a key preserves exactly the rebuilt multiset specification. -/
theorem heapIncreaseKey_perm (old new : Nat) (h : List Nat) :
    (heapIncreaseKey old new h).Perm (new :: h.erase old) := by
  exact buildMaxHeap_perm (new :: h.erase old)

/-- Deleting one key occurrence and rebuilding returns a heap. -/
theorem heapDelete_orderedDesc (key : Nat) (h : List Nat) :
    OrderedDesc (heapDelete key h) := by
  exact buildMaxHeap_orderedDesc (h.erase key)

/-- Deleting one key occurrence preserves exactly the rebuilt multiset specification. -/
theorem heapDelete_perm (key : Nat) (h : List Nat) :
    (heapDelete key h).Perm (h.erase key) := by
  exact buildMaxHeap_perm (h.erase key)

/-! ## Array-level maximum operation -/

/--
Array-level `HEAP-MAXIMUM`: return the root when the heap prefix is nonempty
and within the backing list.
-/
def arrayHeapMaximum? (a : List Nat) (heapSize : Nat) : Option Nat :=
  if h : 0 < heapSize ∧ heapSize ≤ a.length then
    some (a[0]'(Nat.lt_of_lt_of_le h.1 h.2))
  else
    none

/-- The array-level maximum returned from the root bounds every heap element. -/
theorem arrayHeapMaximum?_max {a : List Nat} {heapSize m : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hmax : arrayHeapMaximum? a heapSize = some m) :
    ∀ {i : Nat}, (hi : i < heapSize) →
      a[i]'(Nat.lt_of_lt_of_le hi hheap.heapSize_le_length) ≤ m := by
  intro i hi
  have hnonempty : 0 < heapSize := Nat.zero_lt_of_lt hi
  have hcond : 0 < heapSize ∧ heapSize ≤ a.length :=
    ⟨hnonempty, hheap.heapSize_le_length⟩
  have hroot :
      a[0]'(Nat.lt_of_lt_of_le hnonempty hheap.heapSize_le_length) = m := by
    simpa [arrayHeapMaximum?, hcond] using hmax
  rw [← hroot]
  exact hheap.getElem_le_root hi

end Chapter06
end CLRS
