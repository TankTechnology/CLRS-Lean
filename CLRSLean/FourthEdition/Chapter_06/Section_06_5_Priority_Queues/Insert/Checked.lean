import CLRSLean.FourthEdition.Chapter_06.Section_06_5_Priority_Queues.Insert.Basic

/-!
# Section 6.5 — Checked active-prefix MAX-HEAP-INSERT

The checked list-backed operation accepts exactly the states whose active heap
prefix fits in the backing list.  It inserts a new cell between that prefix and
the inactive tail, preserving the tail order.
-/

namespace CLRS
namespace Chapter06

/-- Restricting a heap to its active prefix preserves the indexed heap. -/
theorem ArrayMaxHeap.take {a : List Nat} {heapSize : Nat}
    (hheap : ArrayMaxHeap a heapSize) :
    ArrayMaxHeap (a.take heapSize) heapSize := by
  have hlen : (a.take heapSize).length = heapSize :=
    List.length_take_of_le hheap.heapSize_le_length
  refine ⟨by simp [hlen], ?_, ?_⟩
  · intro i hi hl
    simpa only [List.getElem_take] using hheap.left_le hi hl
  · intro i hi hr
    simpa only [List.getElem_take] using hheap.right_le hi hr

/-- Appending an inactive tail does not change heap obligations in the prefix. -/
theorem ArrayMaxHeap.append_tail {xs tail : List Nat} {heapSize : Nat}
    (hheap : ArrayMaxHeap xs heapSize) :
    ArrayMaxHeap (xs ++ tail) heapSize := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      heapSize ≤ xs.length := hheap.heapSize_le_length
      _ ≤ (xs ++ tail).length := by simp
  · intro i hi hl
    have hiPrefix : i < xs.length :=
      Nat.lt_of_lt_of_le hi hheap.heapSize_le_length
    have hlPrefix : left i < xs.length :=
      Nat.lt_of_lt_of_le hl hheap.heapSize_le_length
    simpa only [List.getElem_append_left hiPrefix,
      List.getElem_append_left hlPrefix] using hheap.left_le hi hl
  · intro i hi hr
    have hiPrefix : i < xs.length :=
      Nat.lt_of_lt_of_le hi hheap.heapSize_le_length
    have hrPrefix : right i < xs.length :=
      Nat.lt_of_lt_of_le hr hheap.heapSize_le_length
    simpa only [List.getElem_append_left hiPrefix,
      List.getElem_append_left hrPrefix] using hheap.right_le hi hr

/--
Total checked insertion into an active heap prefix.  The inactive tail remains
after the newly enlarged prefix; an out-of-range heap size is rejected.
-/
def arrayHeapInsert? (a : List Nat) (heapSize key : Nat) : Option (List Nat × Nat) :=
  if _h : heapSize ≤ a.length then
    some
      (arrayHeapInsert (a.take heapSize) key ++ a.drop heapSize,
        heapSize + 1)
  else
    none

/-- Checked insertion fails exactly when the active prefix exceeds the backing list. -/
theorem arrayHeapInsert?_eq_none_iff (a : List Nat) (heapSize key : Nat) :
    arrayHeapInsert? a heapSize key = none ↔ ¬ heapSize ≤ a.length := by
  unfold arrayHeapInsert?
  by_cases h : heapSize ≤ a.length <;> simp [h]

/-- Exact guard and output characterization for successful checked insertion. -/
theorem arrayHeapInsert?_eq_some_iff
    (a rest : List Nat) (heapSize newHeapSize key : Nat) :
    arrayHeapInsert? a heapSize key = some (rest, newHeapSize) ↔
      heapSize ≤ a.length ∧
        rest = arrayHeapInsert (a.take heapSize) key ++ a.drop heapSize ∧
        newHeapSize = heapSize + 1 := by
  unfold arrayHeapInsert?
  by_cases h : heapSize ≤ a.length
  · rw [dif_pos h]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hrest, hsize⟩
      exact ⟨h, hrest.symm, hsize.symm⟩
    · rintro ⟨_, hrest, hsize⟩
      exact ⟨hrest.symm, hsize.symm⟩
  · rw [dif_neg h]
    simp [h]

/--
Successful checked insertion grows the active heap and backing list by one,
preserves the inactive tail order, and adds exactly the requested key.
-/
theorem arrayHeapInsert?_state_correct
    {a rest : List Nat} {heapSize newHeapSize key : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hres : arrayHeapInsert? a heapSize key = some (rest, newHeapSize)) :
    heapSize ≤ a.length ∧
      newHeapSize = heapSize + 1 ∧
      rest.length = a.length + 1 ∧
      ArrayMaxHeap rest newHeapSize ∧
      rest.Perm (key :: a) ∧
      rest.drop newHeapSize = a.drop heapSize := by
  have hspec := (arrayHeapInsert?_eq_some_iff
    a rest heapSize newHeapSize key).1 hres
  rcases hspec with ⟨hguard, rfl, rfl⟩
  have htakeLen : (a.take heapSize).length = heapSize :=
    List.length_take_of_le hguard
  have hprefixHeap :
      ArrayMaxHeap (a.take heapSize) (a.take heapSize).length := by
    simpa [htakeLen] using hheap.take
  have hinsertHeap := arrayHeapInsert_isMaxHeap key hprefixHeap
  have hresultHeap :
      ArrayMaxHeap
        (arrayHeapInsert (a.take heapSize) key ++ a.drop heapSize)
        (heapSize + 1) := by
    simpa [htakeLen] using hinsertHeap.append_tail (tail := a.drop heapSize)
  have hlength :
      (arrayHeapInsert (a.take heapSize) key ++ a.drop heapSize).length =
        a.length + 1 := by
    rw [List.length_append, arrayHeapInsert_length]
    simp only [htakeLen, List.length_drop]
    have hsplit := Nat.sub_add_cancel hguard
    omega
  have hpermPrefix :=
    (arrayHeapInsert_perm (a.take heapSize) key).append_right (a.drop heapSize)
  have hperm :
      (arrayHeapInsert (a.take heapSize) key ++ a.drop heapSize).Perm
        (key :: a) := by
    simpa [List.take_append_drop] using hpermPrefix
  have hinsertLen :
      (arrayHeapInsert (a.take heapSize) key).length = heapSize + 1 := by
    simpa [htakeLen] using arrayHeapInsert_length (a.take heapSize) key
  have htail :
      (arrayHeapInsert (a.take heapSize) key ++ a.drop heapSize).drop
          (heapSize + 1) =
        a.drop heapSize := by
    rw [← hinsertLen]
    exact List.drop_left
  exact ⟨hguard, rfl, hlength, hresultHeap, hperm, htail⟩

end Chapter06
end CLRS
