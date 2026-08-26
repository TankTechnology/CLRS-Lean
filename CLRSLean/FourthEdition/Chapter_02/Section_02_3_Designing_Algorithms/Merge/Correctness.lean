import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Definitions

/-!
# CLRS Section 2.3 - MERGE correctness

The local executable MERGE is related to Mathlib's generic list merge only as
a proof bridge.  The public theorems speak directly about the Chapter 2
execution: exact erasure, element preservation, length, and sortedness.
-/

namespace CLRS
namespace Chapter02

/-- Reading the value field of the costed execution is exactly `merge`. -/
theorem mergeWithCost_value (left right : List Nat) :
    (mergeWithCost left right).value = merge left right := rfl

/-- The explicit Chapter 2 merge has the same value as the generic list merge. -/
private theorem merge_eq_listMerge (left right : List Nat) :
    merge left right = List.merge left right (fun x y => decide (x ≤ y)) := by
  induction left, right using mergeWithCost.induct with
  | case1 right =>
      simp [merge, mergeWithCost]
  | case2 left hleft =>
      cases left with
      | nil => exact (hleft rfl).elim
      | cons x xs => simp [merge, mergeWithCost]
  | case3 x xs y ys hxy ih =>
      simp [merge, mergeWithCost, hxy]
      change merge xs (y :: ys) = xs.merge (y :: ys) fun x y => decide (x ≤ y)
      exact ih
  | case4 x xs y ys hxy ih =>
      simp [merge, mergeWithCost, hxy]
      change merge (x :: xs) ys = (x :: xs).merge ys fun x y => decide (x ≤ y)
      exact ih

/-- MERGE preserves every input occurrence, including duplicates. -/
theorem merge_perm (left right : List Nat) :
    (merge left right).Perm (left ++ right) := by
  rw [merge_eq_listMerge]
  exact List.merge_perm_append (fun x y : Nat => decide (x ≤ y))

/-- The output length is the sum of the two input lengths. -/
theorem merge_length (left right : List Nat) :
    (merge left right).length = left.length + right.length := by
  simpa using (merge_perm left right).length_eq

/-- MERGE returns a nondecreasing list when both inputs are nondecreasing. -/
theorem merge_sorted {left right : List Nat}
    (hl : left.SortedLE) (hr : right.SortedLE) :
    (merge left right).SortedLE := by
  rw [merge_eq_listMerge]
  exact (List.Pairwise.merge hl.pairwise hr.pairwise).sortedLE

end Chapter02
end CLRS
