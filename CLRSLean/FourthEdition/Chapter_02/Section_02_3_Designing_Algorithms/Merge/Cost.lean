import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Correctness

/-!
# CLRS Section 2.3 - MERGE comparison cost

This module proves the linear comparison bound for the same execution whose
value is proved correct in `Merge.Correctness`.
-/

namespace CLRS
namespace Chapter02

/-- MERGE performs at most one head comparison per available input element. -/
theorem merge_comparisons_le (left right : List Nat) :
    (mergeWithCost left right).comparisons ≤ left.length + right.length := by
  induction left, right using mergeWithCost.induct with
  | case1 right =>
      simp [mergeWithCost]
  | case2 left hleft =>
      cases left with
      | nil => exact (hleft rfl).elim
      | cons x xs => simp [mergeWithCost]
  | case3 x xs y ys hxy ih =>
      simp [mergeWithCost, hxy] at ih ⊢
      omega
  | case4 x xs y ys hxy ih =>
      simp [mergeWithCost, hxy] at ih ⊢
      omega

/-- MERGE writes each output element exactly once, including copied suffixes. -/
theorem merge_outputWrites_eq (left right : List Nat) :
    (mergeWithCost left right).outputWrites = left.length + right.length := by
  induction left, right using mergeWithCost.induct with
  | case1 right =>
      simp [mergeWithCost]
  | case2 left hleft =>
      cases left with
      | nil => exact (hleft rfl).elim
      | cons x xs => simp [mergeWithCost]
  | case3 x xs y ys hxy ih =>
      simp [mergeWithCost, hxy] at ih ⊢
      omega
  | case4 x xs y ys hxy ih =>
      simp [mergeWithCost, hxy] at ih ⊢
      omega

/--
The textbook list-level MERGE contract: sorted output, exact multiset
preservation, a linear number of head comparisons, and exactly one output
write per input element.
-/
theorem merge_correct {left right : List Nat}
    (hl : left.SortedLE) (hr : right.SortedLE) :
    (merge left right).SortedLE ∧
      (merge left right).Perm (left ++ right) ∧
      (mergeWithCost left right).comparisons ≤ left.length + right.length ∧
      (mergeWithCost left right).outputWrites = left.length + right.length := by
  exact ⟨merge_sorted hl hr, merge_perm left right, merge_comparisons_le left right,
    merge_outputWrites_eq left right⟩

end Chapter02
end CLRS
