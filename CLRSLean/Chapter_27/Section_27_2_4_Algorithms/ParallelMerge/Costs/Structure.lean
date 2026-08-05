import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Definitions

/-!
# CLRS Chapter 27.3 — P-MERGE Structural Cost Bounds

This module exposes the exact child-size accounting of the executable split
and proves the actual CLRS three-quarter shrink bound.  The proof uses the
midpoint of the longer normalized input and the lower-bound index in the
shorter input; it does not replace P-MERGE by a half-size recurrence.
-/

namespace CLRS
namespace Chapter27

universe u

/-- The two recursive P-MERGE children contain every input element except the
chosen primary pivot. -/
theorem pMerge_childSizes_add_one [LinearOrder α] (S : MergeSplit α) :
    S.leftSize + S.rightSize + 1 = S.totalSize :=
  S.childSizes_add_one

private theorem child_size_le_threeQuarters_arith
    (primary secondary split : ℕ)
    (hsecondary : secondary ≤ primary)
    (hsplit : split ≤ secondary) :
    primary / 2 + split ≤
        primary + secondary - (primary + secondary) / 4 ∧
      (primary - (primary / 2 + 1)) + (secondary - split) ≤
        primary + secondary - (primary + secondary) / 4 := by
  omega

/-- Each actual P-MERGE child has size at most three quarters of the parent.

The statement deliberately uses {lit}`n - n / 4`, the natural-number form that
also covers all small totals without auxiliary positivity side conditions.
-/
theorem pMerge_childSize_le_threeQuarters [LinearOrder α] (S : MergeSplit α) :
    S.leftSize ≤ S.totalSize - S.totalSize / 4 ∧
      S.rightSize ≤ S.totalSize - S.totalSize / 4 := by
  have hi : S.primary.length / 2 ≤ S.primary.length :=
    Nat.le_of_lt S.pivotIndex_lt
  have hj : S.splitIndex ≤ S.secondary.length := S.splitIndex_le_secondary
  have harith := child_size_le_threeQuarters_arith
    S.primary.length S.secondary.length S.splitIndex
    S.secondary_length_le_primary hj
  have htotal : S.primary.length + S.secondary.length = S.totalSize := by
    simpa [MergeSplit.totalSize] using S.normalized_total
  simpa [MergeSplit.leftSize, MergeSplit.rightSize,
    MergeSplit.lowerPrimary, MergeSplit.lowerSecondary,
    MergeSplit.upperPrimary, MergeSplit.upperSecondary,
    MergeSplit.pivotIndex, List.length_take, Nat.min_eq_left hi,
    Nat.min_eq_left hj, htotal] using harith

end Chapter27
end CLRS
