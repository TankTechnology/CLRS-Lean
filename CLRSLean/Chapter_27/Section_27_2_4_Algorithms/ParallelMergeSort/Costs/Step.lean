import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Correctness

/-!
# CLRS Chapter 27.3 — P-MERGE-SORT Step Costs

This module exposes the exact work and span equations for one nontrivial
midpoint-split step of the executable P-MERGE-SORT algorithm.
-/

namespace CLRS
namespace Chapter27

/-- Exact work charged by a non-base P-MERGE-SORT step. -/
theorem pMergeSort_work_step_eq [LinearOrder α] (xs : List α)
    (hsmall : ¬ xs.length ≤ 1) :
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    (pMergeSort xs).work =
      (pMergeSort left).work + (pMergeSort right).work + 1 +
        (pMerge (pMergeSort left).value (pMergeSort right).value).work := by
  rw [pMergeSort]
  simp [hsmall]

/-- Exact span charged by a non-base P-MERGE-SORT step. -/
theorem pMergeSort_span_step_eq [LinearOrder α] (xs : List α)
    (hsmall : ¬ xs.length ≤ 1) :
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    (pMergeSort xs).span =
      max (pMergeSort left).span (pMergeSort right).span + 1 +
        (pMerge (pMergeSort left).value (pMergeSort right).value).span := by
  rw [pMergeSort]
  simp [hsmall]

end Chapter27
end CLRS
