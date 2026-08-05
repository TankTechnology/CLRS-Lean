import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Correctness

/-!
# CLRS Chapter 27.3 — P-MERGE-SORT Specification

This module defines the semantic result predicate used by the P-MERGE-SORT
proof and records the two value-reconstruction facts needed by its induction.
-/

namespace CLRS
namespace Chapter27

/-- Semantic specification for a P-MERGE-SORT result: it is sorted, preserves
the input multiset, and has exactly the input length. -/
structure PMergeSortSpec [LinearOrder α] (xs out : List α) : Prop where
  sorted : out.Pairwise (· ≤ ·)
  perm : out.Perm xs
  length_eq : out.length = xs.length

namespace ParallelMergeSort
namespace Correctness

variable [LinearOrder α]

/-- Every list of length at most one is sorted, whether or not sortedness was
assumed of the input. -/
theorem pairwise_of_length_le_one (xs : List α) (hsmall : xs.length ≤ 1) :
    xs.Pairwise (· ≤ ·) := by
  cases xs with
  | nil => exact List.Pairwise.nil
  | cons x tail =>
      have htail : tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons] at hsmall
        omega
      subst tail
      simp

/-- On the base branch, the value returned by P-MERGE-SORT is the input list. -/
theorem value_eq_self (xs : List α) (hsmall : xs.length ≤ 1) :
    (pMergeSort xs).value = xs := by
  rw [pMergeSort]
  simp [hsmall]

/-- On a recursive branch, the value returned by P-MERGE-SORT is the value of
P-MERGE applied to the two recursively sorted halves. -/
theorem value_eq_merge (xs : List α) (hsmall : ¬ xs.length ≤ 1) :
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    (pMergeSort xs).value =
      (pMerge (pMergeSort left).value (pMergeSort right).value).value := by
  rw [pMergeSort]
  simp [hsmall]

end Correctness
end ParallelMergeSort

end Chapter27
end CLRS
