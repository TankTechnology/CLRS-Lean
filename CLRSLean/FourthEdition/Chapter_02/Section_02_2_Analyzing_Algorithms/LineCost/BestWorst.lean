import CLRSLean.FourthEdition.Chapter_02.Section_02_2_Analyzing_Algorithms.LineCost.Formula

/-!
# CLRS Section 2.2 - Best- and worst-case line counts

This module specializes the generic cost table to the textbook traces
`tᵢ = 1` (already sorted input) and `tᵢ = i` (reverse-sorted input).
-/

namespace CLRS
namespace Chapter02

/-- Best-case while trace: each outer iteration tests the condition once. -/
def insertionSortBestTrace : Nat → Nat := fun _ => 1

/-- Worst-case while trace: outer iteration `i` tests the condition `i` times. -/
def insertionSortWorstTrace : Nat → Nat := fun i => i

private theorem sum_range_succ_eq_triangular (m : Nat) :
    (∑ k ∈ Finset.range m, (k + 1)) = triangular m := by
  induction m with
  | zero => simp [triangular]
  | succ m ih =>
      simp [Finset.sum_range_succ, triangular, ih]

private theorem sum_range_add_two_eq (m : Nat) :
    (∑ k ∈ Finset.range m, (k + 2)) = triangular m + m := by
  induction m with
  | zero => simp [triangular]
  | succ m ih =>
      simp [Finset.sum_range_succ, triangular, ih]
      omega

/-- The exact execution-count table for the already-sorted best case. -/
theorem insertionSortLineCounts_best_case (n : Nat) :
    insertionSortLineCounts n insertionSortBestTrace =
      { forLoopTests := n
        keyAssignments := n - 1
        indexInitializations := n - 1
        whileLoopTests := n - 1
        shifts := 0
        decrements := 0
        finalAssignments := n - 1 } := by
  ext <;>
    simp [insertionSortLineCounts, insertionSortWhileTestSum,
      insertionSortBodyIterationSum, insertionSortBestTrace]

/-- The exact execution-count table for the reverse-sorted worst case. -/
theorem insertionSortLineCounts_worst_case (n : Nat) :
    insertionSortLineCounts n insertionSortWorstTrace =
      { forLoopTests := n
        keyAssignments := n - 1
        indexInitializations := n - 1
        whileLoopTests := triangular (n - 1) + (n - 1)
        shifts := triangular (n - 1)
        decrements := triangular (n - 1)
        finalAssignments := n - 1 } := by
  ext <;>
    simp [insertionSortLineCounts, insertionSortWhileTestSum,
      insertionSortBodyIterationSum, insertionSortWorstTrace,
      sum_range_succ_eq_triangular, sum_range_add_two_eq]

/-- Complete best-case line-cost formula after substituting `tᵢ = 1`. -/
theorem insertionSortRunningTime_best_case
    (costs : InsertionSortLineCosts) (n : Nat) :
    insertionSortRunningTime costs n insertionSortBestTrace =
      costs.c₁ * n +
        costs.c₂ * (n - 1) +
        costs.c₄ * (n - 1) +
        costs.c₅ * (n - 1) +
        costs.c₈ * (n - 1) := by
  rw [insertionSortRunningTime, insertionSortLineCounts_best_case]
  simp [InsertionSortLineCosts.evaluate]

/-- Complete worst-case line-cost formula after substituting `tᵢ = i`. -/
theorem insertionSortRunningTime_worst_case
    (costs : InsertionSortLineCosts) (n : Nat) :
    insertionSortRunningTime costs n insertionSortWorstTrace =
      costs.c₁ * n +
        costs.c₂ * (n - 1) +
        costs.c₄ * (n - 1) +
        costs.c₅ * (triangular (n - 1) + (n - 1)) +
        costs.c₆ * triangular (n - 1) +
        costs.c₇ * triangular (n - 1) +
        costs.c₈ * (n - 1) := by
  rw [insertionSortRunningTime, insertionSortLineCounts_worst_case]
  rfl

end Chapter02
end CLRS
