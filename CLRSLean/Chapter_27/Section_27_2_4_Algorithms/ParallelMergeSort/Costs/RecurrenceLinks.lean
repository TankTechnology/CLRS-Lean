import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Step
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Work.Bounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S2_Recurrences

/-!
# CLRS Chapter 27.3 — P-MERGE-SORT Work Recurrence Links

The executable sorter is sandwiched by constant multiples of the existing
textbook work recurrence.  These lemmas keep the algorithmic cost proof tied
to the recurrence model rather than re-proving a second abstract analysis.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMergeSort
namespace Costs

variable [LinearOrder α]

/-- The textbook work recurrence is a lower bound for actual execution work. -/
theorem recurrenceWork_le_execution (n : ℕ) :
    ∀ (xs : List α), xs.length = n →
      pMergeSortWork n ≤ (pMergeSort xs).work := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs hlength
      by_cases hsmall : xs.length ≤ 1
      · have hn : n ≤ 1 := by omega
        rw [pMergeSort]
        simp only [hsmall]
        rw [pMergeSortWork]
        simp [hn, hlength]
      · let mid := xs.length / 2
        let left := xs.take mid
        let right := xs.drop mid
        have hn : 2 ≤ n := by omega
        have hleftLength : left.length = n / 2 := by
          simp [left, mid, hlength]
          omega
        have hrightLength : right.length = n - n / 2 := by
          simp [right, mid, hlength]
        have hleft_lt : left.length < n := by rw [hleftLength]; omega
        have hright_lt : right.length < n := by rw [hrightLength]; omega
        have hleft := ih left.length hleft_lt left rfl
        have hright := ih right.length hright_lt right rfl
        have hmerge := pMerge_work_lower
          (pMergeSort left).value (pMergeSort right).value
        have hleftValue := pMergeSort_value_length left
        have hrightValue := pMergeSort_value_length right
        have hstep := pMergeSort_work_step_eq xs hsmall
        rw [pMergeSortWork_unfold hn]
        change (pMergeSort xs).work =
          (pMergeSort left).work + (pMergeSort right).work + 1 +
            (pMerge (pMergeSort left).value (pMergeSort right).value).work at hstep
        rw [hleftLength] at hleft
        rw [hrightLength] at hright
        omega

/-- Actual execution work is at most sixty-four copies of the textbook work
recurrence.  P-MERGE's logarithmic potential pays for the fork at each node. -/
theorem executionWork_le_recurrence (n : ℕ) :
    ∀ (xs : List α), xs.length = n →
      (pMergeSort xs).work ≤ 64 * pMergeSortWork n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs hlength
      by_cases hsmall : xs.length ≤ 1
      · have hn : n ≤ 1 := by omega
        rw [pMergeSort]
        simp only [hsmall]
        rw [pMergeSortWork]
        simp [hn, hlength]
        omega
      · let mid := xs.length / 2
        let left := xs.take mid
        let right := xs.drop mid
        have hn : 2 ≤ n := by omega
        have hleftLength : left.length = n / 2 := by
          simp [left, mid, hlength]
          omega
        have hrightLength : right.length = n - n / 2 := by
          simp [right, mid, hlength]
        have hleft_lt : left.length < n := by rw [hleftLength]; omega
        have hright_lt : right.length < n := by rw [hrightLength]; omega
        have hleft := ih left.length hleft_lt left rfl
        have hright := ih right.length hright_lt right rfl
        rw [hleftLength] at hleft
        rw [hrightLength] at hright
        have hleftValue := pMergeSort_value_length left
        have hrightValue := pMergeSort_value_length right
        have htotal :
            (pMergeSort left).value.length + (pMergeSort right).value.length = n := by
          rw [hleftValue, hrightValue, hleftLength, hrightLength]
          omega
        have hpotential :=
          ParallelMerge.Costs.Work.potential_of_total n
            (pMergeSort left).value (pMergeSort right).value htotal
        have hlogpos : 0 < Nat.log 2 (n + 1) :=
          Nat.log_pos (by norm_num) (by omega)
        have hmergeFork :
            (pMerge (pMergeSort left).value (pMergeSort right).value).work + 1 ≤
              64 * n := by
          omega
        have hstep := pMergeSort_work_step_eq xs hsmall
        change (pMergeSort xs).work =
          (pMergeSort left).work + (pMergeSort right).work + 1 +
            (pMerge (pMergeSort left).value (pMergeSort right).value).work at hstep
        rw [pMergeSortWork_unfold hn]
        omega

end Costs
end ParallelMergeSort

end Chapter27
end CLRS
