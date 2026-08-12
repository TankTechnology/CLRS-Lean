import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMergeSort.Costs.Step
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.Costs.Span.Bounds
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S3_AllInputBounds

/-!
# CLRS Chapter 26.3 — Executable P-MERGE-SORT Span Upper Bound

The actual critical path is compared to the textbook P-MERGE-SORT span
recurrence.  The comparison uses the proved pointwise quadratic-logarithmic
P-MERGE span bound, then the recurrence's exact power-of-two solution yields
the cubic-logarithmic all-input result.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMergeSort
namespace Costs
namespace Span

/-- The P-MERGE span recurrence dominates a quadratic floor-log expression. -/
private theorem mergeRecurrence_floorLog_lower (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 n + 1) * (Nat.log 2 n + 2) ≤ 2 * pMergeSpan n := by
  let k := Nat.log 2 n
  let q := 2 ^ k
  have hq_le : q ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hmodel : pMergeSpan q ≤ pMergeSpan n :=
    pMergeSpan_monotone hq_le
  calc
    (Nat.log 2 n + 1) * (Nat.log 2 n + 2) =
        (k + 1) * (k + 2) := by rfl
    _ = 2 * pMergeSpan q := by rw [pMergeSpan_pow_two]
    _ ≤ 2 * pMergeSpan n := Nat.mul_le_mul_left 2 hmodel

/-- The actual P-MERGE-SORT critical path is at most 128 copies of the
textbook span recurrence. -/
private theorem execution_le_recurrence [LinearOrder α] (n : ℕ) :
    ∀ (xs : List α), xs.length = n →
      (pMergeSort xs).span ≤ 128 * pMergeSortSpan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs hlength
      by_cases hsmall : xs.length ≤ 1
      · have hn : n ≤ 1 := by omega
        rw [pMergeSort]
        simp only [hsmall]
        rw [pMergeSortSpan]
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
        have hfloor_le_ceil : n / 2 ≤ n - n / 2 := by omega
        have hmodelMono : pMergeSortSpan (n / 2) ≤
            pMergeSortSpan (n - n / 2) :=
          pMergeSortSpan_monotone hfloor_le_ceil
        have hchildren : max (pMergeSort left).span (pMergeSort right).span ≤
            128 * pMergeSortSpan (n - n / 2) := by
          apply max_le
          · exact hleft.trans (Nat.mul_le_mul_left 128 hmodelMono)
          · exact hright
        have hleftValue := pMergeSort_value_length left
        have hrightValue := pMergeSort_value_length right
        have htotal :
            (pMergeSort left).value.length + (pMergeSort right).value.length = n := by
          rw [hleftValue, hrightValue, hleftLength, hrightLength]
          omega
        have hmerge := pMerge_span_upper
          (pMergeSort left).value (pMergeSort right).value
        rw [htotal] at hmerge
        have hmergeModel := mergeRecurrence_floorLog_lower n (by omega)
        have hmergeFork :
            (pMerge (pMergeSort left).value (pMergeSort right).value).span + 1 ≤
              128 * pMergeSpan n := by
          nlinarith
        have hstep := pMergeSort_span_step_eq xs hsmall
        change (pMergeSort xs).span =
          max (pMergeSort left).span (pMergeSort right).span + 1 +
            (pMerge (pMergeSort left).value (pMergeSort right).value).span at hstep
        rw [pMergeSortSpan_unfold hn]
        omega

/-- The textbook span recurrence is bounded by twice a floor-log cube. -/
private theorem recurrence_le_cube (n : ℕ) :
    pMergeSortSpan n ≤ 2 * (Nat.log 2 n + 1) ^ 3 := by
  by_cases hnsmall : n ≤ 1
  · interval_cases n <;> simp [pMergeSortSpan]
  · have hn : 2 ≤ n := by omega
    let k := Nat.log 2 n
    have hk : 1 ≤ k := Nat.log_pos (by norm_num) hn
    have hupper : pMergeSortSpan n ≤ pMergeSortSpan (2 ^ (k + 1)) := by
      simpa [k] using (pMergeSortSpan_power_sandwich n (by omega)).2
    have hclosed : 6 * pMergeSortSpan (2 ^ (k + 1)) =
        (k + 2) * (k + 3) * (k + 4) := by
      rw [pMergeSortSpan_pow_two]
      ring
    change pMergeSortSpan n ≤ 2 * (k + 1) ^ 3
    obtain ⟨t, hk_eq⟩ : ∃ t, k = t + 1 := by
      exact ⟨k - 1, by omega⟩
    rw [hk_eq] at hupper hclosed ⊢
    have hpoly : (t + 3) * (t + 4) * (t + 5) ≤
        12 * (t + 2) ^ 3 := by
      have hnonneg : 0 ≤ 11 * t ^ 3 + 60 * t ^ 2 + 97 * t + 36 :=
        Nat.zero_le _
      nlinarith
    nlinarith

end Span
end Costs
end ParallelMergeSort

/-! ## Public theorem -/

/-- Every executable P-MERGE-SORT run has cubic-logarithmic span. -/
theorem pMergeSort_span_upper [LinearOrder α] (xs : List α) :
    (pMergeSort xs).span ≤
      256 * (Nat.log 2 xs.length + 1) ^ 3 := by
  have hlink := ParallelMergeSort.Costs.Span.execution_le_recurrence
    xs.length xs rfl
  have hmodel := ParallelMergeSort.Costs.Span.recurrence_le_cube xs.length
  nlinarith

end Chapter27
end CLRS
