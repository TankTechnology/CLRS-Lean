import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.RecurrenceLinks
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S3_AllInputBounds

/-!
# CLRS Chapter 27.3 — Executable P-MERGE-SORT Work Bounds

The lower theorem transfers the adjacent-power lower bound through the exact
recurrence link.  The upper theorem counts at most one linear-work merge level
per ceiling-logarithmic recursion level.

Main results:

* {lit}`pMergeSort_work_lower`: pointwise logarithmic-linear work lower bound.
* {lit}`pMergeSort_work_upper`: pointwise logarithmic-linear work upper bound.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMergeSort
namespace Costs
namespace Work

/-- The abstract work recurrence has at most one total-size charge at each
ceiling-logarithmic level. -/
private theorem recurrence_le_clog : ∀ n : ℕ,
    pMergeSortWork n ≤ n * (Nat.clog 2 n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnsmall : n ≤ 1
      · interval_cases n <;> simp [pMergeSortWork]
      · have hn : 2 ≤ n := by omega
        have hfloor_lt : n / 2 < n := by omega
        have hceil_lt : n - n / 2 < n := by omega
        have hfloor := ih (n / 2) hfloor_lt
        have hceil := ih (n - n / 2) hceil_lt
        have hfloor_le_ceil : n / 2 ≤ n - n / 2 := by omega
        have hhalf : (n + 2 - 1) / 2 = n - n / 2 := by omega
        have hclogFloor : Nat.clog 2 (n / 2) + 1 ≤ Nat.clog 2 n := by
          rw [Nat.clog_of_two_le (by norm_num) hn, hhalf]
          exact Nat.add_le_add_right
            (Nat.clog_mono_right 2 hfloor_le_ceil) 1
        have hclogCeil : Nat.clog 2 (n - n / 2) + 1 ≤ Nat.clog 2 n := by
          rw [Nat.clog_of_two_le (by norm_num) hn, hhalf]
        have hfloor' : pMergeSortWork (n / 2) ≤
            (n / 2) * Nat.clog 2 n :=
          hfloor.trans (Nat.mul_le_mul_left _ hclogFloor)
        have hceil' : pMergeSortWork (n - n / 2) ≤
            (n - n / 2) * Nat.clog 2 n :=
          hceil.trans (Nat.mul_le_mul_left _ hclogCeil)
        have hsplit : n / 2 + (n - n / 2) = n := by omega
        rw [pMergeSortWork_unfold hn]
        calc
          pMergeSortWork (n / 2) + pMergeSortWork (n - n / 2) + n ≤
              (n / 2) * Nat.clog 2 n +
                (n - n / 2) * Nat.clog 2 n + n := by omega
          _ = (n / 2 + (n - n / 2)) * Nat.clog 2 n + n := by
            rw [Nat.add_mul]
          _ = n * Nat.clog 2 n + n := by rw [hsplit]
          _ = n * (Nat.clog 2 n + 1) := by rw [Nat.mul_succ]

/-- The exact-power lower solution and monotonicity give a simple floor-log
lower bound for the abstract recurrence. -/
private theorem floorLog_lower (n : ℕ) :
    n * (Nat.log 2 n + 1) ≤ 2 * pMergeSortWork n := by
  by_cases hnzero : n = 0
  · subst n
    simp [pMergeSortWork]
  · let k := Nat.log 2 n
    let q := 2 ^ k
    have hq_le : q ≤ n := by
      exact Nat.pow_log_le_self 2 hnzero
    have hn_lt : n < 2 ^ (k + 1) := by
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    have hn_le : n ≤ 2 * q := by
      apply Nat.le_of_lt
      simpa [q, k, pow_succ, Nat.mul_comm] using hn_lt
    have hmodel : pMergeSortWork q ≤ pMergeSortWork n :=
      pMergeSortWork_monotone hq_le
    calc
      n * (Nat.log 2 n + 1) = n * (k + 1) := by rfl
      _ ≤ (2 * q) * (k + 1) := Nat.mul_le_mul_right (k + 1) hn_le
      _ = 2 * (q * (k + 1)) := by ring
      _ = 2 * pMergeSortWork q := by rw [pMergeSortWork_pow_two]
      _ ≤ 2 * pMergeSortWork n := Nat.mul_le_mul_left 2 hmodel

end Work
end Costs
end ParallelMergeSort

/-! ## Public theorems -/

/-- Every P-MERGE-SORT execution has logarithmic-linear work from below, with an explicit
constant valid at all input sizes. -/
theorem pMergeSort_work_lower [LinearOrder α] (xs : List α) :
    xs.length * (Nat.log 2 xs.length + 1) ≤
      16 * ((pMergeSort xs).work + xs.length + 1) := by
  have hmodel := ParallelMergeSort.Costs.Work.floorLog_lower xs.length
  have hlink := ParallelMergeSort.Costs.recurrenceWork_le_execution
    xs.length xs rfl
  omega

/-- Every P-MERGE-SORT execution has logarithmic-linear work from above, with an explicit
all-input bound. -/
theorem pMergeSort_work_upper [LinearOrder α] (xs : List α) :
    (pMergeSort xs).work ≤
      128 * (xs.length + 1) * (Nat.log 2 xs.length + 1) := by
  have hlink := ParallelMergeSort.Costs.executionWork_le_recurrence
    xs.length xs rfl
  have hmodel := ParallelMergeSort.Costs.Work.recurrence_le_clog xs.length
  have hclog : Nat.clog 2 xs.length ≤ Nat.log 2 xs.length + 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact (Nat.lt_pow_succ_log_self (by norm_num) xs.length).le
  have hmodel' : pMergeSortWork xs.length ≤
      xs.length * (Nat.log 2 xs.length + 2) := by
    exact hmodel.trans (Nat.mul_le_mul_left xs.length (by omega))
  calc
    (pMergeSort xs).work ≤ 64 * pMergeSortWork xs.length := hlink
    _ ≤ 64 * (xs.length * (Nat.log 2 xs.length + 2)) :=
      Nat.mul_le_mul_left 64 hmodel'
    _ ≤ 128 * (xs.length + 1) * (Nat.log 2 xs.length + 1) := by
      nlinarith

end Chapter27
end CLRS
