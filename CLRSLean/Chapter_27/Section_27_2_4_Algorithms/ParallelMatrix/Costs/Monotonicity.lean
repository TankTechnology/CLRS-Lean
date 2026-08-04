import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs.Definitions

/-!
# CLRS Section 27.2 — Monotonicity of Matrix Execution Costs

The executable matrix recurrences use floor halving on arbitrary natural
inputs.  This module proves that all four costs are monotone and packages the
adjacent-power sandwiches used by the all-input asymptotic analysis.

Main results:

- Theorems {lit}`pAddWork_monotone` and {lit}`pAddSpan_monotone`.
- Theorems {lit}`pMatMulExecWork_monotone` and
  {lit}`pMatMulExecSpan_monotone`.
- The four corresponding {lit}`*_power_sandwich` theorems.
-/

namespace CLRS
namespace Chapter27

/-! ## Small base values -/

@[simp] private theorem pAddWork_zero : pAddWork 0 = 1 := by
  rw [pAddWork]
  norm_num

@[simp] private theorem pAddWork_one : pAddWork 1 = 1 := by
  rw [pAddWork]
  norm_num

@[simp] private theorem pAddWork_two : pAddWork 2 = 7 := by
  rw [pAddWork_unfold (n := 2) (by norm_num)]
  norm_num

@[simp] private theorem pAddSpan_zero : pAddSpan 0 = 1 := by
  rw [pAddSpan]
  norm_num

@[simp] private theorem pAddSpan_one : pAddSpan 1 = 1 := by
  rw [pAddSpan]
  norm_num

@[simp] private theorem pAddSpan_two : pAddSpan 2 = 3 := by
  rw [pAddSpan_unfold (n := 2) (by norm_num)]
  norm_num

@[simp] private theorem pMatMulExecWork_zero : pMatMulExecWork 0 = 1 := by
  rw [pMatMulExecWork]
  norm_num

@[simp] private theorem pMatMulExecWork_one : pMatMulExecWork 1 = 1 := by
  rw [pMatMulExecWork]
  norm_num

@[simp] private theorem pMatMulExecWork_two : pMatMulExecWork 2 = 22 := by
  rw [pMatMulExecWork_unfold (n := 2) (by norm_num)]
  norm_num

@[simp] private theorem pMatMulExecSpan_zero : pMatMulExecSpan 0 = 1 := by
  rw [pMatMulExecSpan]
  norm_num

@[simp] private theorem pMatMulExecSpan_one : pMatMulExecSpan 1 = 1 := by
  rw [pMatMulExecSpan]
  norm_num

@[simp] private theorem pMatMulExecSpan_two : pMatMulExecSpan 2 = 7 := by
  rw [pMatMulExecSpan_unfold (n := 2) (by norm_num)]
  norm_num

/-! ## P-ADD -/

/-- P-ADD work does not decrease at a successor input. -/
private theorem pAddWork_le_succ : ∀ n, pAddWork n ≤ pAddWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> simp
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [pAddWork_unfold (n := 2 * m) (by omega),
            pAddWork_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pAddWork_unfold (n := 2 * m + 1) (by omega),
            pAddWork_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 (ih m (by omega))) 3

/-- Exact P-ADD work is monotone in the input size. -/
theorem pAddWork_monotone : Monotone pAddWork :=
  monotone_nat_of_le_succ pAddWork_le_succ

/-- Every positive P-ADD work cost lies between its adjacent power-of-two
costs. -/
theorem pAddWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    pAddWork (2 ^ Nat.log 2 n) ≤ pAddWork n ∧
      pAddWork n ≤ pAddWork (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pAddWork_monotone 2 n (by norm_num) hn.ne'

/-- P-ADD span does not decrease at a successor input. -/
private theorem pAddSpan_le_succ : ∀ n, pAddSpan n ≤ pAddSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> simp
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [pAddSpan_unfold (n := 2 * m) (by omega),
            pAddSpan_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pAddSpan_unfold (n := 2 * m + 1) (by omega),
            pAddSpan_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          exact Nat.add_le_add_right (ih m (by omega)) 2

/-- Exact P-ADD span is monotone in the input size. -/
theorem pAddSpan_monotone : Monotone pAddSpan :=
  monotone_nat_of_le_succ pAddSpan_le_succ

/-- Every positive P-ADD span cost lies between its adjacent power-of-two
costs. -/
theorem pAddSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    pAddSpan (2 ^ Nat.log 2 n) ≤ pAddSpan n ∧
      pAddSpan n ≤ pAddSpan (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pAddSpan_monotone 2 n (by norm_num) hn.ne'

/-! ## P-MATMUL -/

/-- Executable P-MATMUL work does not decrease at a successor input. -/
private theorem pMatMulExecWork_le_succ :
    ∀ n, pMatMulExecWork n ≤ pMatMulExecWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> simp
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [pMatMulExecWork_unfold (n := 2 * m) (by omega),
            pMatMulExecWork_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
          exact Nat.add_le_add_left (pAddWork_monotone (by omega)) _
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMatMulExecWork_unfold (n := 2 * m + 1) (by omega),
            pMatMulExecWork_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          have hrec := ih m (by omega)
          have hadd := pAddWork_monotone (show 2 * m + 1 ≤ 2 * m + 1 + 1 by omega)
          omega

/-- Exact executable P-MATMUL work is monotone in the input size. -/
theorem pMatMulExecWork_monotone : Monotone pMatMulExecWork :=
  monotone_nat_of_le_succ pMatMulExecWork_le_succ

/-- Every positive executable P-MATMUL work cost lies between its adjacent
power-of-two costs. -/
theorem pMatMulExecWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMatMulExecWork (2 ^ Nat.log 2 n) ≤ pMatMulExecWork n ∧
      pMatMulExecWork n ≤ pMatMulExecWork (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pMatMulExecWork_monotone 2 n
    (by norm_num) hn.ne'

/-- Executable P-MATMUL span does not decrease at a successor input. -/
private theorem pMatMulExecSpan_le_succ :
    ∀ n, pMatMulExecSpan n ≤ pMatMulExecSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> simp
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [pMatMulExecSpan_unfold (n := 2 * m) (by omega),
            pMatMulExecSpan_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
          exact Nat.add_le_add_left (pAddSpan_monotone (by omega)) _
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMatMulExecSpan_unfold (n := 2 * m + 1) (by omega),
            pMatMulExecSpan_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          have hrec := ih m (by omega)
          have hadd := pAddSpan_monotone (show 2 * m + 1 ≤ 2 * m + 1 + 1 by omega)
          omega

/-- Exact executable P-MATMUL span is monotone in the input size. -/
theorem pMatMulExecSpan_monotone : Monotone pMatMulExecSpan :=
  monotone_nat_of_le_succ pMatMulExecSpan_le_succ

/-- Every positive executable P-MATMUL span cost lies between its adjacent
power-of-two costs. -/
theorem pMatMulExecSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMatMulExecSpan (2 ^ Nat.log 2 n) ≤ pMatMulExecSpan n ∧
      pMatMulExecSpan n ≤ pMatMulExecSpan (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pMatMulExecSpan_monotone 2 n
    (by norm_num) hn.ne'

end Chapter27
end CLRS
