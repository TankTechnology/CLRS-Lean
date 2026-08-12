import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelStrassen.Recurrences.Definitions

/-!
# Chapter 26 extension — parallel Strassen recurrences: monotonicity

This module proves successor monotonicity and the adjacent-power sandwiches
used to lift the compatibility extension's exact solutions to every input.
-/

namespace CLRS
namespace Chapter27

/-- The parallel Strassen work recurrence does not decrease at a successor step. -/
private theorem strassenWork_le_succ : ∀ n, strassenWork n ≤ strassenWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show strassenWork 0 = 0 by rw [strassenWork]; norm_num]
          exact Nat.zero_le _
        · have hone : strassenWork 1 = 1 := by rw [strassenWork]; norm_num
          rw [hone, strassenWork_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [strassenWork_unfold (n := 2 * m) (by omega),
            strassenWork_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
          have hsquare : (2 * m) * (2 * m) ≤ (2 * m + 1) * (2 * m + 1) := by
            nlinarith
          omega
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [strassenWork_unfold (n := 2 * m + 1) (by omega),
            strassenWork_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          have ihm := ih m (by omega)
          have hsquare : (2 * m + 1) * (2 * m + 1) ≤
              (2 * m + 1 + 1) * (2 * m + 1 + 1) := by
            nlinarith
          omega

/-- Parallel Strassen work is monotone in the input size. -/
theorem strassenWork_monotone : Monotone strassenWork :=
  monotone_nat_of_le_succ strassenWork_le_succ

/-- Every positive parallel-Strassen work cost lies between its adjacent
power-of-two costs. -/
theorem strassenWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    strassenWork (2 ^ Nat.log 2 n) ≤ strassenWork n ∧
      strassenWork n ≤ strassenWork (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich strassenWork_monotone 2 n (by norm_num) hn.ne'

/-- The parallel Strassen span recurrence does not decrease at a successor step. -/
private theorem strassenSpan_le_succ : ∀ n, strassenSpan n ≤ strassenSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show strassenSpan 0 = 0 by rw [strassenSpan]; norm_num]
          exact Nat.zero_le _
        · have hone : strassenSpan 1 = 1 := by rw [strassenSpan]; norm_num
          rw [hone, strassenSpan_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          rw [strassenSpan_unfold (n := 2 * m) (by omega),
            strassenSpan_unfold (n := 2 * m + 1) (by omega), hdiv0, hdiv1]
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [strassenSpan_unfold (n := 2 * m + 1) (by omega),
            strassenSpan_unfold (n := 2 * m + 1 + 1) (by omega), hdiv0, hdiv1]
          exact Nat.add_le_add_right (ih m (by omega)) 1

/-- Parallel Strassen span is monotone in the input size. -/
theorem strassenSpan_monotone : Monotone strassenSpan :=
  monotone_nat_of_le_succ strassenSpan_le_succ

/-- Every positive parallel-Strassen span cost lies between its adjacent
power-of-two costs. -/
theorem strassenSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    strassenSpan (2 ^ Nat.log 2 n) ≤ strassenSpan n ∧
      strassenSpan n ≤ strassenSpan (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich strassenSpan_monotone 2 n (by norm_num) hn.ne'

end Chapter27
end CLRS
