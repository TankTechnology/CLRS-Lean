import Mathlib.Tactic
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S2_Recurrences

/-!
# 27.2–27.3. All-Input Bounds

This module lifts the Chapter 27 main-text exact power-of-two recurrence
solutions to arbitrary positive inputs.
-/

namespace CLRS
namespace Chapter27

/-- All-input upper bound: `T₁(n) + n² ≤ 2n³`. -/
theorem pMatMulWork_le (n : ℕ) : pMatMulWork n + n * n ≤ 2 * n * n * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> native_decide
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv : 2 * m / 2 = m := by omega
          rw [pMatMulWork_unfold (by omega), hdiv]
          have ihm := ih m (by omega)
          nlinarith [ihm]
        · have hdiv : (2 * m + 1) / 2 = m := by omega
          rw [pMatMulWork_unfold (by omega), hdiv]
          have ihm := ih m (by omega)
          nlinarith [ihm]

/-- All-input span bound: `T∞(n) ≤ ⌊log₂ n⌋ + 1`. -/
theorem pMatMulSpan_le (n : ℕ) : pMatMulSpan n ≤ Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n <;> native_decide
      · rw [pMatMulSpan_unfold (by omega)]
        have ihm := ih (n / 2) (by omega)
        have hlog := Nat.log_div_base 2 n
        have hlogpos : 1 ≤ Nat.log 2 n :=
          Nat.le_log_of_pow_le (by norm_num) (by omega)
        omega

/-- The P-MERGE work recurrence does not decrease at a successor step. -/
private theorem pMergeWork_le_succ : ∀ n, pMergeWork n ≤ pMergeWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeWork 0 = 0 by rw [pMergeWork]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeWork 1 = 1 := by rw [pMergeWork]; norm_num
          rw [hone, pMergeWork_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeWork_unfold (n := 2 * m) (by omega),
            pMergeWork_unfold (n := 2 * m + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          have hlog : Nat.log 2 (2 * m) ≤ Nat.log 2 (2 * m + 1) :=
            Nat.log_mono_right (by omega)
          omega
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeWork_unfold (n := 2 * m + 1) (by omega),
            pMergeWork_unfold (n := 2 * m + 1 + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          have hlog : Nat.log 2 (2 * m + 1) ≤ Nat.log 2 (2 * m + 1 + 1) :=
            Nat.log_mono_right (by omega)
          omega

/-- P-MERGE work is monotone in the input size. -/
theorem pMergeWork_monotone : Monotone pMergeWork :=
  monotone_nat_of_le_succ pMergeWork_le_succ

/-- Every positive P-MERGE work cost lies between its adjacent power-of-two costs. -/
theorem pMergeWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeWork (2 ^ Nat.log 2 n) ≤ pMergeWork n ∧
      pMergeWork n ≤ pMergeWork (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pMergeWork_monotone 2 n (by norm_num) hn.ne'

/-- The P-MERGE span recurrence does not decrease at a successor step. -/
private theorem pMergeSpan_le_succ : ∀ n, pMergeSpan n ≤ pMergeSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeSpan 0 = 0 by rw [pMergeSpan]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeSpan 1 = 1 := by rw [pMergeSpan]; norm_num
          rw [hone, pMergeSpan_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeSpan_unfold (n := 2 * m) (by omega),
            pMergeSpan_unfold (n := 2 * m + 1) (by omega),
            hceil0, hceil1]
          have ihm := ih m (by omega)
          have hlog : Nat.log 2 (2 * m) ≤ Nat.log 2 (2 * m + 1) :=
            Nat.log_mono_right (by omega)
          omega
        · have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeSpan_unfold (n := 2 * m + 1) (by omega),
            pMergeSpan_unfold (n := 2 * m + 1 + 1) (by omega),
            hceil0, hceil1]
          have hlog : Nat.log 2 (2 * m + 1) ≤ Nat.log 2 (2 * m + 1 + 1) :=
            Nat.log_mono_right (by omega)
          omega

/-- P-MERGE span is monotone in the input size. -/
theorem pMergeSpan_monotone : Monotone pMergeSpan :=
  monotone_nat_of_le_succ pMergeSpan_le_succ

/-- Every positive P-MERGE span cost lies between its adjacent power-of-two costs. -/
theorem pMergeSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeSpan (2 ^ Nat.log 2 n) ≤ pMergeSpan n ∧
      pMergeSpan n ≤ pMergeSpan (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pMergeSpan_monotone 2 n (by norm_num) hn.ne'

/-- The P-MERGE-SORT work recurrence does not decrease at a successor step. -/
private theorem pMergeSortWork_le_succ : ∀ n, pMergeSortWork n ≤ pMergeSortWork (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeSortWork 0 = 0 by rw [pMergeSortWork]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeSortWork 1 = 1 := by rw [pMergeSortWork]; norm_num
          rw [hone, pMergeSortWork_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hdiv0 : 2 * m / 2 = m := by omega
          have hdiv1 : (2 * m + 1) / 2 = m := by omega
          have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeSortWork_unfold (n := 2 * m) (by omega),
            pMergeSortWork_unfold (n := 2 * m + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          omega
        · have hdiv0 : (2 * m + 1) / 2 = m := by omega
          have hdiv1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
          have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeSortWork_unfold (n := 2 * m + 1) (by omega),
            pMergeSortWork_unfold (n := 2 * m + 1 + 1) (by omega),
            hceil0, hceil1, hdiv0, hdiv1]
          have ihm := ih m (by omega)
          omega

/-- P-MERGE-SORT work is monotone in the input size. -/
theorem pMergeSortWork_monotone : Monotone pMergeSortWork :=
  monotone_nat_of_le_succ pMergeSortWork_le_succ

/-- Every positive P-MERGE-SORT work cost lies between its adjacent power-of-two costs. -/
theorem pMergeSortWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeSortWork (2 ^ Nat.log 2 n) ≤ pMergeSortWork n ∧
      pMergeSortWork n ≤ pMergeSortWork (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pMergeSortWork_monotone 2 n (by norm_num) hn.ne'

/-- The P-MERGE-SORT span recurrence does not decrease at a successor step. -/
private theorem pMergeSortSpan_le_succ : ∀ n, pMergeSortSpan n ≤ pMergeSortSpan (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · interval_cases n
        · rw [show pMergeSortSpan 0 = 0 by rw [pMergeSortSpan]; norm_num]
          exact Nat.zero_le _
        · have hone : pMergeSortSpan 1 = 1 := by rw [pMergeSortSpan]; norm_num
          rw [hone, pMergeSortSpan_unfold (n := 2) (by norm_num)]
          norm_num [hone]
      · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 :=
          ⟨n / 2, by omega⟩
        · have hceil0 : 2 * m - 2 * m / 2 = m := by omega
          have hceil1 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          rw [pMergeSortSpan_unfold (n := 2 * m) (by omega),
            pMergeSortSpan_unfold (n := 2 * m + 1) (by omega), hceil0, hceil1]
          have ihm := ih m (by omega)
          have hp : pMergeSpan (2 * m) ≤ pMergeSpan (2 * m + 1) :=
            pMergeSpan_monotone (by omega)
          omega
        · have hceil0 : 2 * m + 1 - (2 * m + 1) / 2 = m + 1 := by omega
          have hceil1 : 2 * m + 1 + 1 - (2 * m + 1 + 1) / 2 = m + 1 := by omega
          rw [pMergeSortSpan_unfold (n := 2 * m + 1) (by omega),
            pMergeSortSpan_unfold (n := 2 * m + 1 + 1) (by omega), hceil0, hceil1]
          have hp : pMergeSpan (2 * m + 1) ≤ pMergeSpan (2 * m + 1 + 1) :=
            pMergeSpan_monotone (by omega)
          omega

/-- P-MERGE-SORT span is monotone in the input size. -/
theorem pMergeSortSpan_monotone : Monotone pMergeSortSpan :=
  monotone_nat_of_le_succ pMergeSortSpan_le_succ

/-- Every positive P-MERGE-SORT span cost lies between its adjacent power-of-two costs. -/
theorem pMergeSortSpan_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeSortSpan (2 ^ Nat.log 2 n) ≤ pMergeSortSpan n ∧
      pMergeSortSpan n ≤ pMergeSortSpan (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich pMergeSortSpan_monotone 2 n (by norm_num) hn.ne'

/-! ## All-input work and span bounds -/

private theorem add_three_le_three_mul_pow_two (k : ℕ) :
    k + 3 ≤ 3 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      nlinarith

private theorem pMergeWork_exactPower_bounds (k : ℕ) :
    2 ^ k ≤ pMergeWork (2 ^ k) ∧ pMergeWork (2 ^ k) ≤ 4 * 2 ^ k := by
  have hexact := pMergeWork_pow_two k
  have hlinear := add_three_le_three_mul_pow_two k
  omega

private theorem pMergeWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeWork (2 ^ k) : ℝ))
      (fun k : ℕ => (2 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨4, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hreal :
        (pMergeWork (2 ^ k) : ℝ) ≤ ((4 * 2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (pMergeWork_exactPower_bounds k).2
    simpa [Nat.cast_mul, Nat.cast_pow] using hreal
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hreal : ((2 ^ k : ℕ) : ℝ) ≤ (pMergeWork (2 ^ k) : ℝ) := by
      exact_mod_cast (pMergeWork_exactPower_bounds k).1
    simpa [Nat.cast_pow] using hreal

private theorem pMergeSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeSpan (2 ^ k) : ℝ))
      (fun k : ℕ => ((k : ℝ) + 1) ^ 2) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hexact :
        (2 : ℝ) * (pMergeSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      exact_mod_cast pMergeSpan_pow_two k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hproduct : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) :=
      mul_nonneg hk (by positivity)
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr
      ⟨(2 : ℝ)⁻¹, by positivity, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ) + 1) ^ 2),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hexact :
        (2 : ℝ) * (pMergeSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      exact_mod_cast pMergeSpan_pow_two k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith

private theorem pMergeSortWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeSortWork (2 ^ k) : ℝ))
      (fun k : ℕ => ((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
  have hfun :
      (fun k : ℕ => (pMergeSortWork (2 ^ k) : ℝ)) =
        (fun k : ℕ => ((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
    funext k
    rw [pMergeSortWork_pow_two]
    push_cast
    ring
  rw [hfun]
  exact Chapter03.isBigTheta_refl _

private theorem pMergeSortSpan_exactPower_closed (k : ℕ) :
    6 * pMergeSortSpan (2 ^ k) = (k + 1) * (k + 2) * (k + 3) := by
  rw [pMergeSortSpan_pow_two]
  ring

private theorem pMergeSortSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (pMergeSortSpan (2 ^ k) : ℝ))
      (fun k : ℕ => ((k : ℝ) + 1) ^ 3) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hexact :
        (6 : ℝ) * (pMergeSortSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
      exact_mod_cast pMergeSortSpan_exactPower_closed k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk2 : 0 ≤ (k : ℝ) * (k : ℝ) := mul_nonneg hk hk
    have hk3 : 0 ≤ (k : ℝ) * ((k : ℝ) * (k : ℝ)) := mul_nonneg hk hk2
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr
      ⟨(6 : ℝ)⁻¹, by positivity, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ) + 1) ^ 3),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hexact :
        (6 : ℝ) * (pMergeSortSpan (2 ^ k) : ℝ) =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
      exact_mod_cast pMergeSortSpan_exactPower_closed k
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk2 : 0 ≤ (k : ℝ) * (k : ℝ) := mul_nonneg hk hk
    nlinarith

/-- P-MERGE has linear work on every positive input size. -/
theorem pMergeWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeWork n : ℝ))
      (Chapter04.polynomialScale 1) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (pMergeWork n : ℝ))
        (Chapter04.criticalPowerScale 2 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerScale 2 2
      (fun n : ℕ => (pMergeWork n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast pMergeWork_monotone)
      pMergeWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerScale_isBigTheta_polynomialScale 2 1
      (by norm_num))

/-- P-MERGE has quadratic-logarithmic span on every positive input size. -/
theorem pMergeSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeSpan n : ℝ))
      (Chapter04.criticalPowerLogPolylogScale 1 2 1) := by
  have hpower :
      Chapter03.isBigTheta
        (fun i : ℕ => (pMergeSpan (2 ^ i) : ℝ))
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 1 (2 ^ i)) := by
    have hscale :
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 1 (2 ^ i)) =
          (fun i : ℕ => ((i : ℝ) + 1) ^ 2) := by
      funext i
      simp [Chapter04.criticalPowerLogPolylogScale_exactPower]
    rw [hscale]
    exact pMergeSpan_exactPower_bigTheta
  exact Chapter04.allInput_bigTheta_of_powerStep 2
    (fun n : ℕ => (pMergeSpan n : ℝ))
    (Chapter04.criticalPowerLogPolylogScale 1 2 1) (by norm_num)
    (Chapter04.monotoneAbs_natCast pMergeSpan_monotone)
    (Chapter04.criticalPowerLogPolylogScale_monotoneAbs 1 2 1 (by norm_num))
    (Chapter04.criticalPowerLogPolylogScale_powerStepBound 1 2 1
      (by norm_num) (by norm_num))
    hpower

/-- P-MERGE-SORT has `n log n` work on every positive input size. -/
theorem pMergeSortWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeSortWork n : ℝ))
      (Chapter04.polynomialLogScale 2 1) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (pMergeSortWork n : ℝ))
        (Chapter04.criticalPowerLogScale 2 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerLogScale 2 2
      (fun n : ℕ => (pMergeSortWork n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast pMergeSortWork_monotone)
      pMergeSortWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale 2 1
      (by norm_num))

/-- P-MERGE-SORT has cubic-logarithmic span on every positive input size. -/
theorem pMergeSortSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMergeSortSpan n : ℝ))
      (Chapter04.criticalPowerLogPolylogScale 1 2 2) := by
  have hpower :
      Chapter03.isBigTheta
        (fun i : ℕ => (pMergeSortSpan (2 ^ i) : ℝ))
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 2 (2 ^ i)) := by
    have hscale :
        (fun i : ℕ => Chapter04.criticalPowerLogPolylogScale 1 2 2 (2 ^ i)) =
          (fun i : ℕ => ((i : ℝ) + 1) ^ 3) := by
      funext i
      simp [Chapter04.criticalPowerLogPolylogScale_exactPower]
    rw [hscale]
    exact pMergeSortSpan_exactPower_bigTheta
  exact Chapter04.allInput_bigTheta_of_powerStep 2
    (fun n : ℕ => (pMergeSortSpan n : ℝ))
    (Chapter04.criticalPowerLogPolylogScale 1 2 2) (by norm_num)
    (Chapter04.monotoneAbs_natCast pMergeSortSpan_monotone)
    (Chapter04.criticalPowerLogPolylogScale_monotoneAbs 1 2 2 (by norm_num))
    (Chapter04.criticalPowerLogPolylogScale_powerStepBound 1 2 2
      (by norm_num) (by norm_num))
    hpower

end Chapter27
end CLRS
