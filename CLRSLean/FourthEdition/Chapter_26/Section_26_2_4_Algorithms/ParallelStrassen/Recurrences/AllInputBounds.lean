import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelStrassen.Recurrences.Monotonicity

/-!
# Chapter 26 extension — parallel Strassen recurrences: all-input bounds

This module lifts the compatibility extension's exact power-of-two work and
span solutions to all positive input sizes.
-/

namespace CLRS
namespace Chapter27

private theorem strassenWork_exactPower_bounds (k : ℕ) :
    7 ^ k ≤ strassenWork (2 ^ k) ∧ strassenWork (2 ^ k) ≤ 3 * 7 ^ k := by
  have hexact := strassenWork_pow_two k
  rw [pow_succ (4 : ℕ) k, pow_succ (7 : ℕ) k] at hexact
  have hpow : 4 ^ k ≤ 7 ^ k := Nat.pow_le_pow_left (by norm_num) k
  constructor <;> omega

private theorem strassenWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (strassenWork (2 ^ k) : ℝ))
      (fun k : ℕ => (7 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨3, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    have hreal :
        (strassenWork (2 ^ k) : ℝ) ≤ ((3 * 7 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (strassenWork_exactPower_bounds k).2
    simpa [Nat.cast_mul, Nat.cast_pow] using hreal
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity : 0 ≤ (7 : ℝ) ^ k),
      abs_of_nonneg (Nat.cast_nonneg _)]
    have hreal : ((7 ^ k : ℕ) : ℝ) ≤ (strassenWork (2 ^ k) : ℝ) := by
      exact_mod_cast (strassenWork_exactPower_bounds k).1
    simpa [Nat.cast_pow] using hreal

private theorem strassenSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : ℕ => (strassenSpan (2 ^ k) : ℝ))
      (fun k : ℕ => (k : ℝ) + 1) := by
  have hfun :
      (fun k : ℕ => (strassenSpan (2 ^ k) : ℝ)) =
        (fun k : ℕ => (k : ℝ) + 1) := by
    funext k
    rw [strassenSpan_pow_two]
    push_cast
    norm_num
  rw [hfun]
  exact Chapter03.isBigTheta_refl _

/-- Parallel Strassen has work `n^(log₂ 7)` on every positive input size. -/
theorem strassenWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (strassenWork n : ℝ))
      (Chapter04.realLogScale 7 2) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (strassenWork n : ℝ))
        (Chapter04.criticalPowerScale 7 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerScale 7 2
      (fun n : ℕ => (strassenWork n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast strassenWork_monotone)
      strassenWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical
    (Chapter04.criticalPowerScale_isBigTheta_realLogScale 7 2
      (by norm_num) (by norm_num))

/-- Parallel Strassen has logarithmic span on every positive input size. -/
theorem strassenSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (strassenSpan n : ℝ))
      (Chapter04.polynomialLogScale 2 0) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (strassenSpan n : ℝ))
        (Chapter04.criticalPowerLogScale 1 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerLogScale 1 2
      (fun n : ℕ => (strassenSpan n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast strassenSpan_monotone) (by
        simpa only [Nat.cast_one, one_pow, mul_one] using
          strassenSpan_exactPower_bigTheta)
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale 2 0
      (by norm_num))

end Chapter27
end CLRS
