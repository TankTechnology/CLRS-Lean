import CLRSLean.Chapter_04.Section_04_5_Master_Theorem

/-!
# CLRS Section 4.6 - All-input Master-theorem bridge

Section 4.5 proves the exact-power Master-theorem core for values
{lit}`T(b^i)`.  The full CLRS theorem needs a second bridge from exact powers
to arbitrary natural input sizes, including floor and ceiling recurrences.

This file proves the reusable transfer layer for that bridge.  It deliberately
keeps the power-sandwich facts as explicit hypotheses: later files can discharge
those hypotheses for concrete scales such as polynomial and logarithmic
functions, or for specific floor/ceiling recurrence models.
-/

namespace CLRS
namespace Chapter04

/-! ## Monotone and sandwich interfaces -/

/-- Absolute-value monotonicity for a cost function. -/
def MonotoneAbs (T : ℕ → ℝ) : Prop :=
  ∀ {m n : ℕ}, m ≤ n → |T m| ≤ |T n|

/--
Eventually every large input can be bounded above by a large enough exact
power, with the comparison scale at that power controlled by the scale at the
original input.
-/
def EventuallyPowerUpperSandwich (b : ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧
    ∀ i₀ : ℕ, ∃ n₀ : ℕ, ∀ n, n ≥ n₀ →
      ∃ i : ℕ, i ≥ i₀ ∧ n ≤ b ^ i ∧ |g (b ^ i)| ≤ A * |g n|

/--
Eventually every large input has a large enough exact power below it, with the
comparison scale at the original input controlled by the scale at that power.
-/
def EventuallyPowerLowerSandwich (b : ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧
    ∀ i₀ : ℕ, ∃ n₀ : ℕ, ∀ n, n ≥ n₀ →
      ∃ i : ℕ, i ≥ i₀ ∧ b ^ i ≤ n ∧ |g n| ≤ A * |g (b ^ i)|

/-! ## Exact powers to all inputs -/

/--
Transfer an exact-power big-O bound to all natural inputs, provided the cost is
monotone in absolute value and the comparison function admits an eventual upper
power sandwich.
-/
theorem allInput_bigO_of_power_upper_sandwich
    (b : ℕ) (T g : ℕ → ℝ)
    (hT_mono : MonotoneAbs T)
    (hg_sandwich : EventuallyPowerUpperSandwich b g)
    (h_power :
      Chapter03.isBigO
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigO T g := by
  rcases (Chapter03.isBigO_iff
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ => g (b ^ i))).mp h_power with
    ⟨C, hC_pos, i₀, hC⟩
  rcases hg_sandwich with ⟨A, hA_pos, hA⟩
  rcases hA i₀ with ⟨n₀, hn₀⟩
  refine (Chapter03.isBigO_iff T g).mpr ?_
  refine ⟨C * A, mul_pos hC_pos hA_pos, n₀, ?_⟩
  intro n hn
  rcases hn₀ n hn with ⟨i, hi_ge, hn_le_pow, hg⟩
  calc
    |T n| ≤ |T (b ^ i)| := hT_mono hn_le_pow
    _ ≤ C * |g (b ^ i)| := hC i hi_ge
    _ ≤ C * (A * |g n|) := by
      gcongr
    _ = (C * A) * |g n| := by ring

/--
Transfer an exact-power big-Omega bound to all natural inputs, provided the
cost is monotone in absolute value and the comparison function admits an
eventual lower power sandwich.
-/
theorem allInput_bigOmega_of_power_lower_sandwich
    (b : ℕ) (T g : ℕ → ℝ)
    (hT_mono : MonotoneAbs T)
    (hg_sandwich : EventuallyPowerLowerSandwich b g)
    (h_power :
      Chapter03.isBigOmega
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigOmega T g := by
  rcases (Chapter03.isBigOmega_iff
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ => g (b ^ i))).mp h_power with
    ⟨c, hc_pos, i₀, hc⟩
  rcases hg_sandwich with ⟨A, hA_pos, hA⟩
  rcases hA i₀ with ⟨n₀, hn₀⟩
  refine (Chapter03.isBigOmega_iff T g).mpr ?_
  refine ⟨c / A, div_pos hc_pos hA_pos, n₀, ?_⟩
  intro n hn
  rcases hn₀ n hn with ⟨i, hi_ge, hpow_le_n, hg⟩
  have hA_ne_zero : A ≠ 0 := ne_of_gt hA_pos
  have hdiv_nonneg : 0 ≤ c / A := (div_pos hc_pos hA_pos).le
  calc
    (c / A) * |g n| ≤ (c / A) * (A * |g (b ^ i)|) := by
      gcongr
    _ = c * |g (b ^ i)| := by
      field_simp [hA_ne_zero]
    _ ≤ |T (b ^ i)| := hc i hi_ge
    _ ≤ |T n| := hT_mono hpow_le_n

/--
Transfer an exact-power big-Theta bound to all natural inputs using both power
sandwich directions.
-/
theorem allInput_bigTheta_of_power_sandwich
    (b : ℕ) (T g : ℕ → ℝ)
    (hT_mono : MonotoneAbs T)
    (hg_upper : EventuallyPowerUpperSandwich b g)
    (hg_lower : EventuallyPowerLowerSandwich b g)
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigTheta T g := by
  exact
    ⟨allInput_bigO_of_power_upper_sandwich b T g hT_mono hg_upper h_power.1,
      allInput_bigOmega_of_power_lower_sandwich b T g hT_mono hg_lower h_power.2⟩

end Chapter04
end CLRS
