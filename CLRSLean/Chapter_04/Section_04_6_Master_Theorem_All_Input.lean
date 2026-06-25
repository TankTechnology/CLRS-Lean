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

/-! ## Floor/ceiling recurrence interfaces -/

/--
All-input floor-division form of the Master-theorem recurrence:
`T(n) = a T(⌊n / b⌋) + f(n)`.
-/
structure FloorDivideRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ n : ℕ, T n = (a : ℝ) * T (n / b) + f n

/--
All-input ceiling-division form of the Master-theorem recurrence:
`T(n) = a T(⌈n / b⌉) + f(n)`, represented over natural numbers as
{lit}`(n + b - 1) / b`.
-/
structure CeilDivideRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ n : ℕ, T n = (a : ℝ) * T ((n + (b - 1)) / b) + f n

theorem pow_succ_div_base {b i : ℕ} (hb : 0 < b) :
    b ^ (i + 1) / b = b ^ i := by
  rw [show b ^ (i + 1) = b * b ^ i by
    rw [pow_succ, Nat.mul_comm]]
  exact Nat.mul_div_right (b ^ i) hb

theorem pow_succ_add_pred_div_base {b i : ℕ} (hb : 0 < b) :
    (b ^ (i + 1) + (b - 1)) / b = b ^ i := by
  apply Nat.div_eq_of_lt_le
  · rw [show b ^ i * b = b ^ (i + 1) by rw [pow_succ]]
    exact Nat.le_add_right _ _
  · rw [Nat.add_mul, one_mul]
    rw [show b ^ i * b = b ^ (i + 1) by rw [pow_succ]]
    omega

theorem exactPowerRecurrence_of_floorDivideRecurrence
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence a b f T) (hb : 0 < b) :
    ExactPowerRecurrence a b f T := by
  refine ⟨?_⟩
  intro i
  rw [h_rec.step (b ^ (i + 1))]
  rw [pow_succ_div_base (b := b) (i := i) hb]

theorem exactPowerRecurrence_of_ceilDivideRecurrence
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence a b f T) (hb : 0 < b) :
    ExactPowerRecurrence a b f T := by
  refine ⟨?_⟩
  intro i
  rw [h_rec.step (b ^ (i + 1))]
  rw [pow_succ_add_pred_div_base (b := b) (i := i) hb]

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
