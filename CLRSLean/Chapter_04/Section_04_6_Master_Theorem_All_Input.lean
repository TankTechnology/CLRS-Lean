import CLRSLean.Chapter_04.Section_04_5_Master_Theorem

/-!
# CLRS Section 4.6 - All-input Master-theorem bridge

Section 4.5 proves the exact-power Master-theorem core for values
{lit}`T(b^i)`.  The full CLRS theorem needs a second bridge from exact powers
to arbitrary natural input sizes, including floor and ceiling recurrences.

This file proves the reusable transfer layer for that bridge.  It first keeps
the power-sandwich facts as explicit hypotheses, then gives a reusable way to
discharge them from a monotonicity hypothesis plus a one-step scale bound
between adjacent powers of the base.
-/

namespace CLRS
namespace Chapter04

/-! ## Monotone and sandwich interfaces -/

/-- Absolute-value monotonicity for a cost function. -/
def MonotoneAbs (T : ℕ → ℝ) : Prop :=
  ∀ {m n : ℕ}, m ≤ n → |T m| ≤ |T n|

/--
Eventual one-step control for a comparison scale across one multiplication by
the Master-theorem base.  This is the local regularity assumption that turns
the adjacent-power interval `b^i ≤ n < b^(i+1)` into the global power-sandwich
hypotheses below.
-/
def EventuallyPowerStepBound (b : ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → |g (b * n)| ≤ A * |g n|

/--
Discrete critical-power scale for the exact-power Master theorem.  On exact
powers it satisfies
{lit}`criticalPowerScale a b (b^i) = a^i`; between exact powers it is the
step function determined by {lit}`Nat.log b n`.

This is deliberately weaker and cleaner than the analytic scale
{lit}`n^(log_b a)`, but it is enough to make the exact-power-to-all-input
bridge concrete.
-/
def criticalPowerScale (a b : ℕ) (n : ℕ) : ℝ :=
  (a : ℝ) ^ Nat.log b n

theorem criticalPowerScale_exactPower
    (a b i : ℕ) (hb : 1 < b) :
    criticalPowerScale a b (b ^ i) = (a : ℝ) ^ i := by
  simp [criticalPowerScale, Nat.log_pow hb]

theorem criticalPowerScale_monotoneAbs
    (a b : ℕ) (ha : 1 ≤ a) :
    MonotoneAbs (criticalPowerScale a b) := by
  intro m n hmn
  have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
  have ha_one : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have hlog : Nat.log b m ≤ Nat.log b n :=
    Nat.log_mono_right hmn
  calc
    |criticalPowerScale a b m| = (a : ℝ) ^ Nat.log b m := by
      rw [criticalPowerScale, abs_of_nonneg (pow_nonneg ha_nonneg _)]
    _ ≤ (a : ℝ) ^ Nat.log b n :=
      pow_le_pow_right₀ ha_one hlog
    _ = |criticalPowerScale a b n| := by
      rw [criticalPowerScale, abs_of_nonneg (pow_nonneg ha_nonneg _)]

theorem criticalPowerScale_powerStepBound
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    EventuallyPowerStepBound b (criticalPowerScale a b) := by
  refine ⟨(a : ℝ), ?_, 1, ?_⟩
  · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  · intro n hn
    have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
    have hn_ne_zero : n ≠ 0 := by omega
    have hlog : Nat.log b (b * n) = Nat.log b n + 1 := by
      rw [Nat.mul_comm]
      exact Nat.log_mul_base hb hn_ne_zero
    simp [criticalPowerScale, hlog, abs_of_nonneg (pow_nonneg ha_nonneg _),
      pow_succ, mul_comm]

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

/-! ## Adjacent powers generate sandwich witnesses -/

/--
Every positive natural input lies between adjacent powers of a base
{lit}`b > 1`.
This is the arithmetic step that CLRS uses implicitly when it extends
exact-power recurrence bounds to all input sizes.
-/
theorem powerInterval_of_pos (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) :
    b ^ Nat.log b n ≤ n ∧ n < b ^ (Nat.log b n + 1) :=
  ⟨Nat.pow_log_le_self b hn, by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hb n⟩

private theorem power_log_ge_step_threshold
    {b step n j₀ : ℕ} (hb : 1 < b)
    (hj₀_step : Nat.log b step + 1 ≤ j₀)
    (hj₀_log : j₀ ≤ Nat.log b n) :
    step ≤ b ^ Nat.log b n := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  have hstep_lt : step < b ^ (Nat.log b step + 1) :=
    Nat.lt_pow_succ_log_self hb step
  have hpow_le :
      b ^ (Nat.log b step + 1) ≤ b ^ Nat.log b n :=
    Nat.pow_le_pow_right hb_pos (Nat.le_trans hj₀_step hj₀_log)
  exact Nat.le_trans (Nat.le_of_lt hstep_lt) hpow_le

/--
Monotone scales with eventual one-step control automatically satisfy the upper
power-sandwich hypothesis: for every large {lit}`n`, choose the next exact
power above it.
-/
theorem eventuallyPowerUpperSandwich_of_powerStep
    (b : ℕ) (g : ℕ → ℝ) (hb : 1 < b)
    (hg_mono : MonotoneAbs g)
    (hg_step : EventuallyPowerStepBound b g) :
    EventuallyPowerUpperSandwich b g := by
  rcases hg_step with ⟨A, hA_pos, step₀, hstep⟩
  refine ⟨A, hA_pos, ?_⟩
  intro i₀
  let j₀ := max i₀ (Nat.log b step₀ + 1)
  refine ⟨b ^ j₀, ?_⟩
  intro n hn
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  have hn_ne_zero : n ≠ 0 := by
    have hpow_pos : 0 < b ^ j₀ := pow_pos hb_pos j₀
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hpow_pos hn)
  have hj₀_log : j₀ ≤ Nat.log b n :=
    Nat.le_log_of_pow_le hb hn
  let i := Nat.log b n + 1
  refine ⟨i, ?_, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_max_left i₀ (Nat.log b step₀ + 1))
      (Nat.le_trans hj₀_log (Nat.le_succ _))
  · exact Nat.le_of_lt (powerInterval_of_pos b n hb hn_ne_zero).2
  · have hstep_arg : step₀ ≤ b ^ Nat.log b n :=
      power_log_ge_step_threshold (b := b) (step := step₀) (n := n)
        (j₀ := j₀) hb (Nat.le_max_right _ _) hj₀_log
    have hlocal := hstep (b ^ Nat.log b n) hstep_arg
    have hmono_to_n : |g (b ^ Nat.log b n)| ≤ |g n| :=
      hg_mono (Nat.pow_log_le_self b hn_ne_zero)
    calc
      |g (b ^ i)| = |g (b * b ^ Nat.log b n)| := by
        simp [i, pow_succ, Nat.mul_comm]
      _ ≤ A * |g (b ^ Nat.log b n)| := hlocal
      _ ≤ A * |g n| := by
        gcongr

/--
Monotone scales with eventual one-step control automatically satisfy the lower
power-sandwich hypothesis: for every large {lit}`n`, choose the previous exact
power below it.
-/
theorem eventuallyPowerLowerSandwich_of_powerStep
    (b : ℕ) (g : ℕ → ℝ) (hb : 1 < b)
    (hg_mono : MonotoneAbs g)
    (hg_step : EventuallyPowerStepBound b g) :
    EventuallyPowerLowerSandwich b g := by
  rcases hg_step with ⟨A, hA_pos, step₀, hstep⟩
  refine ⟨A, hA_pos, ?_⟩
  intro i₀
  let j₀ := max i₀ (Nat.log b step₀ + 1)
  refine ⟨b ^ j₀, ?_⟩
  intro n hn
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  have hn_ne_zero : n ≠ 0 := by
    have hpow_pos : 0 < b ^ j₀ := pow_pos hb_pos j₀
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hpow_pos hn)
  have hj₀_log : j₀ ≤ Nat.log b n :=
    Nat.le_log_of_pow_le hb hn
  let i := Nat.log b n
  refine ⟨i, ?_, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_max_left i₀ (Nat.log b step₀ + 1)) hj₀_log
  · exact (powerInterval_of_pos b n hb hn_ne_zero).1
  · have hstep_arg : step₀ ≤ b ^ Nat.log b n :=
      power_log_ge_step_threshold (b := b) (step := step₀) (n := n)
        (j₀ := j₀) hb (Nat.le_max_right _ _) hj₀_log
    have hlocal := hstep (b ^ Nat.log b n) hstep_arg
    have hn_le_next :
        n ≤ b ^ (Nat.log b n + 1) :=
      Nat.le_of_lt (powerInterval_of_pos b n hb hn_ne_zero).2
    calc
      |g n| ≤ |g (b ^ (Nat.log b n + 1))| := hg_mono hn_le_next
      _ = |g (b * b ^ Nat.log b n)| := by
        simp [pow_succ, Nat.mul_comm]
      _ ≤ A * |g (b ^ Nat.log b n)| := hlocal
      _ = A * |g (b ^ i)| := by simp [i]

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

/--
Direct all-input transfer theorem from exact powers using adjacent-power
regularity of the comparison scale.  This packages the CLRS proof step:
choose the exact power immediately below or above an arbitrary input {lit}`n`,
use monotonicity for {lit}`T`, and use one-step regularity for {lit}`g`.
-/
theorem allInput_bigTheta_of_powerStep
    (b : ℕ) (T g : ℕ → ℝ) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (hg_mono : MonotoneAbs g)
    (hg_step : EventuallyPowerStepBound b g)
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigTheta T g :=
  allInput_bigTheta_of_power_sandwich b T g hT_mono
    (eventuallyPowerUpperSandwich_of_powerStep b g hb hg_mono hg_step)
    (eventuallyPowerLowerSandwich_of_powerStep b g hb hg_mono hg_step)
    h_power

/--
Concrete all-input bridge for the first exact-power Master scale.  If the
exact-power sequence {lit}`T(b^i)` is {lit}`Θ(a^i)` and the cost is monotone in
absolute value, then the all-input cost is {lit}`Θ(a^(⌊log_b n⌋))`, represented
by {name}`criticalPowerScale`.

This theorem is intentionally discrete: a later analytic comparison can relate
{name}`criticalPowerScale` to {lit}`n^(log_b a)` when that real-valued scale is
needed.
-/
theorem allInput_bigTheta_of_criticalPowerScale
    (a b : ℕ) (T : ℕ → ℝ) (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => (a : ℝ) ^ i)) :
    Chapter03.isBigTheta T (criticalPowerScale a b) := by
  have h_power_scale :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => criticalPowerScale a b (b ^ i)) := by
    have hscale :
        (fun i : ℕ => criticalPowerScale a b (b ^ i)) =
          (fun i : ℕ => (a : ℝ) ^ i) := by
      funext i
      exact criticalPowerScale_exactPower a b i hb
    rw [hscale]
    exact h_power
  exact allInput_bigTheta_of_powerStep b T (criticalPowerScale a b) hb
    hT_mono
    (criticalPowerScale_monotoneAbs a b ha)
    (criticalPowerScale_powerStepBound a b ha hb)
    h_power_scale

end Chapter04
end CLRS
