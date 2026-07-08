import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib.Tactic

open Finset
open scoped BigOperators

/-!
# 4.5. The Master Method - Exact Powers

This file proves the exact-power algebraic core of the Chapter 4 Master Theorem.
For recurrences on exact powers,
{lit}`T(b^(i+1)) = a * T(b^i) + f(b^(i+1))`, the normalized quantity
{lit}`T(b^i) / a^i` unfolds into the initial value plus a finite sum of normalized
forcing terms.  The three Master-style exact-power criteria below then turn
bounded, constant, or tail-dominated normalized forcing into the expected
asymptotic conclusions.

Main result:

- Theorem {lit}`CLRS.Chapter04.h_formula`: the normalized exact-power recurrence
  expansion.
- Theorem {lit}`CLRS.Chapter04.master_case1_geometric`: bounded normalized
  forcing, obtained from a geometric upper bound, gives {lit}`T(b^i) = Θ(a^i)`.
- Theorem {lit}`CLRS.Chapter04.master_case2_constant_forcing`: constant
  normalized forcing gives {lit}`T(b^i) = Θ((i+1)a^i)`.
- Theorem {lit}`CLRS.Chapter04.master_case3_tail_dominated`: tail-dominated
  normalized forcing gives the third Master-style exact-power case.

Status: `proved` for the exact-power Master theorem core.
The all-input extension (floor/ceiling sandwiching) is proved in Section 4.6.
-/

namespace CLRS
namespace Chapter04

/-! ## Exact-power recurrences -/

/-- Exact-power form of the CLRS Master Theorem recurrence. -/
structure ExactPowerRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ i : ℕ, T (b ^ (i + 1)) = (a : ℝ) * T (b ^ i) + f (b ^ (i + 1))

/-- The normalized value {lit}`T(b^i) / a^i`. -/
noncomputable def normalizedValue (a b : ℕ) (T : ℕ → ℝ) (i : ℕ) : ℝ :=
  T (b ^ i) / ((a : ℝ) ^ i)

/-- The normalized forcing term contributed at the step from {lit}`i` to {lit}`i+1`. -/
noncomputable def normalizedForcing (a b : ℕ) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  f (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1))

/-! ## Public theorem -/

/--
Unroll the exact-power recurrence after dividing by {lit}`a^i`.

This is the algebraic spine of the Master Theorem proof: the remaining CLRS
case analysis is a question about bounding the finite sum on the right-hand
side.
-/
theorem h_formula (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T) (ha_ne_zero : (a : ℝ) ≠ 0)
    (i : ℕ) :
    T (b ^ i) / ((a : ℝ) ^ i) =
      T (b ^ 0) / ((a : ℝ) ^ 0) +
        (∑ k ∈ range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))) := by
  induction' i with i ih
  · simp
  · rw [show
        T (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1)) =
          T (b ^ i) / ((a : ℝ) ^ i) +
            f (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1)) by
        field_simp [ha_ne_zero, pow_succ]
        rw [h_rec.step i]
        ring]
    rw [ih]
    simp [sum_range_succ, add_assoc]

lemma normalizedValue_eq_base_add_sum (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T) (ha_ne_zero : (a : ℝ) ≠ 0)
    (i : ℕ) :
    normalizedValue a b T i =
      normalizedValue a b T 0 +
        (∑ k ∈ range i, normalizedForcing a b f k) := by
  simpa [normalizedValue, normalizedForcing] using
    h_formula a b f T h_rec ha_ne_zero i

private theorem isBigTheta_of_eventual_bounds {f g : ℕ → ℝ}
    (hO : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n, n ≥ n₀ → |f n| ≤ C * |g n|)
    (hΩ : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n ≥ n₀ → c * |g n| ≤ |f n|) :
    Chapter03.isBigTheta f g := by
  exact ⟨(Chapter03.isBigO_iff f g).2 hO, (Chapter03.isBigOmega_iff f g).2 hΩ⟩

/--
If the normalized recurrence values are eventually within constant multiples of
a nonnegative scale {lit}`s`, then the original exact-power recurrence is {lit}`Θ(s(i)a^i)`.
-/
theorem theta_of_normalized_by_scale (a b : ℕ) (T : ℕ → ℝ) (scale : ℕ → ℝ)
    (ha_pos : 0 < (a : ℝ))
    (hscale_nonneg : ∀ i, 0 ≤ scale i)
    (h_lower :
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ →
        c * scale i ≤ normalizedValue a b T i)
    (h_upper :
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ →
        normalizedValue a b T i ≤ C * scale i) :
    Chapter03.isBigTheta
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ => scale i * ((a : ℝ) ^ i)) := by
  rcases h_lower with ⟨c, hc_pos, nL, hL⟩
  rcases h_upper with ⟨C, hC_pos, nU, hU⟩
  have ha_ne_zero : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  refine isBigTheta_of_eventual_bounds ?_ ?_
  · refine ⟨C, hC_pos, max nL nU, ?_⟩
    intro i hi
    have hiL : i ≥ nL := le_trans (Nat.le_max_left _ _) hi
    have hiU : i ≥ nU := le_trans (Nat.le_max_right _ _) hi
    have hscale_i := hscale_nonneg i
    have hnv_nonneg : 0 ≤ normalizedValue a b T i := by
      have hmul_nonneg : 0 ≤ c * scale i := mul_nonneg hc_pos.le hscale_i
      exact hmul_nonneg.trans (hL i hiL)
    have hT_eq :
        T (b ^ i) = ((a : ℝ) ^ i) * normalizedValue a b T i := by
      dsimp [normalizedValue]
      field_simp [pow_ne_zero i ha_ne_zero]
    have hT_abs :
        |T (b ^ i)| = ((a : ℝ) ^ i) * normalizedValue a b T i := by
      rw [hT_eq, abs_mul, abs_of_nonneg (pow_nonneg ha_pos.le i),
        abs_of_nonneg hnv_nonneg]
    have htarget_abs :
        |scale i * ((a : ℝ) ^ i)| = scale i * ((a : ℝ) ^ i) := by
      rw [abs_of_nonneg (mul_nonneg hscale_i (pow_nonneg ha_pos.le i))]
    calc
      |T (b ^ i)| = ((a : ℝ) ^ i) * normalizedValue a b T i := hT_abs
      _ ≤ ((a : ℝ) ^ i) * (C * scale i) := by
        gcongr
        exact hU i hiU
      _ = C * (scale i * ((a : ℝ) ^ i)) := by ring
      _ = C * |scale i * ((a : ℝ) ^ i)| := by rw [htarget_abs]
  · refine ⟨c, hc_pos, max nL nU, ?_⟩
    intro i hi
    have hiL : i ≥ nL := le_trans (Nat.le_max_left _ _) hi
    have hscale_i := hscale_nonneg i
    have hnv_nonneg : 0 ≤ normalizedValue a b T i := by
      have hmul_nonneg : 0 ≤ c * scale i := mul_nonneg hc_pos.le hscale_i
      exact hmul_nonneg.trans (hL i hiL)
    have hT_eq :
        T (b ^ i) = ((a : ℝ) ^ i) * normalizedValue a b T i := by
      dsimp [normalizedValue]
      field_simp [pow_ne_zero i ha_ne_zero]
    have hT_abs :
        |T (b ^ i)| = ((a : ℝ) ^ i) * normalizedValue a b T i := by
      rw [hT_eq, abs_mul, abs_of_nonneg (pow_nonneg ha_pos.le i),
        abs_of_nonneg hnv_nonneg]
    have htarget_abs :
        |scale i * ((a : ℝ) ^ i)| = scale i * ((a : ℝ) ^ i) := by
      rw [abs_of_nonneg (mul_nonneg hscale_i (pow_nonneg ha_pos.le i))]
    calc
      c * |scale i * ((a : ℝ) ^ i)| = c * (scale i * ((a : ℝ) ^ i)) := by
        rw [htarget_abs]
      _ = ((a : ℝ) ^ i) * (c * scale i) := by ring
      _ ≤ ((a : ℝ) ^ i) * normalizedValue a b T i := by
        gcongr
        exact hL i hiL
      _ = |T (b ^ i)| := by rw [hT_abs]

private lemma geometric_sum_le_tsum_bound {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (i : ℕ) :
    (∑ k ∈ range i, r ^ k) ≤ (1 - r)⁻¹ := by
  have hsumm : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr_nonneg hr_lt_one
  calc
    (∑ k ∈ range i, r ^ k) ≤ ∑' k : ℕ, r ^ k :=
      hsumm.sum_le_tsum (range i) (fun k _ => pow_nonneg hr_nonneg k)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr_nonneg hr_lt_one

/--
Master case 1, exact-power form: if the normalized forcing terms are bounded by
a convergent geometric sequence, then {lit}`T(b^i) = Θ(a^i)`.
-/
theorem master_case1_geometric (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T) (ha_pos : 0 < (a : ℝ))
    (h_base_pos : 0 < normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ => ((a : ℝ) ^ i)) := by
  have ha_ne_zero : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  have hsum_bound :
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ i, (∑ k ∈ range i, normalizedForcing a b f k) ≤ B := by
    refine ⟨C * (1 - r)⁻¹, mul_nonneg hC_pos.le (inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)), ?_⟩
    intro i
    calc
      (∑ k ∈ range i, normalizedForcing a b f k)
          ≤ ∑ k ∈ range i, C * r ^ k := by
        exact Finset.sum_le_sum (fun k _ => h_term_upper k)
      _ = C * (∑ k ∈ range i, r ^ k) := by
        simp [Finset.mul_sum]
      _ ≤ C * (1 - r)⁻¹ := by
        gcongr
        exact geometric_sum_le_tsum_bound hr_nonneg hr_lt_one i
  rcases hsum_bound with ⟨B, hB_nonneg, hB⟩
  have h_lower :
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ →
        c * (fun _ : ℕ => (1 : ℝ)) i ≤ normalizedValue a b T i := by
    refine ⟨normalizedValue a b T 0, h_base_pos, 0, ?_⟩
    intro i _hi
    have h_formula_i :=
      normalizedValue_eq_base_add_sum a b f T h_rec ha_ne_zero i
    have hsum_nonneg : 0 ≤ ∑ k ∈ range i, normalizedForcing a b f k :=
      Finset.sum_nonneg (fun k _ => h_term_nonneg k)
    calc
      normalizedValue a b T 0 * (1 : ℝ) = normalizedValue a b T 0 := by ring
      _ ≤ normalizedValue a b T i := by
        rw [h_formula_i]
        linarith
  have h_upper :
      ∃ C' : ℝ, 0 < C' ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ →
        normalizedValue a b T i ≤ C' * (fun _ : ℕ => (1 : ℝ)) i := by
    refine ⟨normalizedValue a b T 0 + B, by linarith, 0, ?_⟩
    intro i _hi
    have h_formula_i :=
      normalizedValue_eq_base_add_sum a b f T h_rec ha_ne_zero i
    calc
      normalizedValue a b T i =
          normalizedValue a b T 0 + (∑ k ∈ range i, normalizedForcing a b f k) := h_formula_i
      _ ≤ normalizedValue a b T 0 + B := by
        gcongr
        exact hB i
      _ = (normalizedValue a b T 0 + B) * (1 : ℝ) := by ring
  simpa using
    theta_of_normalized_by_scale a b T (fun _ : ℕ => (1 : ℝ)) ha_pos
      (fun _ => by norm_num) h_lower h_upper

/--
Master case 2, exact-power form: if the normalized forcing terms are trapped
between positive constants, then {lit}`T(b^i) = Θ((i+1)a^i)`.
-/
theorem master_case2_constant_forcing (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T) (ha_pos : 0 < (a : ℝ))
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing a b f k)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C) :
    Chapter03.isBigTheta
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ => ((i : ℝ) + 1) * ((a : ℝ) ^ i)) := by
  have ha_ne_zero : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  refine theta_of_normalized_by_scale a b T (fun i => (i : ℝ) + 1) ha_pos
    (fun i => by positivity) ?_ ?_
  · refine ⟨c / 2, by positivity, 1, ?_⟩
    intro i hi
    have h_formula_i :=
      normalizedValue_eq_base_add_sum a b f T h_rec ha_ne_zero i
    have hsum_lower :
        c * (i : ℝ) ≤ ∑ k ∈ range i, normalizedForcing a b f k := by
      calc
        c * (i : ℝ) = ∑ _k ∈ range i, c := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ k ∈ range i, normalizedForcing a b f k := by
          exact Finset.sum_le_sum (fun k _ => h_term_lower k)
    have hi_real : 1 ≤ (i : ℝ) := by exact_mod_cast hi
    calc
      (c / 2) * ((i : ℝ) + 1) ≤ c * (i : ℝ) := by nlinarith [hc_pos]
      _ ≤ ∑ k ∈ range i, normalizedForcing a b f k := hsum_lower
      _ ≤ normalizedValue a b T i := by
        rw [h_formula_i]
        linarith
  · refine ⟨normalizedValue a b T 0 + C, by linarith, 0, ?_⟩
    intro i _hi
    have h_formula_i :=
      normalizedValue_eq_base_add_sum a b f T h_rec ha_ne_zero i
    have hsum_upper :
        (∑ k ∈ range i, normalizedForcing a b f k) ≤ C * (i : ℝ) := by
      calc
        (∑ k ∈ range i, normalizedForcing a b f k) ≤ ∑ _k ∈ range i, C := by
          exact Finset.sum_le_sum (fun k _ => h_term_upper k)
        _ = C * (i : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hi_nonneg : 0 ≤ (i : ℝ) := by positivity
    calc
      normalizedValue a b T i =
          normalizedValue a b T 0 + (∑ k ∈ range i, normalizedForcing a b f k) := h_formula_i
      _ ≤ normalizedValue a b T 0 + C * (i : ℝ) := by
        gcongr
      _ ≤ (normalizedValue a b T 0 + C) * ((i : ℝ) + 1) := by
        nlinarith [h_base_nonneg, hC_pos]

/--
Master case 3, exact-power form: if the normalized recurrence value is
eventually controlled by the last normalized forcing term, then the last term
dominates the whole recurrence tree.
-/
theorem master_case3_tail_dominated (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T) (ha_pos : 0 < (a : ℝ))
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    (h_tail_upper :
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ → 1 ≤ i →
        normalizedValue a b T i ≤ C * normalizedForcing a b f (i - 1)) :
    Chapter03.isBigTheta
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ =>
        (if i = 0 then 1 else normalizedForcing a b f (i - 1)) * ((a : ℝ) ^ i)) := by
  have ha_ne_zero : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  refine theta_of_normalized_by_scale a b T
    (fun i : ℕ => if i = 0 then 1 else normalizedForcing a b f (i - 1))
    ha_pos ?_ ?_ ?_
  · intro i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi, h_term_nonneg]
  · refine ⟨1, by norm_num, 1, ?_⟩
    intro i hi
    have hi_pos : 0 < i := by omega
    have hi_ne : i ≠ 0 := Nat.ne_of_gt hi_pos
    have h_formula_i :=
      normalizedValue_eq_base_add_sum a b f T h_rec ha_ne_zero i
    have hlast_mem : i - 1 ∈ range i := by
      rw [Finset.mem_range]
      omega
    have hlast_le_sum :
        normalizedForcing a b f (i - 1) ≤
          ∑ k ∈ range i, normalizedForcing a b f k :=
      Finset.single_le_sum (fun k _ => h_term_nonneg k) hlast_mem
    calc
      1 * (if i = 0 then 1 else normalizedForcing a b f (i - 1))
          = normalizedForcing a b f (i - 1) := by simp [hi_ne]
      _ ≤ ∑ k ∈ range i, normalizedForcing a b f k := hlast_le_sum
      _ ≤ normalizedValue a b T i := by
        rw [h_formula_i]
        linarith
  · rcases h_tail_upper with ⟨C, hC_pos, n₀, htail⟩
    refine ⟨C, hC_pos, max 1 n₀, ?_⟩
    intro i hi
    have hi_one : 1 ≤ i := le_trans (Nat.le_max_left _ _) hi
    have hi_n₀ : i ≥ n₀ := le_trans (Nat.le_max_right _ _) hi
    have hi_ne : i ≠ 0 := by omega
    calc
      normalizedValue a b T i ≤ C * normalizedForcing a b f (i - 1) :=
        htail i hi_n₀ hi_one
      _ = C * (if i = 0 then 1 else normalizedForcing a b f (i - 1)) := by simp [hi_ne]

end Chapter04
end CLRS
