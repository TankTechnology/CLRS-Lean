import CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions.TextbookIdentities

open Filter
open scoped Topology

/-!
# Robbins' finite Stirling error

CLRS equation (3.29) uses the effective error exponent in Stirling's
approximation.  Mathlib exposes the exact positive series for successive
logarithmic errors and its sharp stepwise bound; this file telescopes those
facts to the textbook finite bound.
-/

namespace CLRS
namespace Chapter03

/-- The logarithmic error between the normalized Stirling ratio and its limit. -/
noncomputable def robbinsAlpha (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)

private theorem robbinsAlpha_hasSum (n : ℕ) :
    HasSum
      (fun k : ℕ => Real.log (Stirling.stirlingSeq (n + 1 + k)) -
        Real.log (Stirling.stirlingSeq ((n + 1 + k) + 1)))
      (robbinsAlpha (n + 1)) := by
  let f (k : ℕ) := Real.log (Stirling.stirlingSeq (n + 1 + k))
  change HasSum (fun k => f k - f (k + 1)) (robbinsAlpha (n + 1))
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hlog : Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq k)) atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
      (Real.continuousAt_log (Real.sqrt_pos.mpr Real.pi_pos).ne').tendsto.comp
        Stirling.tendsto_stirlingSeq_sqrt_pi
    have htail : Tendsto f atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
      simpa [f, Function.comp_def, add_comm] using
        hlog.comp (tendsto_add_atTop_nat (n + 1))
    convert tendsto_const_nhds.sub htail using 1
    · ext m
      rw [Finset.sum_range_sub']
    · simp [robbinsAlpha, f]
  · intro k
    apply sub_nonneg.mpr
    simpa [f, Function.comp_apply, add_assoc, add_comm, add_left_comm] using
      Stirling.log_stirlingSeq'_antitone (Nat.le_succ (n + k))

private theorem robbinsUpper_hasSum (n : ℕ) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (12 * ((k + n + 1 : ℕ) : ℝ)) -
        1 / (12 * (((k + 1) + n + 1 : ℕ) : ℝ)))
      (1 / (12 * ((0 + n + 1 : ℕ) : ℝ))) := by
  let g (k : ℕ) : ℝ := 1 / (12 * ((k + n + 1 : ℕ) : ℝ))
  change HasSum (fun k => g k - g (k + 1)) (g 0)
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hinv : Tendsto g atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      have hcast : Tendsto (fun m : ℕ => ((m + (n + 1) : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (n + 1))
      simpa [g, add_assoc] using
        hcast.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
    convert tendsto_const_nhds.sub hinv using 1
    ext m
    rw [Finset.sum_range_sub']
    simp [g]
  · intro k
    dsimp [g]
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le (by positivity)
    norm_cast
    omega

/-- The upper half `αₙ ≤ 1/(12n)` of the Robbins bound, for positive `n`. -/
theorem robbinsAlpha_le (n : ℕ) :
    robbinsAlpha (n + 1) ≤ 1 / (12 * ((n + 1 : ℕ) : ℝ)) := by
  have hle : robbinsAlpha (n + 1) ≤ 1 / (12 * ((0 + n + 1 : ℕ) : ℝ)) := by
    apply hasSum_le (fun k => ?_) (robbinsAlpha_hasSum n) (robbinsUpper_hasSum n)
    have h := Stirling.log_stirlingSeq_sdiff_le (n + 1 + k)
    calc
      Real.log (Stirling.stirlingSeq (n + 1 + k)) -
          Real.log (Stirling.stirlingSeq ((n + 1 + k) + 1))
        ≤ 1 / (12 * ((n + 1 + k : ℕ) : ℝ) * ((n + 1 + k : ℕ) + 1)) := h
      _ = (1 : ℝ) / (12 * ((k + n + 1 : ℕ) : ℝ)) -
          1 / (12 * (((k + 1) + n + 1 : ℕ) : ℝ)) := by
        have hm : (0 : ℝ) < ((n + 1 + k : ℕ) : ℝ) := by positivity
        push_cast
        field_simp
        ring
  simpa using hle

private theorem robbinsLogStep_lt (n : ℕ) :
    Real.log (Stirling.stirlingSeq (n + 1)) -
        Real.log (Stirling.stirlingSeq (n + 2)) <
      1 / (12 * ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  let r := ((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ^ 2
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    grw [← n.zero_le]
    norm_num
  have hg : HasSum (fun j : ℕ => r ^ (j + 1) / 3)
      (1 / (12 * ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := by
    grind [((hasSum_geometric_of_lt_one hr0 hr1).mul_right r).div_const 3]
  have hf := Stirling.log_stirlingSeq_sdiff_hasSum n
  have hpoint : ∀ j : ℕ,
      (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ) + 1) *
          ((1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (j + 1) ≤
        r ^ (j + 1) / 3 := by
    intro j
    simpa [r, field] using
      show (3 : ℝ) ≤ 2 * (j + 1) + 1 by norm_cast; omega
  have hstrict :
      (1 : ℝ) / (2 * ((1 + 1 : ℕ) : ℝ) + 1) *
          ((1 / (2 * ((n + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (1 + 1) <
        r ^ (1 + 1) / 3 := by
    have hpow : 0 < r ^ (1 + 1) := by positivity
    have hcoef : (1 : ℝ) / (2 * ((1 + 1 : ℕ) : ℝ) + 1) < 1 / 3 := by norm_num
    simpa [r, div_eq_mul_inv, mul_comm] using mul_lt_mul_of_pos_right hcoef hpow
  exact hasSum_lt hpoint hstrict hf hg

/-- The strict upper half `αₙ < 1/(12n)` of Robbins' bound. -/
theorem robbinsAlpha_lt (n : ℕ) :
    robbinsAlpha (n + 1) < 1 / (12 * ((n + 1 : ℕ) : ℝ)) := by
  have hpoint : ∀ k : ℕ,
      Real.log (Stirling.stirlingSeq (n + 1 + k)) -
          Real.log (Stirling.stirlingSeq ((n + 1 + k) + 1)) ≤
        (1 : ℝ) / (12 * ((k + n + 1 : ℕ) : ℝ)) -
          1 / (12 * (((k + 1) + n + 1 : ℕ) : ℝ)) := by
    intro k
    have h := Stirling.log_stirlingSeq_sdiff_le (n + 1 + k)
    calc
      Real.log (Stirling.stirlingSeq (n + 1 + k)) -
          Real.log (Stirling.stirlingSeq ((n + 1 + k) + 1))
        ≤ 1 / (12 * ((n + 1 + k : ℕ) : ℝ) * ((n + 1 + k : ℕ) + 1)) := h
      _ = (1 : ℝ) / (12 * ((k + n + 1 : ℕ) : ℝ)) -
          1 / (12 * (((k + 1) + n + 1 : ℕ) : ℝ)) := by
        have hm : (0 : ℝ) < ((n + 1 + k : ℕ) : ℝ) := by positivity
        push_cast
        field_simp
        ring
  have hstrict :
      Real.log (Stirling.stirlingSeq (n + 1 + 0)) -
          Real.log (Stirling.stirlingSeq ((n + 1 + 0) + 1)) <
        (1 : ℝ) / (12 * ((0 + n + 1 : ℕ) : ℝ)) -
          1 / (12 * (((0 + 1) + n + 1 : ℕ) : ℝ)) := by
    have h := robbinsLogStep_lt n
    calc
      Real.log (Stirling.stirlingSeq (n + 1 + 0)) -
          Real.log (Stirling.stirlingSeq ((n + 1 + 0) + 1))
        < 1 / (12 * ((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by simpa using h
      _ = (1 : ℝ) / (12 * ((0 + n + 1 : ℕ) : ℝ)) -
          1 / (12 * (((0 + 1) + n + 1 : ℕ) : ℝ)) := by
        have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        push_cast
        field_simp
        ring
  have hlt := hasSum_lt hpoint hstrict (robbinsAlpha_hasSum n) (robbinsUpper_hasSum n)
  simpa using hlt

private theorem robbinsLower_hasSum (n : ℕ) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (12 * ((k + n + 1 : ℕ) : ℝ) + 1) -
        1 / (12 * (((k + 1) + n + 1 : ℕ) : ℝ) + 1))
      (1 / (12 * ((0 + n + 1 : ℕ) : ℝ) + 1)) := by
  let g (k : ℕ) : ℝ := 1 / (12 * ((k + n + 1 : ℕ) : ℝ) + 1)
  change HasSum (fun k => g k - g (k + 1)) (g 0)
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hinv : Tendsto g atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      have hcast : Tendsto (fun m : ℕ => ((m + (n + 1) : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (n + 1))
      have hmul := hcast.const_mul_atTop (by norm_num : (0 : ℝ) < 12)
      simpa [g, add_assoc] using tendsto_atTop_add_const_right atTop 1 hmul
    convert tendsto_const_nhds.sub hinv using 1
    ext m
    rw [Finset.sum_range_sub']
    simp [g]
  · intro k
    dsimp [g]
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le (by positivity)
    norm_cast
    omega

private theorem robbinsLowerStep_lt_first (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / (12 * (m : ℝ) + 1) - 1 / (12 * ((m + 1 : ℕ) : ℝ) + 1) <
      (1 / 3 : ℝ) * ((1 / (2 * (m : ℝ) + 1)) ^ 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  field_simp
  ring_nf at *
  nlinarith

private theorem robbinsFirstTerm_le_step (n k : ℕ) :
    (1 / 3 : ℝ) * ((1 / (2 * ((n + 1 + k : ℕ) : ℝ) + 1)) ^ 2) ≤
      Real.log (Stirling.stirlingSeq (n + 1 + k)) -
        Real.log (Stirling.stirlingSeq ((n + 1 + k) + 1)) := by
  let term (j : ℕ) : ℝ :=
    1 / (2 * ((j + 1 : ℕ) : ℝ) + 1) *
      ((1 / (2 * ((n + k + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (j + 1)
  have hseries := Stirling.log_stirlingSeq_sdiff_hasSum (n + k)
  have hsingle : HasSum (fun j : ℕ => if j = 0 then term 0 else 0) (term 0) :=
    hasSum_ite_eq 0 (term 0)
  have hle : term 0 ≤
      Real.log (Stirling.stirlingSeq (n + k + 1)) -
        Real.log (Stirling.stirlingSeq (n + k + 2)) := by
    apply hasSum_le (fun j => ?_) hsingle hseries
    by_cases hj : j = 0
    · subst j; simp [term]
    · simp only [hj, ↓reduceIte]
      positivity
  norm_num [term, add_assoc, add_comm, add_left_comm] at hle ⊢
  exact hle

/-- The strict lower half `1/(12n+1) < αₙ` of Robbins' bound. -/
theorem robbinsAlpha_gt (n : ℕ) :
    1 / (12 * ((n + 1 : ℕ) : ℝ) + 1) < robbinsAlpha (n + 1) := by
  have hlt :
      1 / (12 * ((0 + n + 1 : ℕ) : ℝ) + 1) < robbinsAlpha (n + 1) := by
    have hpoint : ∀ k : ℕ,
        (1 : ℝ) / (12 * ((k + n + 1 : ℕ) : ℝ) + 1) -
            1 / (12 * (((k + 1) + n + 1 : ℕ) : ℝ) + 1) ≤
          Real.log (Stirling.stirlingSeq (n + 1 + k)) -
            Real.log (Stirling.stirlingSeq ((n + 1 + k) + 1)) := by
      intro k
      simpa [add_assoc, add_comm, add_left_comm] using
        (robbinsLowerStep_lt_first (n + 1 + k) (by omega)).le.trans
          (robbinsFirstTerm_le_step n k)
    have hstrict :
        (1 : ℝ) / (12 * ((0 + n + 1 : ℕ) : ℝ) + 1) -
            1 / (12 * (((0 + 1) + n + 1 : ℕ) : ℝ) + 1) <
          Real.log (Stirling.stirlingSeq (n + 1 + 0)) -
            Real.log (Stirling.stirlingSeq ((n + 1 + 0) + 1)) := by
      simpa [add_assoc, add_comm, add_left_comm] using
        (robbinsLowerStep_lt_first (n + 1) (by omega)).trans_le
          (robbinsFirstTerm_le_step n 0)
    exact hasSum_lt hpoint hstrict (robbinsLower_hasSum n) (robbinsAlpha_hasSum n)
  simpa using hlt

/-- The normalized error exponent reconstructs the factorial exactly. -/
theorem factorial_eq_stirling_mul_exp_robbinsAlpha (n : ℕ) :
    (Nat.factorial (n + 1) : ℝ) =
      Real.sqrt (2 * Real.pi * (n + 1)) *
        (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1) *
        Real.exp (robbinsAlpha (n + 1)) := by
  have hN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hs : 0 < Stirling.stirlingSeq (n + 1) := Stirling.stirlingSeq'_pos n
  have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsqrt_two_n : 0 < Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) := by positivity
  have hpow : 0 < (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1) := by positivity
  have hsqrt :
      Real.sqrt (2 * Real.pi * ((n : ℝ) + 1)) =
        Real.sqrt Real.pi * Real.sqrt (2 * ((n : ℝ) + 1)) := by
    rw [show 2 * Real.pi * ((n : ℝ) + 1) =
      Real.pi * (2 * ((n : ℝ) + 1)) by ring,
      Real.sqrt_mul (le_of_lt Real.pi_pos)]
  rw [robbinsAlpha, Real.exp_sub, Real.exp_log hs, Real.exp_log hsqrtpi,
    Stirling.stirlingSeq]
  push_cast
  rw [hsqrt]
  field_simp

/-- The exact strict effective Robbins bounds from CLRS equation (3.29). -/
theorem robbinsAlpha_bounds (n : ℕ) :
    1 / (12 * ((n + 1 : ℕ) : ℝ) + 1) < robbinsAlpha (n + 1) ∧
      robbinsAlpha (n + 1) < 1 / (12 * ((n + 1 : ℕ) : ℝ)) :=
  ⟨robbinsAlpha_gt n, robbinsAlpha_lt n⟩

end Chapter03
end CLRS
