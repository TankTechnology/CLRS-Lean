import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib.Tactic

open Real Filter Asymptotics Finset
open scoped BigOperators

/-!
# 4.5. The Master Method — Exact Powers

Complete proof of the Master Theorem for recurrences on exact powers
`n = bⁱ`:  `T(bⁱ⁺¹) = a·T(bⁱ) + f(bⁱ⁺¹)`, where `f(n) = Θ(n^d)`.

Let `h(i) = T(bⁱ)/aⁱ`.  Then `h(i+1) = h(i) + f(bⁱ⁺¹)/aⁱ⁺¹`, so
`h(i) = h(0) + Σ_{k=1}^i f(bᵏ)/aᵏ`.  With `r = b^d/a`, each term
`f(bᵏ)/aᵏ = Θ(rᵏ)`.  The three cases are:

1. `r < 1` (i.e. `b^d < a`): series converges → `h(i) = Θ(1)` → `T = Θ(aⁱ)`.
2. `r = 1` (i.e. `b^d = a`): harmonic sum → `h(i) = Θ(i)` → `T = Θ(i·aⁱ)`.
3. `r > 1` (i.e. `b^d > a`): dominated by last term → `T = Θ(f(bⁱ))`.
-/

namespace CLRS
namespace Chapter04

open Chapter03

structure ExactPowerRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ i : ℕ, T (b ^ (i + 1)) = (a : ℝ) * T (b ^ i) + f (b ^ (i + 1))

lemma h_formula (a b : ℕ) (f T : ℕ → ℝ) (h_rec : ExactPowerRecurrence a b f T)
    (ha_pos : (a : ℝ) ≠ 0) (i : ℕ) :
    T (b ^ i) / ((a : ℝ) ^ i) = T (b ^ 0) / ((a : ℝ) ^ 0) +
      (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))) := by
  induction' i with i IH
  · simp
  · rw [show T (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1))
        = (T (b ^ i) / ((a : ℝ) ^ i)) + f (b ^ (i + 1)) / ((a : ℝ) ^ (i + 1)) by
      field_simp [ha_pos, pow_succ]; rw [h_rec.step i]; ring]
    rw [IH]; simp [sum_range_succ, add_assoc]

/-- **Case 1:** `b^d < a`.  The series `Σ rᵏ` converges, `h` is bounded. -/
theorem master_case1 (a b d : ℕ) (ha : 1 ≤ a) (hb : 1 < b)
    (f T : ℕ → ℝ) (h_rec : ExactPowerRecurrence a b f T)
    (h_f_theta : isBigTheta f (fun n : ℕ => (n : ℝ) ^ (d : ℕ)))
    (h_nonneg_T : ∀ i, 0 ≤ T (b ^ i))
    (h_nonneg_f : ∀ n, 0 ≤ f n) (h_T0_pos : 0 < T (b ^ 0))
    (h_cond : (b : ℕ) ^ d < a) :
    isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => ((a : ℝ) ^ i)) := by
  have ha_pos : (a : ℝ) > 0 := by exact_mod_cast (by omega : 0 < a)
  have ha_ne_zero : (a : ℝ) ≠ 0 := by linarith
  let r := ((b : ℝ) ^ (d : ℕ)) / (a : ℝ)
  have hr0 : 0 ≤ r := div_nonneg (by positivity) (by positivity)
  have hr1 : r < 1 := (div_lt_one ha_pos).mpr (by exact mod_cast h_cond)
  rcases h_f_theta with ⟨h_f_O, h_f_Omega⟩
  rcases h_f_O.exists_pos with ⟨C, hC_pos, hC⟩
  have hC_ev : ∀ᶠ (n : ℕ) in atTop, f n ≤ C * ((n : ℝ) ^ (d : ℕ)) := by
    filter_upwards [hC] with n hn
    simpa [abs_of_nonneg (h_nonneg_f n), abs_pow, abs_of_nonneg (Nat.cast_nonneg n)] using hn
  rw [Filter.eventually_atTop] at hC_ev; rcases hC_ev with ⟨N, hN⟩
  let C' := max C ((range (max N 1)).sup' (by simp) (fun k => f (b ^ (k + 1)) / (((a : ℝ) ^ (k + 1)) * (r ^ (k + 1)))))
  have hC'_ge_C : C ≤ C' := le_max_left _ _
  have hC'_term : ∀ k, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)) ≤ C' * (r ^ (k + 1)) := by
    intro k
    by_cases hk : k < N
    · have hk_sup : f (b ^ (k + 1)) / (((a : ℝ) ^ (k + 1)) * (r ^ (k + 1))) ≤ C' :=
        le_trans (Finset.le_sup' _ (mem_range.2 hk)) (le_max_right _ _)
      have hpos : 0 < r ^ (k + 1) := pow_pos (lt_of_lt_of_le (by norm_num) (by
        -- r > 0 because b^d > 0 and a > 0
        positivity)) (k + 1)
      -- Actually r could be 0. If r = 0 then b^d = 0 → impossible.
      -- Since b ≥ 2, b^d ≥ 1, and a ≥ 1, r = b^d/a ≥ 1/a > 0. But r could be 0 if b^d = 0.
      -- b^d > 0 for b > 0, so r > 0.  So r^(k+1) > 0.
      have hr_pos : 0 < r := by
        refine div_pos (pow_pos (by exact_mod_cast (Nat.zero_lt_of_lt hb)) _) ha_pos
      have h_rpow_pos : 0 < r ^ (k + 1) := pow_pos hr_pos _
      field_simp [h_rpow_pos.ne'] at hk_sup ⊢
      nlinarith
    · -- k ≥ N: use hN with n = b^(k+1)
      have h_bpow_ge_N : N ≤ b ^ (k + 1) := by
        have h2b : 2 ≤ b := by omega
        have hk1_le_2pow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := by
          induction' k with j IH; · norm_num; rw [Nat.pow_succ]; omega
        calc N ≤ k := by omega; _ < k + 1 := by omega
          _ ≤ 2 ^ (k + 1) := hk1_le_2pow
          _ ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) h2b
      have h_fb := hN (b ^ (k + 1)) h_bpow_ge_N
      calc
        f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))
            ≤ (C * (((b : ℝ) ^ (k + 1)) ^ (d : ℕ))) / ((a : ℝ) ^ (k + 1)) := by
          refine (div_le_div_right (by positivity)).mpr h_fb
        _ = C * ((((b : ℝ) ^ (d : ℕ)) / (a : ℝ)) ^ (k + 1)) := by
          simp [div_pow, mul_div_assoc, mul_comm, pow_mul]
        _ = C * (r ^ (k + 1)) := rfl
        _ ≤ C' * (r ^ (k + 1)) := by gcongr
  have h_geom : (∑' k : ℕ, r ^ (k + 1)) = r / (1 - r) := by
    calc
      (∑' k : ℕ, r ^ (k + 1)) = (∑' k : ℕ, r ^ k * r) := by
        refine tsum_congr (fun k => ?_); rw [pow_succ]
      _ = (∑' k : ℕ, r ^ k) * r := by rw [tsum_mul_right]
      _ = (1 / (1 - r)) * r := by
        rw [tsum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])]
      _ = r / (1 - r) := by ring
  -- O-bound
  have h_O : isBigO (fun i : ℕ => T (b ^ i)) (fun i : ℕ => ((a : ℝ) ^ i)) := by
    refine Asymptotics.isBigO_of_le' atTop (fun i => ?_)
    have h_ratio : T (b ^ i) / ((a : ℝ) ^ i) ≤ T (b ^ 0) / ((a : ℝ) ^ 0) + C' * (r / (1 - r)) := by
      rw [h_formula a b f T h_rec ha_ne_zero i, div_one]
      calc
        T (b ^ 0) + (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)))
            ≤ T (b ^ 0) + (∑ k in range i, C' * (r ^ (k + 1))) := by gcongr
        _ = T (b ^ 0) + C' * (∑ k in range i, r ^ (k + 1)) := by simp [Finset.mul_sum]
        _ ≤ T (b ^ 0) + C' * (∑' k : ℕ, r ^ (k + 1)) := by
          gcongr; refine sum_le_tsum _ (fun _ _ => pow_nonneg hr0 _) ?_
          exact summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr0])
        _ = T (b ^ 0) + C' * (r / (1 - r)) := by rw [h_geom]
    calc
      T (b ^ i) = ((a : ℝ) ^ i) * (T (b ^ i) / ((a : ℝ) ^ i)) := by field_simp [ha_ne_zero]
      _ ≤ ((a : ℝ) ^ i) * (T (b ^ 0) + C' * (r / (1 - r))) := by gcongr; linarith
  -- Ω-bound
  have h_Omega : isBigOmega (fun i : ℕ => T (b ^ i)) (fun i : ℕ => ((a : ℝ) ^ i)) := by
    rw [isBigOmega_iff]
    refine ⟨T (b ^ 0), h_T0_pos, 0, fun i hi => ?_⟩
    have h_ge : T (b ^ i) ≥ ((a : ℝ) ^ i) * T (b ^ 0) := by
      induction' i with k IH; · simp
      rw [h_rec.step k]; nlinarith
    -- h_ge: T(bⁱ) ≥ aⁱ·T(b⁰)
    -- Need: T(b⁰)·aⁱ ≤ T(bⁱ)
    simpa [mul_comm] using h_ge
  exact ⟨h_O, h_Omega⟩

/-- **Case 2:** `b^d = a`.  Each term `f(bᵏ)/aᵏ = Θ(1)`, harmonic sum. -/
theorem master_case2 (a b d : ℕ) (ha : 1 ≤ a) (hb : 1 < b)
    (f T : ℕ → ℝ) (h_rec : ExactPowerRecurrence a b f T)
    (h_f_theta : isBigTheta f (fun n : ℕ => (n : ℝ) ^ (d : ℕ)))
    (h_nonneg_T : ∀ i, 0 ≤ T (b ^ i))
    (h_nonneg_f : ∀ n, 0 ≤ f n) (h_T0_pos : 0 < T (b ^ 0))
    (h_cond : (b : ℕ) ^ d = a) :
    isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => (i : ℝ) * ((a : ℝ) ^ i)) := by
  have ha_pos : (a : ℝ) > 0 := by exact_mod_cast (by omega : 0 < a)
  have ha_ne_zero : (a : ℝ) ≠ 0 := by linarith
  rcases h_f_theta with ⟨h_f_O, h_f_Omega⟩
  rcases h_f_O.exists_pos with ⟨C2, hC2_pos, hC2⟩
  rcases h_f_Omega.exists_pos with ⟨C1, hC1_pos, hC1⟩
  have hC1_ev : ∀ᶠ (n : ℕ) in atTop, C1 * ((n : ℝ) ^ (d : ℕ)) ≤ f n := by
    filter_upwards [hC1] with n hn
    simpa [abs_of_nonneg (h_nonneg_f n), abs_pow, abs_of_nonneg (Nat.cast_nonneg n), mul_comm] using hn
  rw [Filter.eventually_atTop] at hC1_ev; rcases hC1_ev with ⟨N1, hN1⟩
  have hC2_ev : ∀ᶠ (n : ℕ) in atTop, f n ≤ C2 * ((n : ℝ) ^ (d : ℕ)) := by
    filter_upwards [hC2] with n hn
    simpa [abs_of_nonneg (h_nonneg_f n), abs_pow, abs_of_nonneg (Nat.cast_nonneg n)] using hn
  rw [Filter.eventually_atTop] at hC2_ev; rcases hC2_ev with ⟨N2, hN2⟩
  let N := max N1 N2
  -- Key: since b^d = a, we have (b^k)^d / a^k = 1
  have h_ratio_one : ∀ k, (((b : ℝ) ^ k) ^ (d : ℕ)) / ((a : ℝ) ^ k) = 1 := by
    intro k
    have hb_eq_a : ((b : ℝ) ^ (d : ℕ)) = (a : ℝ) := by exact_mod_cast h_cond
    simp [div_pow, hb_eq_a, div_self (pow_ne_zero k ha_ne_zero)]
  -- Universal upper bound C2' for all terms f(b^{k+1})/a^{k+1}
  let small_max := (range (max N 1)).sup' (by simp) (fun j => f (b ^ (j + 1)) / ((a : ℝ) ^ (j + 1)))
  let C2' := max C2 small_max
  have hC2'_ge_C2 : C2 ≤ C2' := le_max_left _ _
  have hC2'_term : ∀ k, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)) ≤ C2' := by
    intro k
    by_cases hk : k < N
    · exact le_trans (Finset.le_sup' _ (mem_range.2 hk)) (le_max_right _ _)
    · -- k ≥ N: use the O(n^d) bound with h_ratio_one
      have h_fb := hN2 (b ^ (k + 1)) (by
        have h2b : 2 ≤ b := by omega
        have hk1_le_2pow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := by
          induction' k with j IH; · norm_num; rw [Nat.pow_succ]; omega
        calc N2 ≤ N := le_max_right _ _; _ ≤ k := by omega; _ < k + 1 := by omega
          _ ≤ 2 ^ (k + 1) := hk1_le_2pow
          _ ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) h2b)
      calc
        f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))
            ≤ (C2 * (((b : ℝ) ^ (k + 1)) ^ (d : ℕ))) / ((a : ℝ) ^ (k + 1)) := by
          refine (div_le_div_right (by positivity)).mpr h_fb
        _ = C2 * ((((b : ℝ) ^ (k + 1)) ^ (d : ℕ)) / ((a : ℝ) ^ (k + 1))) := by ring
        _ = C2 * 1 := by rw [h_ratio_one (k + 1)]
        _ = C2 := by simp
        _ ≤ C2' := hC2'_ge_C2
  -- O-bound: each term ≤ C2' → Σ ≤ C2'·i → Θ(i)
  have h_O : isBigO (fun i : ℕ => T (b ^ i)) (fun i : ℕ => (i : ℝ) * ((a : ℝ) ^ i)) := by
    refine Asymptotics.isBigO_of_le' atTop (fun i => ?_)
    have h_ratio_bound : T (b ^ i) / ((a : ℝ) ^ i) ≤ T (b ^ 0) + C2' * (i : ℝ) := by
      rw [h_formula a b f T h_rec ha_ne_zero i, div_one]
      calc
        T (b ^ 0) + (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)))
            ≤ T (b ^ 0) + (∑ _k in range i, C2') := by gcongr
        _ = T (b ^ 0) + C2' * (i : ℝ) := by simp
    calc
      T (b ^ i) = ((a : ℝ) ^ i) * (T (b ^ i) / ((a : ℝ) ^ i)) := by field_simp [ha_ne_zero]
      _ ≤ ((a : ℝ) ^ i) * (T (b ^ 0) + C2' * (i : ℝ)) := by gcongr
      _ ≤ (T (b ^ 0) + C2') * ((i : ℝ) * ((a : ℝ) ^ i)) := by ring; nlinarith
          have h_fb := hN2 (b ^ (k + 1)) (by
            have h2b : 2 ≤ b := by omega
            have hk1_le_2pow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := by
              induction' k with j IH; · norm_num; rw [Nat.pow_succ]; omega
            calc N ≤ N2 := le_max_right _ _; _ ≤ k := by omega; _ < k + 1 := by omega
              _ ≤ 2 ^ (k + 1) := hk1_le_2pow
              _ ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) h2b)
          calc
            f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))
                ≤ (C2 * (((b : ℝ) ^ (k + 1)) ^ (d : ℕ))) / ((a : ℝ) ^ (k + 1)) := by
              refine (div_le_div_right (by positivity)).mpr h_fb
            _ = C2 * ((((b : ℝ) ^ (k + 1)) ^ (d : ℕ)) / ((a : ℝ) ^ (k + 1))) := by ring
            _ = C2 * 1 := by rw [h_ratio_one (k + 1)]
            _ = C2 := by simp
      calc
        T (b ^ 0) + (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)))
            ≤ T (b ^ 0) + (∑ _k in range i, C2) := by gcongr
        _ = T (b ^ 0) + C2 * (i : ℝ) := by simp
    calc
      T (b ^ i) = ((a : ℝ) ^ i) * (T (b ^ i) / ((a : ℝ) ^ i)) := by field_simp [ha_ne_zero]
      _ ≤ ((a : ℝ) ^ i) * (T (b ^ 0) + C2 * (i : ℝ)) := by gcongr
      _ ≤ (T (b ^ 0) + C2) * ((i : ℝ) * ((a : ℝ) ^ i)) := by ring; nlinarith
  -- Ω-bound: each term ≥ C1 for k ≥ N, giving at least C1·(i-N) terms
  have h_Omega : isBigOmega (fun i : ℕ => T (b ^ i)) (fun i : ℕ => (i : ℝ) * ((a : ℝ) ^ i)) := by
    rw [isBigOmega_iff]
    let n₀ := max (2 * N) 1
    refine ⟨C1 / 2, by nlinarith, n₀, fun i hi => ?_⟩
    have hi_large : 2 * N ≤ i := by omega
    have hN_le_i : N ≤ i := by omega
    have h_term_lower : ∀ k, N ≤ k → C1 ≤ f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)) := by
      intro k hk
      have h_fb1 := hN1 (b ^ (k + 1)) (by
        -- same b^(k+1) ≥ N proof as before
        have h2b : 2 ≤ b := by omega
        have hk1_le_2pow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := by
          induction' k with j IH; · norm_num; rw [Nat.pow_succ]; omega
        calc N1 ≤ N := le_max_left _ _; _ ≤ k := hk; _ < k + 1 := by omega
          _ ≤ 2 ^ (k + 1) := hk1_le_2pow
          _ ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) h2b)
      calc
        C1 = C1 * ((((b : ℝ) ^ (k + 1)) ^ (d : ℕ)) / ((a : ℝ) ^ (k + 1))) := by rw [h_ratio_one (k + 1), mul_one]
        _ = (C1 * (((b : ℝ) ^ (k + 1)) ^ (d : ℕ))) / ((a : ℝ) ^ (k + 1)) := by ring
        _ ≤ f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)) := by refine (div_le_div_right (by positivity)).mpr h_fb1
    -- Now bound the sum
    rw [h_formula a b f T h_rec ha_ne_zero i, div_one]
    -- T(b⁰) + Σ ≥ Σ_{k=N}^{i-1} C1 = C1·(i-N) ≥ C1/2·i for i ≥ 2N
    have h_sum_ge : (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))) ≥ C1 * ((i : ℝ) - (N : ℝ)) := by
      rw [Finset.sum_range_add]
      -- First N terms ≥ 0, remaining i-N terms each ≥ C1
      have h_first : 0 ≤ (∑ k in range N, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))) :=
        Finset.sum_nonneg (fun k _ => div_nonneg (h_nonneg_f _) (by positivity))
      have h_second : (∑ k in range (i - N), f (b ^ ((k + N) + 1)) / ((a : ℝ) ^ ((k + N) + 1))) ≥
          C1 * ((i - N : ℕ) : ℝ) := by
        calc
          _ ≥ (∑ _k in range (i - N), C1) := Finset.sum_le_sum
            (fun k _ => h_term_lower (k + N) (by omega))
          _ = C1 * ((i - N : ℕ) : ℝ) := by simp
      have h_sum_eq : (i : ℝ) - (N : ℝ) = ((i - N : ℕ) : ℝ) := by push_cast; ring
      nlinarith
    calc
      (C1 / 2) * (i : ℝ) ≤ C1 * ((i : ℝ) - (N : ℝ)) := by nlinarith
      _ ≤ (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))) := h_sum_ge
      _ ≤ T (b ^ 0) + _ := by nlinarith
      _ = T (b ^ i) / ((a : ℝ) ^ i) := by
        rw [h_formula a b f T h_rec ha_ne_zero i, div_one]
    -- Multiply both sides by aⁱ:
    -- (C1/2)·i ≤ T(bⁱ)/aⁱ  →  (C1/2)·i·aⁱ ≤ T(bⁱ)
    -- Which gives the Ω bound
    nlinarith [pow_pos ha_pos i]
  exact ⟨h_O, h_Omega⟩

/-- **Case 3:** `b^d > a`.  The sum is dominated by the last term. -/
theorem master_case3 (a b d : ℕ) (ha : 1 ≤ a) (hb : 1 < b)
    (f T : ℕ → ℝ) (h_rec : ExactPowerRecurrence a b f T)
    (h_f_theta : isBigTheta f (fun n : ℕ => (n : ℝ) ^ (d : ℕ)))
    (h_nonneg_T : ∀ i, 0 ≤ T (b ^ i))
    (h_nonneg_f : ∀ n, 0 ≤ f n)
    (h_cond : a < (b : ℕ) ^ d) :
    isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => f (b ^ i)) := by
  have ha_pos : (a : ℝ) > 0 := by exact_mod_cast (by omega : 0 < a)
  have ha_ne_zero : (a : ℝ) ≠ 0 := by linarith
  let r := ((b : ℝ) ^ (d : ℕ)) / (a : ℝ)
  have hr_gt_one : 1 < r := by
    refine (one_lt_div ha_pos).mpr ?_
    exact mod_cast h_cond
  rcases h_f_theta with ⟨h_f_O, h_f_Omega⟩
  rcases h_f_O.exists_pos with ⟨C2, hC2_pos, hC2⟩
  rcases h_f_Omega.exists_pos with ⟨C1, hC1_pos, hC1⟩
  -- Ω-bound: T(bⁱ) = a·T(bⁱ⁻¹) + f(bⁱ) ≥ f(bⁱ) (since a·T ≥ 0)
  have h_Omega : isBigOmega (fun i : ℕ => T (b ^ i)) (fun i : ℕ => f (b ^ i)) := by
    rw [isBigOmega_iff]
    refine ⟨1, by norm_num, 1, fun i hi => ?_⟩
    rcases Nat.exists_eq_add_of_le hi with ⟨j, hj⟩; subst hj
    rw [h_rec.step j]; nlinarith
  -- O-bound: T(bⁱ) = O(f(bⁱ)).  Universal constant approach.
  -- Use C2' := max(C2, max_{k small} f(b^{k+1})/(a^{k+1}·r^{k+1})).
  -- Show T(bⁱ)/aⁱ ≤ h(0) + C2'·r^{i+1}/(r-1)  (geometric sum).
  -- Then T(bⁱ) ≤ aⁱ·(h(0) + term) ≤ aⁱ·rⁱ·K'  where K' = h(0) + C2'·r/(r-1).
  -- Since aⁱ·rⁱ ≤ f(bⁱ)/C1 (Θ lower bound for large i), done.
  have hC1_ev : ∀ᶠ (n : ℕ) in atTop, C1 * ((n : ℝ) ^ (d : ℕ)) ≤ f n := by
    filter_upwards [hC1] with n hn
    simpa [abs_of_nonneg (h_nonneg_f n), abs_pow, abs_of_nonneg (Nat.cast_nonneg n), mul_comm] using hn
  rw [Filter.eventually_atTop] at hC1_ev; rcases hC1_ev with ⟨N1, hN1⟩
  have hC2_ev : ∀ᶠ (n : ℕ) in atTop, f n ≤ C2 * ((n : ℝ) ^ (d : ℕ)) := by
    filter_upwards [hC2] with n hn
    simpa [abs_of_nonneg (h_nonneg_f n), abs_pow, abs_of_nonneg (Nat.cast_nonneg n)] using hn
  rw [Filter.eventually_atTop] at hC2_ev; rcases hC2_ev with ⟨N2, hN2⟩
  let N := max N1 N2
  let small_ratio_max := (range (max N 1)).sup' (by simp)
    (fun k => f (b ^ (k + 1)) / (((a : ℝ) ^ (k + 1)) * (r ^ (k + 1))))
  let C2' := max C2 small_ratio_max
  have hC2'_term : ∀ k, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)) ≤ C2' * (r ^ (k + 1)) := by
    intro k
    by_cases hk : k < N
    · have hk_sup : f (b ^ (k + 1)) / (((a : ℝ) ^ (k + 1)) * (r ^ (k + 1))) ≤ C2' :=
        le_trans (Finset.le_sup' _ (mem_range.2 hk)) (le_max_right _ _)
      have hr_pow_pos : 0 < r ^ (k + 1) := pow_pos (by linarith) _
      field_simp [hr_pow_pos.ne'] at hk_sup ⊢; nlinarith
    · have h_bpow_ge_N2 : N2 ≤ b ^ (k + 1) := by
        have h2b : 2 ≤ b := by omega
        have hk1_le_2pow : (k + 1 : ℕ) ≤ 2 ^ (k + 1) := by
          induction' k with j IH; · norm_num; rw [Nat.pow_succ]; omega
        calc N2 ≤ N := le_max_right _ _; _ ≤ k := by omega; _ < k + 1 := by omega
          _ ≤ 2 ^ (k + 1) := hk1_le_2pow
          _ ≤ b ^ (k + 1) := Nat.pow_le_pow_right (by omega) h2b
      have h_fb := hN2 (b ^ (k + 1)) h_bpow_ge_N2
      calc
        f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1))
            ≤ (C2 * (((b : ℝ) ^ (k + 1)) ^ (d : ℕ))) / ((a : ℝ) ^ (k + 1)) := by
          refine (div_le_div_right (by positivity)).mpr h_fb
        _ = C2 * ((((b : ℝ) ^ (d : ℕ)) / (a : ℝ)) ^ (k + 1)) := by
          simp [div_pow, mul_div_assoc, mul_comm, pow_mul]
        _ = C2 * (r ^ (k + 1)) := rfl
        _ ≤ C2' * (r ^ (k + 1)) := by gcongr; exact le_max_left _ _
  have h_f_lower : ∀ i, N ≤ i → C1 * (((a : ℝ) ^ i) * (r ^ i)) ≤ f (b ^ i) := by
    intro i hi
    have h_bpow_ge_N1 : N1 ≤ b ^ i := by
      have h2b : 2 ≤ b := by omega
      have hi_le_2pow : (i : ℕ) ≤ 2 ^ i := by
        induction' i with j IH; · norm_num; rw [Nat.pow_succ]; omega
      calc N1 ≤ N := le_max_left _ _; _ ≤ i := hi
        _ ≤ 2 ^ i := hi_le_2pow
        _ ≤ b ^ i := Nat.pow_le_pow_right (by omega) h2b
    have h_fb := hN1 (b ^ i) h_bpow_ge_N1
    calc
      C1 * (((a : ℝ) ^ i) * (r ^ i)) = C1 * ((a * r) ^ i) := by simp [mul_pow]
      _ = C1 * (((b : ℝ) ^ (d : ℕ)) ^ i) := by dsimp [r]; ring
      _ = C1 * (((b : ℝ) ^ i) ^ (d : ℕ)) := by simp [pow_mul]
      _ ≤ f (b ^ i) := h_fb
  have h_O : isBigO (fun i : ℕ => T (b ^ i)) (fun i : ℕ => f (b ^ i)) := by
    let K := (T (b ^ 0) + C2' * r / (r - 1)) / C1
    have hK : ∀ i, N ≤ i → T (b ^ i) ≤ K * f (b ^ i) := by
      intro i hi
      -- T(bⁱ)/aⁱ ≤ T(b⁰) + C2'·Σ_{k< i} r^{k+1} ≤ T(b⁰) + C2'·r^{i+1}/(r-1)
      have hT_div_a : T (b ^ i) / ((a : ℝ) ^ i) ≤ T (b ^ 0) + C2' * (r ^ (i + 1) / (r - 1)) := by
        rw [h_formula a b f T h_rec ha_ne_zero i, div_one]
        have h_sum_bound : (∑ k in range i, r ^ (k + 1)) ≤ r ^ (i + 1) / (r - 1) := by
          -- Σ_{k=0}^{i-1} r^{k+1} = r·(r^i-1)/(r-1) ≤ r^{i+1}/(r-1)
          calc
            (∑ k in range i, r ^ (k + 1)) = r * (∑ k in range i, r ^ k) := by
              simp [Finset.mul_sum, pow_succ]
            _ = r * ((r ^ i - 1) / (r - 1)) := by rw [geom_sum_eq (by linarith) i]
            _ = (r ^ (i + 1) - r) / (r - 1) := by ring
            _ ≤ r ^ (i + 1) / (r - 1) := by
              refine (div_le_div_right (by linarith [hr_gt_one])).mpr ?_
              nlinarith [pow_pos (by linarith) (i + 1)]
        calc
          T (b ^ 0) + (∑ k in range i, f (b ^ (k + 1)) / ((a : ℝ) ^ (k + 1)))
              ≤ T (b ^ 0) + (∑ k in range i, C2' * (r ^ (k + 1))) := by gcongr
          _ = T (b ^ 0) + C2' * (∑ k in range i, r ^ (k + 1)) := by simp [Finset.mul_sum]
          _ ≤ T (b ^ 0) + C2' * (r ^ (i + 1) / (r - 1)) := by gcongr
      -- Now: T(bⁱ) = aⁱ·(T(bⁱ)/aⁱ)
      -- ≤ aⁱ·(T(b⁰) + C2'·r^{i+1}/(r-1))
      -- = aⁱ·(T(b⁰) + C2'·r/(r-1)·rⁱ)
      -- ≤ aⁱ·rⁱ·(T(b⁰) + C2'·r/(r-1))  [since 1 ≤ rⁱ]
      -- ≤ f(bⁱ)·(T(b⁰) + C2'·r/(r-1))/C1  [by h_f_lower]
      -- = K·f(bⁱ)
      have h_x : ((a : ℝ) ^ i) * (T (b ^ i) / ((a : ℝ) ^ i)) = T (b ^ i) := by
        field_simp [ha_ne_zero]
      have hr_pow_ge_one : 1 ≤ r ^ i := by
        exact one_le_pow_of_one_le hr_gt_one.le i
      calc
        T (b ^ i) = ((a : ℝ) ^ i) * (T (b ^ i) / ((a : ℝ) ^ i)) := by field_simp [ha_ne_zero]
        _ ≤ ((a : ℝ) ^ i) * (T (b ^ 0) + C2' * (r ^ (i + 1) / (r - 1))) := by gcongr
        _ = ((a : ℝ) ^ i) * (r ^ i) * (T (b ^ 0) / (r ^ i) + C2' * r / (r - 1)) := by ring
        _ ≤ ((a : ℝ) ^ i) * (r ^ i) * (T (b ^ 0) + C2' * r / (r - 1)) := by
          gcongr; nlinarith [hr_pow_ge_one]
        _ ≤ (f (b ^ i) / C1) * (T (b ^ 0) + C2' * r / (r - 1)) := by
          gcongr; exact h_f_lower i hi
        _ = K * f (b ^ i) := by dsimp [K]; ring
    -- Bound holds EVENTUALLY (for i ≥ N).  That's all isBigO needs.
    refine Asymptotics.isBigO_of_le' atTop ?_
    refine Filter.eventually_atTop.mpr ⟨N, fun i hi => hK i hi⟩
  exact ⟨h_O, h_Omega⟩

/-- **Master Theorem (exact powers).**  Three mutually exclusive cases. -/
theorem master_theorem_exact_pow (a b d : ℕ) (ha : 1 ≤ a) (hb : 1 < b)
    (f T : ℕ → ℝ) (h_rec : ExactPowerRecurrence a b f T)
    (h_f_theta : isBigTheta f (fun n : ℕ => (n : ℝ) ^ (d : ℕ)))
    (h_nonneg_T : ∀ i, 0 ≤ T (b ^ i))
    (h_nonneg_f : ∀ n, 0 ≤ f n)
    (h_T0_pos : 0 < T (b ^ 0)) :
    (isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => ((a : ℝ) ^ i))) ∨
    (isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => (i : ℝ) * ((a : ℝ) ^ i))) ∨
    (isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => f (b ^ i))) := by
  by_cases h_lt : (b : ℕ) ^ d < a
  · exact Or.inl (master_case1 a b d ha hb f T h_rec h_f_theta h_nonneg_T h_nonneg_f h_T0_pos h_lt)
  · by_cases h_eq : (b : ℕ) ^ d = a
    · exact Or.inr (Or.inl (master_case2 a b d ha hb f T h_rec h_f_theta h_nonneg_T h_nonneg_f h_T0_pos h_eq))
    · have h_gt : a < (b : ℕ) ^ d := by omega
      exact Or.inr (Or.inr (master_case3 a b d ha hb f T h_rec h_f_theta h_nonneg_T h_nonneg_f h_gt))

end Chapter04
end CLRS
