import Mathlib

open scoped BigOperators

/-- For `2 ≤ x` and `0 < p`, the power drop from `x` to `⌊x⌋₊` is `O(x^(p-1))`. -/
lemma rpow_sub_floor_le_of_two_le {p : ℝ} (hp : 0 < p) {x : ℝ} (hx2 : 2 ≤ x) :
    x ^ p - (⌊x⌋₊ : ℝ) ^ p ≤ 2 * (1 + p) * x ^ (p - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx2
  by_cases hx_int : (⌊x⌋₊ : ℝ) = x
  · rw [hx_int]
    have hnonneg : 0 ≤ 2 * (1 + p) * x ^ (p - 1) := by positivity
    linarith
  · have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hfloor_ge : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one x
      linarith
    have hfloor_ge_half : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
      have h1 : x / 2 ≤ x - 1 := by linarith
      exact le_trans h1 hfloor_ge
    have hfloor_ge_one : 1 ≤ (⌊x⌋₊ : ℝ) := by
      have h1 : (1 : ℝ) ≤ x / 2 := by linarith
      exact le_trans h1 hfloor_ge_half
    have hlt : (⌊x⌋₊ : ℝ) < x := lt_of_le_of_ne hfloor_le hx_int
    have hmvt : ∃ c ∈ Set.Ioo (⌊x⌋₊ : ℝ) x,
        deriv (fun z : ℝ => z ^ p) c = (x ^ p - (⌊x⌋₊ : ℝ) ^ p) / (x - (⌊x⌋₊ : ℝ)) := by
      refine exists_deriv_eq_slope (fun z : ℝ => z ^ p) hlt ?_ ?_
      · exact (Real.continuous_rpow_const hp.le).continuousOn.mono (Set.subset_univ _)
      · intro z hz
        rw [Set.mem_Ioo] at hz
        have hz_pos : 0 < z := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
          (le_trans hfloor_ge_one (le_of_lt hz.1))
        exact (Real.differentiableAt_rpow_const_of_ne p (ne_of_gt hz_pos)).differentiableWithinAt
    rcases hmvt with ⟨c, hcIoo, hc⟩
    have hc_pos : 0 < c := by
      rw [Set.mem_Ioo] at hcIoo
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hfloor_ge_one (le_of_lt hcIoo.1))
    have hc_le_x : c ≤ x := by
      rw [Set.mem_Ioo] at hcIoo
      exact le_of_lt hcIoo.2
    have hc_ge_half : x / 2 ≤ c := by
      rw [Set.mem_Ioo] at hcIoo
      exact le_trans hfloor_ge_half (le_of_lt hcIoo.1)
    have hden_pos : 0 < x - (⌊x⌋₊ : ℝ) := sub_pos.mpr hlt
    have hden_le_one : x - (⌊x⌋₊ : ℝ) ≤ 1 := by
      have h := Nat.lt_floor_add_one x
      linarith
    have hmain : x ^ p - (⌊x⌋₊ : ℝ) ^ p = p * c ^ (p - 1) * (x - (⌊x⌋₊ : ℝ)) := by
      rw [Real.deriv_rpow_const] at hc
      rw [eq_div_iff (ne_of_gt hden_pos)] at hc
      exact hc.symm
    have hcp : c ^ (p - 1) ≤ 2 * x ^ (p - 1) := by
      by_cases hp1 : 1 ≤ p
      · have h : 0 ≤ p - 1 := sub_nonneg.mpr hp1
        calc c ^ (p - 1) ≤ x ^ (p - 1) := Real.rpow_le_rpow hc_pos.le hc_le_x h
          _ ≤ 2 * x ^ (p - 1) := by
            have hx_p1_nonneg : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hx0.le (p - 1)
            nlinarith
      · have hp_lt_one : p < 1 := lt_of_not_ge hp1
        have hneg : p - 1 < 0 := sub_neg.mpr hp_lt_one
        have hx_half_pos : 0 < x / 2 := by positivity
        have hhalf : (x / 2) ^ (p - 1) = (2 : ℝ) ^ (1 - p) * x ^ (p - 1) := by
          rw [Real.div_rpow hx0.le (by norm_num : 0 ≤ (2 : ℝ))]
          rw [div_eq_mul_inv]
          rw [← Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) (p - 1)]
          rw [show -(p - 1) = 1 - p by ring]
          ring
        calc c ^ (p - 1) ≤ (x / 2) ^ (p - 1) := Real.rpow_le_rpow_of_nonpos hx_half_pos hc_ge_half (le_of_lt hneg)
          _ = (2 : ℝ) ^ (1 - p) * x ^ (p - 1) := hhalf
          _ ≤ 2 * x ^ (p - 1) := by
            have h2 : (2 : ℝ) ^ (1 - p) ≤ 2 := by
              have hsub : 1 - p ≤ 1 := by nlinarith
              have hle : (2 : ℝ) ^ (1 - p) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hsub
              rw [Real.rpow_one] at hle
              exact hle
            exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le (p - 1))
    calc
      x ^ p - (⌊x⌋₊ : ℝ) ^ p = p * c ^ (p - 1) * (x - (⌊x⌋₊ : ℝ)) := hmain
      _ ≤ p * c ^ (p - 1) * 1 := by
        have hnonneg : 0 ≤ p * c ^ (p - 1) := mul_nonneg hp.le (Real.rpow_nonneg hc_pos.le (p - 1))
        exact mul_le_mul_of_nonneg_left hden_le_one hnonneg
      _ = p * c ^ (p - 1) := by ring
      _ ≤ p * (2 * x ^ (p - 1)) := mul_le_mul_of_nonneg_left hcp hp.le
      _ = 2 * p * x ^ (p - 1) := by ring
      _ ≤ 2 * (1 + p) * x ^ (p - 1) := by
        have hx_p1_nonneg : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hx0.le (p - 1)
        nlinarith

#check rpow_sub_floor_le_of_two_le
