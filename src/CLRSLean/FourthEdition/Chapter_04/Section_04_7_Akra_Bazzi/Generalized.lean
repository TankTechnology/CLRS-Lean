import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi

/-!
# Akra–Bazzi comparison for all nonnegative polynomial forcing exponents

The discrete power-sum estimate closes the forcing interval {lit}`p < q < p + 1`.
At characteristic root zero, induction on the integral itself handles the
zero input without requiring a positive power. The resulting theorem
{lit}`akraBazzi_bigTheta_nonneg` covers every {lit}`p, q ≥ 0` under
{lit}`PolynomialGrowth` and the floor recurrence {lit}`SatisfiesAkraBazzi`.

This retains the explicit monomial sandwich and monotonicity assumptions on
forcing. It does not assert the unrestricted perturbation theorem.
-/

open scoped BigOperators

namespace CLRS.Chapter04

/-- The positive power sum estimate, including decreasing summands. -/
lemma akraBazzi_sum_rpow_le {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (n : ℕ) :
    (∑ u ∈ Finset.range n, ((u + 1 : ℕ) : ℝ) ^ (d - 1)) ≤
      (1 + 1 / d) * (n : ℝ) ^ d := by
  cases n with
  | zero => simp [Real.zero_rpow hd.ne']
  | succ k =>
    have hant : AntitoneOn (fun x : ℝ => x ^ (d - 1)) (Set.Icc 1 (1 + (k : ℝ))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hsum := hant.sum_le_integral
    have hint : (∫ x : ℝ in 1..1 + (k : ℝ), x ^ (d - 1)) =
        (((k + 1 : ℕ) : ℝ) ^ d - 1) / d := by
      rw [integral_rpow (Or.inl (by linarith : -1 < d - 1))]
      simp only [sub_add_cancel, Real.one_rpow, Nat.cast_add, Nat.cast_one]
      rw [add_comm (1 : ℝ)]
    rw [hint] at hsum
    have hshift : (∑ u ∈ Finset.range (k + 1), ((u + 1 : ℕ) : ℝ) ^ (d - 1)) =
        1 + ∑ u ∈ Finset.range k, (1 + ((u + 1 : ℕ) : ℝ)) ^ (d - 1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, zero_add, Real.one_rpow]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      congr 1; ring
    rw [hshift]
    have hnp : 1 ≤ ((k + 1 : ℕ) : ℝ) ^ d :=
      Real.one_le_rpow (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) hd.le
    have hdiv : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
    calc
      1 + ∑ u ∈ Finset.range k, (1 + ((u + 1 : ℕ) : ℝ)) ^ (d - 1)
          ≤ 1 + ((((k + 1 : ℕ) : ℝ) ^ d - 1) / d) := add_le_add_right hsum 1
      _ ≤ (1 + 1 / d) * ((k + 1 : ℕ) : ℝ) ^ d := by
        rw [sub_div, div_eq_mul_inv, one_div]
        nlinarith

/-- The discrete integral has polynomial growth whenever the forcing exponent
strictly exceeds the characteristic exponent. -/
lemma akraBazzi_integral_le_poly_of_lt {p q : ℝ} {g : ℕ → ℝ}
    (hsmooth : PolynomialGrowth g q) (hpq : p < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n,
      akraBazziIntegral p g n ≤ C * (n : ℝ) ^ (q - p) := by
  by_cases hlarge : p + 1 ≤ q
  · exact akraBazzi_integral_le_poly hsmooth hlarge
  rcases hsmooth.2.2 with ⟨c, Cg, hc, hCg, hlower, hupper⟩
  have hd : 0 < q - p := sub_pos.mpr hpq
  refine ⟨Cg * (1 + 1 / (q - p)), by positivity, ?_⟩
  intro n
  calc
    akraBazziIntegral p g n
        ≤ ∑ u ∈ Finset.range n, Cg * ((u + 1 : ℕ) : ℝ) ^ (q - p - 1) := by
      apply Finset.sum_le_sum
      intro u hu
      have hu0 : 0 < ((u + 1 : ℕ) : ℝ) := by positivity
      calc
        g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1)
            ≤ (Cg * ((u + 1 : ℕ) : ℝ) ^ q) / ((u + 1 : ℕ) : ℝ) ^ (p + 1) :=
          div_le_div_of_nonneg_right (hupper _ (by omega)) (Real.rpow_nonneg hu0.le _)
        _ = Cg * ((u + 1 : ℕ) : ℝ) ^ (q - p - 1) := by
          rw [mul_div_assoc, ← Real.rpow_sub hu0]
          congr 2; ring
    _ = Cg * (∑ u ∈ Finset.range n, ((u + 1 : ℕ) : ℝ) ^ (q - p - 1)) :=
      (Finset.mul_sum ..).symm
    _ ≤ Cg * ((1 + 1 / (q - p)) * (n : ℝ) ^ (q - p)) :=
      mul_le_mul_of_nonneg_left (akraBazzi_sum_rpow_le hd (by linarith) n) hCg.le
    _ = _ := by ring

/-- Every strictly larger forcing exponent dominates the integral scale. -/
theorem akraBazzi_lower_bound_of_lt {branches : List (ℕ × ℝ)} {g T : ℕ → ℝ} {n₀ : ℕ} {p q : ℝ}
    (hvalid : BranchesValid branches) (_hnonempty : branches ≠ [])
    (_hroot : IsAkraBazziRoot branches p) (hp : 0 ≤ p) (hpq : p < q)
    (hsmooth : PolynomialGrowth g q) (hsat : SatisfiesAkraBazzi branches g T n₀) :
    Chapter03.isBigOmega T (akraBazziScale p g) := by
  have hgnonneg : ∀ n, 0 ≤ g n := hsmooth.1
  rcases hsmooth.2.2 with ⟨c₀, _C, hc₀pos, _hCpos, hglower, _hgupper⟩
  rcases akraBazzi_integral_le_poly_of_lt hsmooth hpq with ⟨Ci, _hCipos, hCi⟩
  have hT_nonneg : ∀ n, 0 ≤ T n := akraBazzi_T_nonneg hvalid hgnonneg hsat
  have hT_ge_g : ∀ n, n₀ < n → g n ≤ T n := akraBazzi_T_ge_g hvalid hgnonneg hsat
  let c : ℝ := c₀ / (1 + Ci)
  have hc_pos : 0 < c := div_pos hc₀pos (by positivity)
  rw [Chapter03.isBigOmega_iff]
  refine ⟨c, hc_pos, n₀ + 1, ?_⟩
  intro n hn
  have hn₀n : n₀ < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hg_lower : c₀ * (n : ℝ) ^ q ≤ g n := hglower n hn1
  have hF_le : akraBazziScale p g n ≤ (1 + Ci) * (n : ℝ) ^ q := by
    unfold akraBazziScale
    have hI : akraBazziIntegral p g n ≤ Ci * (n : ℝ) ^ (q - p) := hCi n
    have hnp : (n : ℝ) ^ p ≤ (n : ℝ) ^ q := by
      have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
      exact Real.rpow_le_rpow_of_exponent_le hn' (by linarith [hpq] : p ≤ q)
    calc
      (n : ℝ) ^ p * (1 + akraBazziIntegral p g n)
          ≤ (n : ℝ) ^ p * (1 + Ci * (n : ℝ) ^ (q - p)) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by positivity) p)
      _ = (n : ℝ) ^ p + Ci * ((n : ℝ) ^ p * (n : ℝ) ^ (q - p)) := by ring
      _ = (n : ℝ) ^ p + Ci * (n : ℝ) ^ q := by
            have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hn1)
            rw [show (n : ℝ) ^ p * (n : ℝ) ^ (q - p) = (n : ℝ) ^ q by
              rw [← Real.rpow_add hn_pos p (q - p)]
              congr 1; ring]
      _ ≤ (n : ℝ) ^ q + Ci * (n : ℝ) ^ q := by nlinarith [hnp]
      _ = (1 + Ci) * (n : ℝ) ^ q := by ring
  rw [abs_of_nonneg (akraBazziScale_nonneg hp hgnonneg n)]
  rw [abs_of_nonneg (hT_nonneg n)]
  calc
    c * akraBazziScale p g n ≤ c * ((1 + Ci) * (n : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_left hF_le hc_pos.le
    _ = c₀ * (n : ℝ) ^ q := by
          dsimp [c]
          field_simp [ne_of_gt (by positivity : 0 < 1 + Ci)]
    _ ≤ g n := hg_lower
    _ ≤ T n := hT_ge_g n hn₀n


/-- At root zero there is no power-rounding loss in the discrete integral. -/
lemma akraBazzi_integral_children_zero {branches : List (ℕ × ℝ)} {g : ℕ → ℝ}
    (hvalid : BranchesValid branches) (hroot : IsAkraBazziRoot branches 0) (n : ℕ) :
    (branches.map (fun ab => (ab.1 : ℝ) * akraBazziIntegral 0 g ⌊(n : ℝ) / ab.2⌋₊)).sum =
      akraBazziIntegral 0 g n -
        (branches.map (fun ab => akraBazziIncrement 0 g ab n)).sum := by
  have hcoeff : (branches.map (fun ab => (ab.1 : ℝ))).sum = 1 := by
    simpa [IsAkraBazziRoot, charFun, charTerm] using hroot
  have hd := akraBazzi_scale_decomp branches 0 g n hvalid hroot
  simp only [akraBazziScale, Real.rpow_zero, one_mul, mul_one, mul_add,
    List.sum_map_add] at hd
  rw [hcoeff] at hd
  linarith

/-- A zero characteristic exponent also admits the lower integral comparison.
The induction uses the integral alone because it vanishes at input zero. -/
theorem akraBazzi_lower_bound_zero {branches : List (ℕ × ℝ)} {g T : ℕ → ℝ}
    {n₀ : ℕ} {q : ℝ} (hvalid : BranchesValid branches) (hnonempty : branches ≠ [])
    (hroot : IsAkraBazziRoot branches 0) (hq : 0 ≤ q)
    (hsmooth : PolynomialGrowth g q) (hsat : SatisfiesAkraBazzi branches g T n₀) :
    Chapter03.isBigOmega T (akraBazziScale 0 g) := by
  have hgn := hsmooth.1
  have hTn := akraBazzi_T_nonneg hvalid hgn hsat
  rcases hsmooth.2.2 with ⟨c₀, C₀, hc₀, hC₀, hgl, hgu⟩
  rcases akraBazzi_increment_upper hvalid hnonempty (p := 0) (by norm_num) hgn
    hsmooth.2.1 with ⟨K, hK, N, hinc⟩
  let M : ℕ := max n₀ N + 1
  let A : ℝ := min 1 c₀
  have hA : 0 < A := lt_min (by norm_num) hc₀
  have hI : 0 ≤ akraBazziIntegral 0 g M := akraBazziIntegral_nonneg hgn M
  let c : ℝ := min (A / (akraBazziIntegral 0 g M + 1)) (1 / (K + 1))
  have hc : 0 < c := lt_min (div_pos hA (by positivity)) (by positivity)
  have hcA : c * (akraBazziIntegral 0 g M + 1) ≤ A := by
    exact (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hcK : c * K ≤ 1 := by
    have h : c * (K + 1) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  have hTpos : ∀ n, 1 ≤ n → A ≤ T n := by
    intro n hn
    by_cases hb : n ≤ n₀
    · rw [hsat.2.1 n hn hb]
      exact min_le_left _ _
    · have hforce := akraBazzi_T_ge_g hvalid hgn hsat n (by omega)
      have hpow : 1 ≤ (n : ℝ) ^ q := Real.one_le_rpow (by exact_mod_cast hn) hq
      have hlo := hgl n hn
      have hAc : A ≤ c₀ := min_le_right _ _
      nlinarith
  have hmain : ∀ n, c * akraBazziIntegral 0 g n ≤ T n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hz : n = 0
      · subst n
        simp [akraBazziIntegral, hsat.1]
      have hn : 1 ≤ n := by omega
      by_cases hsmall : n ≤ M
      · have hmono := akraBazziIntegral_mono hgn hsmall (p := 0)
        have hle := mul_le_mul_of_nonneg_left hmono hc.le
        have hpos := hTpos n hn
        nlinarith
      · have hchild : c * (branches.map (fun ab => (ab.1 : ℝ) *
            akraBazziIntegral 0 g ⌊(n : ℝ) / ab.2⌋₊)).sum ≤
          (branches.map (fun ab => (ab.1 : ℝ) * T ⌊(n : ℝ) / ab.2⌋₊)).sum := by
          rw [← List.sum_map_mul_left]
          apply List.sum_le_sum
          intro ab hab
          have hh := ih ⌊(n : ℝ) / ab.2⌋₊ (floor_div_lt_self (hvalid ab hab).2 (by omega))
          calc
            c * ((ab.1 : ℝ) * akraBazziIntegral 0 g ⌊(n : ℝ) / ab.2⌋₊) =
                (ab.1 : ℝ) * (c * akraBazziIntegral 0 g ⌊(n : ℝ) / ab.2⌋₊) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
        rw [akraBazzi_integral_children_zero hvalid hroot n] at hchild
        have hi := hinc n (show N ≤ n by dsimp [M] at hsmall; omega)
        have hice := mul_le_mul_of_nonneg_left hi hc.le
        have hgce := mul_le_mul_of_nonneg_right hcK (hgn n)
        rw [hsat.2.2 n (by dsimp [M] at hsmall; omega)]
        nlinarith
  rcases akraBazziIntegral_lower_const (p := 0) hsmooth with ⟨d, hd, hdI⟩
  rw [Chapter03.isBigOmega_iff]
  refine ⟨c * d / (d + 1), by positivity, 1, ?_⟩
  intro n hn
  rw [abs_of_nonneg (akraBazziScale_nonneg (by norm_num) hgn n),
    abs_of_nonneg (hTn n)]
  have hIn := hdI n hn
  have hcompare : d / (d + 1) * (1 + akraBazziIntegral 0 g n) ≤
      akraBazziIntegral 0 g n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hcompare hc.le
  simp only [akraBazziScale, Real.rpow_zero, one_mul]
  calc
    c * d / (d + 1) * (1 + akraBazziIntegral 0 g n) =
        c * (d / (d + 1) * (1 + akraBazziIntegral 0 g n)) := by ring
    _ ≤ c * akraBazziIntegral 0 g n := hm
    _ ≤ T n := hmain n

/-- All nonnegative polynomial forcing exponents satisfy the discrete
Akra–Bazzi comparison, including the zero characteristic root. -/
theorem akraBazzi_bigTheta_nonneg {branches : List (ℕ × ℝ)} {g T : ℕ → ℝ}
    {n₀ : ℕ} {p q : ℝ} (hvalid : BranchesValid branches) (hnonempty : branches ≠ [])
    (hroot : IsAkraBazziRoot branches p) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsmooth : PolynomialGrowth g q) (hsat : SatisfiesAkraBazzi branches g T n₀) :
    Chapter03.isBigTheta T (akraBazziScale p g) := by
  refine ⟨akraBazzi_upper_bound_nonneg hvalid hnonempty hroot hp hq hsmooth hsat, ?_⟩
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · subst p
    exact akraBazzi_lower_bound_zero hvalid hnonempty hroot hq hsmooth hsat
  rcases lt_trichotomy q p with hlt | heq | hgt
  · exact akraBazzi_lower_bound_leaf hvalid hnonempty hroot hp0 hlt hq hsmooth hsat
  · subst q
    exact akraBazzi_lower_bound_critical hvalid hnonempty hroot hp0 hsmooth hsat
  · exact akraBazzi_lower_bound_of_lt hvalid hnonempty hroot hp hgt hsmooth hsat

end CLRS.Chapter04
