import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi.Generalized

open CLRS.Chapter04

#check akraBazzi_integral_le_poly_of_lt
#check akraBazzi_upper_bound_nonneg
#check akraBazzi_lower_bound_of_lt
#check akraBazzi_lower_bound_zero
#check akraBazzi_bigTheta_nonneg

private theorem powerForcing_smooth {q : ℝ} (hq : 0 ≤ q) :
    PolynomialGrowth (fun n : ℕ => (n : ℝ) ^ q) q := by
  refine ⟨fun n => Real.rpow_nonneg (Nat.cast_nonneg n) q, ?_, 1, 1, by norm_num,
    by norm_num, ?_, ?_⟩
  · intro m n hmn
    exact Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hmn) hq
  · intro n hn
    simp
  · intro n hn
    simp

-- A decreasing power summand: the gap between the root and forcing is one half.
example : ∃ C : ℝ, 0 < C ∧ ∀ n,
    akraBazziIntegral 1 (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) n ≤
      C * (n : ℝ) ^ (1 / 2 : ℝ) := by
  convert akraBazzi_integral_le_poly_of_lt
    (p := 1) (powerForcing_smooth (q := 3 / 2) (by norm_num)) (by norm_num) using 1
  norm_num

-- The floor recurrence T(n) = 2 T(floor(n/2)) + n^(3/2) has the full integral bound.
example {T : ℕ → ℝ} {n₀ : ℕ}
    (hsat : SatisfiesAkraBazzi [(2, 2)] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) T n₀) :
    CLRS.Chapter03.isBigTheta T
      (akraBazziScale 1 (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ))) := by
  apply akraBazzi_bigTheta_nonneg (branches := [(2, 2)]) (q := 3 / 2) (n₀ := n₀)
  · norm_num [BranchesValid, BranchValid]
  · simp
  · norm_num [IsAkraBazziRoot, charFun, charTerm]
  · norm_num
  · norm_num
  · exact powerForcing_smooth (by norm_num)
  · exact hsat

-- The zero-root critical recurrence accumulates constant forcing along one branch.
example {T : ℕ → ℝ} {n₀ : ℕ}
    (hsat : SatisfiesAkraBazzi [(1, 2)] (fun _ => 1) T n₀) :
    CLRS.Chapter03.isBigTheta T (akraBazziScale 0 (fun _ => 1)) := by
  apply akraBazzi_bigTheta_nonneg (branches := [(1, 2)]) (q := 0) (n₀ := n₀)
  · norm_num [BranchesValid, BranchValid]
  · simp
  · norm_num [IsAkraBazziRoot, charFun, charTerm]
  · norm_num
  · norm_num
  · simpa using powerForcing_smooth (q := 0) (by norm_num)
  · exact hsat

-- Zero root and strictly larger forcing also fall within the same theorem.
example {T : ℕ → ℝ} {n₀ : ℕ}
    (hsat : SatisfiesAkraBazzi [(1, 3)] (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) T n₀) :
    CLRS.Chapter03.isBigTheta T
      (akraBazziScale 0 (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ))) := by
  apply akraBazzi_bigTheta_nonneg (branches := [(1, 3)]) (q := 1 / 2) (n₀ := n₀)
  · norm_num [BranchesValid, BranchValid]
  · simp
  · norm_num [IsAkraBazziRoot, charFun, charTerm]
  · norm_num
  · norm_num
  · exact powerForcing_smooth (by norm_num)
  · exact hsat

-- Compatibility: the positive-root upper theorem retains its former interface.
example {branches : List (ℕ × ℝ)} {g T : ℕ → ℝ} {n₀ : ℕ} {p q : ℝ}
    (hv : BranchesValid branches) (hne : branches ≠ [])
    (hr : IsAkraBazziRoot branches p) (hp : 0 < p) (hq : 0 ≤ q)
    (hg : PolynomialGrowth g q) (hs : SatisfiesAkraBazzi branches g T n₀) :
    CLRS.Chapter03.isBigO T (akraBazziScale p g) :=
  akraBazzi_upper_bound hv hne hr hp hq hg hs
