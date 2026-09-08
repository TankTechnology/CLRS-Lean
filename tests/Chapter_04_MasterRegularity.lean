import CLRSLean.FourthEdition.Chapter_04.Section_04_5_Master_Theorem

open CLRS.Chapter04

#check exactPower_upper_of_eventual_regularity
#check normalized_tail_upper_of_eventual_regularity
#check master_case3_of_eventual_regularity

-- The upper bound is derived from forcing regularity, with no bound on T among
-- the hypotheses and with an arbitrary finite prefix before i₀.
example (a b : ℕ) (f T : ℕ → ℝ) (hrec : ExactPowerRecurrence a b f T)
    (i₀ : ℕ) (c : ℝ) (hc : c < 1) (hbase : 0 ≤ T 1)
    (hstart : 0 < f (b ^ i₀)) (hf : ∀ i, 0 ≤ f (b ^ i))
    (hreg : ∀ i, i₀ ≤ i → (a : ℝ) * f (b ^ i) ≤ c * f (b ^ (i + 1))) :
    CLRS.Chapter03.isBigTheta (fun i : ℕ => T (b ^ i)) (fun i : ℕ => f (b ^ i)) :=
  master_case3_of_eventual_regularity a b f T hrec i₀ hc hbase hstart hf hreg

-- Concrete case 3: T(n) = 2 n² - n satisfies T(2n) = 2 T(n) + (2n)².
-- Regularity holds with c = 1/2, so the theorem delivers Θ(n²) on powers of 2.
example : CLRS.Chapter03.isBigTheta
    (fun i : ℕ => 2 * ((2 ^ i : ℕ) : ℝ) ^ 2 - ((2 ^ i : ℕ) : ℝ))
    (fun i : ℕ => ((2 ^ i : ℕ) : ℝ) ^ 2) := by
  apply master_case3_of_eventual_regularity 2 2
    (fun n : ℕ => (n : ℝ) ^ 2) (fun n : ℕ => 2 * (n : ℝ) ^ 2 - n)
    (i₀ := 0) (c := 1 / 2)
  · constructor
    intro i
    push_cast
    simp only [pow_succ]
    ring
  · norm_num
  · norm_num
  · norm_num
  · intro i
    positivity
  · intro i _
    push_cast
    simp only [pow_succ]
    ring_nf
    rfl

-- The critical linear forcing does not satisfy the strict case-3 condition.
example (c : ℝ) (hc : c < 1) :
    ¬ (∀ i : ℕ, (2 : ℝ) * ((2 ^ i : ℕ) : ℝ) ≤
      c * ((2 ^ (i + 1) : ℕ) : ℝ)) := by
  intro h
  have hzero := h 0
  norm_num at hzero
  linarith

-- The derived bound has exactly the legacy tail-domination premise's type.
example (a b : ℕ) (f T : ℕ → ℝ) (hrec : ExactPowerRecurrence a b f T)
    (ha : 0 < (a : ℝ)) (i₀ : ℕ) (c : ℝ) (hc : c < 1)
    (hbase : 0 ≤ normalizedValue a b T 0)
    (hstart : 0 < f (b ^ i₀)) (hf : ∀ i, 0 ≤ f (b ^ i))
    (hreg : ∀ i, i₀ ≤ i → (a : ℝ) * f (b ^ i) ≤ c * f (b ^ (i + 1))) :
    CLRS.Chapter03.isBigTheta (fun i : ℕ => T (b ^ i))
      (fun i : ℕ =>
        (if i = 0 then 1 else normalizedForcing a b f (i - 1)) * ((a : ℝ) ^ i)) := by
  apply master_case3_tail_dominated a b f T hrec ha hbase
  · intro k
    exact div_nonneg (hf (k + 1)) (pow_nonneg ha.le _)
  · exact normalized_tail_upper_of_eventual_regularity a b f T hrec i₀ hc hstart
      (fun i _ => hf i) hreg
