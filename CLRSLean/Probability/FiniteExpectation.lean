import Mathlib

/-!
# Finite Expectation Toolkit

A unified, reusable finite discrete expectation library for CLRS-Lean.
Sample spaces are `Finset.range n`; a `fintypeExpect` wrapper exists for
arbitrary `[Fintype Ω]`.

Main definitions:
- `expect`: `(∑ i < n, X i) / n`.
- `prob`: event probability.
- `indicator`: 0/1 indicator.
- `fintypeExpect`: generic Fintype wrapper.

Main theorems:
- `expect_add`, `expect_const`, `expect_nonneg`, `expect_sum`, `expect_indicator`
- `prob_singleton`, `prob_add_of_disjoint`
- `fintypeExpect_add`, `fintypeExpect_nonneg`, `fintypeExpect_const`,
  `fintypeExpect_indicator_singleton`, `fintypeExpect_sum`, `fintypeExpect_equiv`
- `expect_mul_of_indep`: expectation of a product of independent variables
- `fintypeExpect_fst`: marginalise out an unused independent coordinate
-/

namespace CLRS
namespace Probability

/-- 0/1 indicator. -/
def indicator (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- Uniform expectation over `Finset.range n`: `(∑ i<n, X i) / n`. -/
noncomputable def expect (n : ℕ) (X : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, X i) / (n : ℝ)

/-- Uniform probability over `Finset.range n`. -/
noncomputable def prob (n : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  expect n (fun i => indicator (P i))

theorem expect_add (n : ℕ) (X Y : ℕ → ℝ) :
    expect n (X + Y) = expect n X + expect n Y := by
  simp [expect, Finset.sum_add_distrib, add_div]

theorem expect_const (n : ℕ) (c : ℝ) (hn : n ≠ 0) :
    expect n (fun _ => c) = c := by
  simp [expect, hn]

theorem expect_nonneg (n : ℕ) (X : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) : 0 ≤ expect n X := by
  unfold expect
  apply div_nonneg (Finset.sum_nonneg (fun i _ => hX i))
  positivity

theorem expect_sum {ι : Type} (n : ℕ) (hn : n ≠ 0) (s : Finset ι) (X : ι → ℕ → ℝ) :
    expect n (fun i => ∑ k ∈ s, X k i) = ∑ k ∈ s, expect n (X k) := by
  unfold expect
  rw [Finset.sum_comm, Finset.sum_div]

theorem expect_indicator (n : ℕ) (hn : n ≠ 0) (P : ℕ → Prop) [DecidablePred P] :
    expect n (fun i => indicator (P i)) = prob n P := rfl

theorem prob_singleton (n j : ℕ) (hn : n ≠ 0) (hj : j ∈ Finset.range n) :
    prob n (fun i => i = j) = 1 / (n : ℝ) := by
  unfold prob expect indicator
  have hsum : (∑ i ∈ Finset.range n, (if i = j then (1 : ℝ) else 0)) = (1 : ℝ) := by
    simp [hj]
  rw [hsum]

theorem prob_add_of_disjoint (n : ℕ) (hn : n ≠ 0)
    {A B : ℕ → Prop} [DecidablePred A] [DecidablePred B]
    (hdisj : ∀ i, ¬ (A i ∧ B i)) :
    prob n (fun i => A i ∨ B i) = prob n A + prob n B := by
  unfold prob expect indicator
  have hsum : (∑ i ∈ Finset.range n, (if (A i ∨ B i) then (1 : ℝ) else 0)) =
      (∑ i ∈ Finset.range n, (if A i then 1 else 0)) +
      (∑ i ∈ Finset.range n, (if B i then 1 else 0)) := by
    calc
      (∑ i ∈ Finset.range n, (if (A i ∨ B i) then (1 : ℝ) else 0))
          = (∑ i ∈ Finset.range n, ((if A i then 1 else 0) + (if B i then 1 else 0))) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        by_cases hA : A i
        · have hB : ¬ B i := fun h => hdisj i ⟨hA, h⟩
          simp [hA, hB]
        · by_cases hB : B i
          · simp [hA, hB]
          · simp [hA, hB]
      _ = (∑ i ∈ Finset.range n, (if A i then 1 else 0)) +
          (∑ i ∈ Finset.range n, (if B i then 1 else 0)) := by
        rw [Finset.sum_add_distrib]
  rw [hsum]
  rw [add_div]

/-- Generic Fintype wrapper. -/
noncomputable def fintypeExpect {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ)

/-! ## Generic `fintypeExpect` algebra

These are the `[Fintype Ω]` analogues of the `expect` lemmas above.  They let
Chapter 8.4 (bucket sort) and Chapter 11.2 (chained hashing) reuse a single
finite-expectation API over `Fin m` instead of hand-rolling their own copies. -/

/-- `fintypeExpect` is additive. -/
theorem fintypeExpect_add {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X Y : Ω → ℝ) :
    fintypeExpect (fun ω => X ω + Y ω) = fintypeExpect X + fintypeExpect Y := by
  simp [fintypeExpect, Finset.sum_add_distrib, add_div]

/-- A `fintypeExpect` of nonnegative quantities is nonnegative. -/
theorem fintypeExpect_nonneg {Ω : Type} [Fintype Ω] [DecidableEq Ω] {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ fintypeExpect X := by
  unfold fintypeExpect
  exact div_nonneg (Finset.sum_nonneg fun ω _ => hX ω) (by positivity)

/-- The `fintypeExpect` of a constant over a nonempty space is that constant. -/
theorem fintypeExpect_const {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω ≠ 0) (c : ℝ) :
    fintypeExpect (fun _ : Ω => c) = c := by
  unfold fintypeExpect
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hΩ
  field_simp

/-- A singleton event has probability `1 / card Ω` under the uniform Fintype model. -/
theorem fintypeExpect_indicator_singleton {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (j : Ω) :
    fintypeExpect (fun ω => indicator (ω = j)) = 1 / (Fintype.card Ω : ℝ) := by
  unfold fintypeExpect indicator
  have hsum : (∑ ω : Ω, (if ω = j then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℝ))]
    simp
  rw [hsum]

/-- **Product expectation under independence.**

If `X` depends only on the first coordinate and `Y` only on the second of a
product sample space `Ω₁ × Ω₂`, then the expectation of the product factors as
the product of the expectations.  This is the finite-uniform form of
`E[XY] = E[X] · E[Y]` for independent `X`, `Y` (CLRS Appendix C, equation
(C.24)), and is the missing primitive for the bucket-sort second moment and the
SUHA chained-hash analysis. -/
theorem expect_mul_of_indep {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq Ω₁] [DecidableEq Ω₂] (X : Ω₁ → ℝ) (Y : Ω₂ → ℝ) :
    fintypeExpect (fun p : Ω₁ × Ω₂ => X p.1 * Y p.2) =
      fintypeExpect X * fintypeExpect Y := by
  unfold fintypeExpect
  have hnum : (∑ p : Ω₁ × Ω₂, X p.1 * Y p.2) =
      (∑ a : Ω₁, X a) * (∑ b : Ω₂, Y b) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [hnum, Fintype.card_prod]
  push_cast
  rw [div_mul_div_comm]

/-- `fintypeExpect` is invariant under reindexing the sample space by an
equivalence. -/
theorem fintypeExpect_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']
    [DecidableEq Ω] [DecidableEq Ω'] (e : Ω ≃ Ω') (X : Ω' → ℝ) :
    fintypeExpect (fun ω => X (e ω)) = fintypeExpect X := by
  unfold fintypeExpect
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e X

/-- Linearity of `fintypeExpect` over a finite sum of random variables. -/
theorem fintypeExpect_sum {Ω : Type} [Fintype Ω] [DecidableEq Ω] {ι : Type}
    (S : Finset ι) (f : ι → Ω → ℝ) :
    fintypeExpect (fun ω => ∑ s ∈ S, f s ω) = ∑ s ∈ S, fintypeExpect (f s) := by
  unfold fintypeExpect
  rw [Finset.sum_comm, Finset.sum_div]

/-- A random variable that only reads the first coordinate of a product sample
space has the same expectation as over that coordinate alone (the second factor
marginalises out).  This is the "drop an independent unused coordinate" step. -/
theorem fintypeExpect_fst {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Fintype Ω₂]
    [DecidableEq Ω₁] [DecidableEq Ω₂] (hΩ₂ : Fintype.card Ω₂ ≠ 0) (X : Ω₁ → ℝ) :
    fintypeExpect (fun p : Ω₁ × Ω₂ => X p.1) = fintypeExpect X := by
  have h := expect_mul_of_indep X (fun _ : Ω₂ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h, fintypeExpect_const hΩ₂, mul_one]

/-! ## Backward-compatible aliases -/

/-- Alias for `expect n` used by Chapter 5. -/
noncomputable def uniformAverage (n : ℕ) (X : ℕ → ℝ) : ℝ := expect n X

/-- Singleton indicator lemma used by Chapter 5. -/
theorem uniformAverage_indicator_singleton {m j : ℕ} (hj : j ∈ Finset.range m) :
    uniformAverage m (fun i => indicator (i = j)) = 1 / (m : ℝ) := by
  unfold uniformAverage
  have hm : m ≠ 0 := by
    intro h; rw [h] at hj; simp at hj
  rw [expect]
  -- Now goal: (∑ i ∈ range m, indicator (i = j)) / (m : ℝ) = 1 / (m : ℝ)
  -- Same as prob_singleton unfolded
  have h := prob_singleton m j hm hj
  unfold prob expect indicator at h
  -- h: (∑ i ∈ range m, (if i = j then 1 else 0)) / (m : ℝ) = 1 / (m : ℝ)
  simpa [indicator] using h

end Probability
end CLRS
