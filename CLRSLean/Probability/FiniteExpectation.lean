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

/-! ## Fin-based API (used by Ch8, Ch11) -/

/-- Alias for `expect` with `Fin m` sample space. -/
noncomputable def uniformAverageFin {m : ℕ} (X : Fin m → ℝ) : ℝ :=
  fintypeExpect X

/-- Uniform average over two independent Fin choices. -/
noncomputable def uniformAverageFin2 {m : ℕ} (X : Fin m → Fin m → ℝ) : ℝ :=
  fintypeExpect (fun (p : Fin m × Fin m) => X p.1 p.2)

theorem uniformAverageFin_add {m : ℕ} (X Y : Fin m → ℝ) :
    uniformAverageFin (X + Y) = uniformAverageFin X + uniformAverageFin Y := by
  simp [uniformAverageFin, fintypeExpect, Finset.sum_add_distrib, add_div]

theorem uniformAverageFin_nonneg {m : ℕ} {X : Fin m → ℝ} (hX : ∀ i, 0 ≤ X i) :
    0 ≤ uniformAverageFin X := by
  unfold uniformAverageFin fintypeExpect
  apply div_nonneg (Finset.sum_nonneg (fun i _ => hX i))
  positivity

theorem uniformAverageFin_indicator_singleton {m : ℕ} (j : Fin m) :
    uniformAverageFin (fun i => indicator (i = j)) = 1 / (m : ℝ) := by
  unfold uniformAverageFin fintypeExpect indicator
  simp

theorem uniformAverageFin2_add {m : ℕ} (X Y : Fin m → Fin m → ℝ) :
    uniformAverageFin2 (X + Y) = uniformAverageFin2 X + uniformAverageFin2 Y := by
  simp [uniformAverageFin2, fintypeExpect, Finset.sum_add_distrib, add_div, Pi.add_apply]

/-! ## Independence: product expectation -/


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
