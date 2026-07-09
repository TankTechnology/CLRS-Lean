import Mathlib

/-!
# Finite Expectation Toolkit

Unified finite discrete expectation library mirroring the Ch5 `uniformAverageRange` pattern.

- {lit}`uniformAverage`: `(∑ i < n, X i) / n`.
- {lit}`indicator`: 0/1 indicator.
- {lit}`probabilityOf`: event probability via indicator.
-/

namespace CLRS
namespace Probability

/-- 0/1 indicator. -/
def indicator (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- Uniform average over first {lit}`n` natural numbers. -/
noncomputable def uniformAverage (n : ℕ) (X : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, X i) / (n : ℝ)

/-- Probability of a predicate under uniform distribution on {lit}`{0,…,n-1}`. -/
noncomputable def probabilityOf (n : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  uniformAverage n (fun i => indicator (P i))

theorem uniformAverage_add (n : ℕ) (X Y : ℕ → ℝ) :
    uniformAverage n (X + Y) = uniformAverage n X + uniformAverage n Y := by
  simp [uniformAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_nonneg (n : ℕ) (X : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) :
    0 ≤ uniformAverage n X := by
  unfold uniformAverage
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => hX i)
  · positivity

theorem indicator_singleton (n j : ℕ) (hj : j ∈ Finset.range n) :
    uniformAverage n (fun i => indicator (i = j)) = 1 / (n : ℝ) := by
  unfold uniformAverage indicator
  have hsum : (∑ i ∈ Finset.range n, (if i = j then (1 : ℝ) else 0)) = (1 : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [hbj]
    · intro hj_not; exact (hj_not hj).elim
  rw [hsum]

end Probability
end CLRS
