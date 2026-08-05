import CLRSLean.Chapter_29.Section_29_4_Duality.Definitions

/-!
# 29.4 Weak duality

This module proves CLRS Theorem 29.8.  For every primal-feasible {lit}`x` and
dual-feasible {lit}`y`, the primal objective is bounded by the dual objective:
{lit}`cᵀx ≤ bᵀy`.

The proof follows the CLRS calculation
{lit}`cᵀx ≤ (Aᵀy)ᵀx = yᵀAx ≤ yᵀb`.

Main result:

- {lit}`StandardLP.weak_duality`: CLRS Theorem 29.8.

Downstream layers:

- Later Section 29.4 modules prove strong duality (Theorem 29.9) and
  complementary slackness (Theorem 29.10).
-/

namespace CLRS
namespace Chapter29

open Matrix

namespace StandardLP

/-- Increasing the left factor of a dot product preserves order when the right
factor is coordinatewise nonnegative. -/
theorem dotProduct_mono_right_of_nonnegative {n : ℕ}
    {a b x : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) (hx : IsNonnegative x) :
    a ⬝ᵥ x ≤ b ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hab i) (hx i)

/-- Increasing the right factor of a dot product preserves order when the left
factor is coordinatewise nonnegative. -/
theorem dotProduct_mono_left_of_nonnegative {n : ℕ}
    {a b y : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) (hy : IsNonnegative y) :
    y ⬝ᵥ a ≤ y ⬝ᵥ b := by
  simp only [dotProduct]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hab i) (hy i)

/-- Moving a matrix transpose across a finite dot product exchanges the order
of summation: {lit}`(Aᵀy)ᵀx = yᵀ(Ax)`. -/
theorem transpose_mulVec_dotProduct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ) :
    (A.transpose *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **CLRS Theorem 29.8 (weak duality).** Every primal-feasible objective
value is at most every dual-feasible objective value. -/
theorem weak_duality {m n : ℕ} (P : StandardLP m n)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.objective x ≤ P.dualObjective y := by
  calc
    P.objective x = P.c ⬝ᵥ x := rfl
    _ ≤ (P.A.transpose *ᵥ y) ⬝ᵥ x :=
      dotProduct_mono_right_of_nonnegative hy.coefficient_le hx.1
    _ = y ⬝ᵥ (P.A *ᵥ x) := transpose_mulVec_dotProduct P.A y x
    _ ≤ y ⬝ᵥ P.b :=
      dotProduct_mono_left_of_nonnegative hx.2 hy.nonnegative
    _ = P.dualObjective y := by
      simp only [dualObjective, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring

end StandardLP
end Chapter29
end CLRS
