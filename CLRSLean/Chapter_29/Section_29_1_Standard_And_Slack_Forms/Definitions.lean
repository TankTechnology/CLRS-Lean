import Mathlib

/-!
# 29.1 Standard-form linear programs

This module defines the finite real matrix model used by Chapter 29.  A
standard-form program maximizes {lit}`cᵀx` subject to {lit}`Ax ≤ b` and
{lit}`0 ≤ x`.

Main declarations:

- {lit}`IsNonnegative`: pointwise nonnegativity of a finite vector.
- {lit}`StandardLP`: coefficients, bounds, and objective coefficients.
- {lit}`StandardLP.IsFeasible`: primal standard-form feasibility.
- {lit}`StandardLP.objective`: the value {lit}`cᵀx`.

Downstream layers:

- Slack-variable equivalence is proved in later Section 29.1 modules.
- Basic/nonbasic dictionaries and SIMPLEX are developed in Sections 29.3--29.5.
-/

namespace CLRS
namespace Chapter29

open Matrix

/-- A finite real vector is nonnegative when every coordinate is nonnegative. -/
def IsNonnegative {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j, 0 ≤ x j

/-- A maximization linear program in CLRS standard form:
maximize {lit}`cᵀx` subject to {lit}`Ax ≤ b` and {lit}`0 ≤ x`. -/
structure StandardLP (m n : ℕ) where
  /-- The constraint coefficient matrix. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The constraint right-hand side. -/
  b : Fin m → ℝ
  /-- The objective coefficient vector. -/
  c : Fin n → ℝ

namespace StandardLP

/-- A vector is primal feasible when it is nonnegative and satisfies every
row inequality of the standard-form program. -/
def IsFeasible {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) : Prop :=
  IsNonnegative x ∧ ∀ i, (P.A *ᵥ x) i ≤ P.b i

/-- The objective value {lit}`cᵀx` of a standard-form assignment. -/
def objective {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) : ℝ :=
  P.c ⬝ᵥ x

end StandardLP
end Chapter29
end CLRS
