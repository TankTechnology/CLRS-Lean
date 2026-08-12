import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions

/-!
# 29.1 Slack-variable construction

The canonical slack vector for an assignment {lit}`x` is {lit}`b - Ax`.
Primal feasibility makes this vector nonnegative and converts every row
inequality into an equality.

Main results:

- {lit}`slack_nonnegative_of_feasible`.
- {lit}`slack_equation`.
- {lit}`slackExtension_of_feasible`.
-/

namespace CLRS
namespace Chapter29

open Matrix

namespace StandardLP

/-- The canonical slack vector {lit}`b - Ax`. -/
def slack {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => P.b i - (P.A *ᵥ x) i

/-- A nonnegative slack extension satisfies {lit}`Ax + s = b` coordinatewise. -/
def IsSlackExtension {m n : ℕ} (P : StandardLP m n)
    (x : Fin n → ℝ) (s : Fin m → ℝ) : Prop :=
  IsNonnegative x ∧ IsNonnegative s ∧
    ∀ i, (P.A *ᵥ x) i + s i = P.b i

/-- A feasible assignment has a nonnegative canonical slack vector. -/
theorem slack_nonnegative_of_feasible {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} (hx : P.IsFeasible x) :
    IsNonnegative (P.slack x) := by
  intro i
  exact sub_nonneg.mpr (hx.2 i)

/-- The canonical slack vector satisfies {lit}`Ax + slack(x) = b`. -/
theorem slack_equation {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) :
    ∀ i, (P.A *ᵥ x) i + P.slack x i = P.b i := by
  intro i
  simp [slack]

/-- Every primal-feasible assignment extends canonically to a nonnegative
equality-form assignment. -/
theorem slackExtension_of_feasible {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} (hx : P.IsFeasible x) :
    P.IsSlackExtension x (P.slack x) := by
  exact ⟨hx.1, slack_nonnegative_of_feasible hx, P.slack_equation x⟩

end StandardLP
end Chapter29
end CLRS
