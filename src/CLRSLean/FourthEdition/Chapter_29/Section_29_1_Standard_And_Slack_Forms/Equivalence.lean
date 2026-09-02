import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.SlackVariables

/-!
# 29.1 Standard/slack feasibility equivalence

This module proves the exact semantic bridge
{lit}`Ax ≤ b ↔ ∃ s ≥ 0, Ax + s = b` for nonnegative decision variables.
The slack vector is uniquely determined by the decision assignment.

Main results:

- {lit}`isFeasible_iff_exists_slackExtension`.
- {lit}`slackExtension_eq_slack`.
- {lit}`existsUnique_slackExtension_iff`.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- Eliminating nonnegative slack variables recovers primal feasibility. -/
theorem feasible_of_slackExtension {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} {s : Fin m → ℝ} (hxs : P.IsSlackExtension x s) :
    P.IsFeasible x := by
  refine ⟨hxs.1, ?_⟩
  intro i
  have hs : 0 ≤ s i := hxs.2.1 i
  have heq := hxs.2.2 i
  linarith

/-- Standard-form feasibility is equivalent to the existence of a nonnegative
slack vector satisfying the equality system. -/
theorem isFeasible_iff_exists_slackExtension {m n : ℕ}
    (P : StandardLP m n) {x : Fin n → ℝ} :
    P.IsFeasible x ↔ ∃ s, P.IsSlackExtension x s := by
  constructor
  · intro hx
    exact ⟨P.slack x, slackExtension_of_feasible hx⟩
  · rintro ⟨s, hxs⟩
    exact feasible_of_slackExtension hxs

/-- Every slack extension equals the canonical vector {lit}`b - Ax`. -/
theorem slackExtension_eq_slack {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} {s : Fin m → ℝ} (hxs : P.IsSlackExtension x s) :
    s = P.slack x := by
  funext i
  have heq := hxs.2.2 i
  simp only [slack]
  linarith

/-- A standard-form assignment is feasible exactly when it has a unique
nonnegative slack extension. -/
theorem existsUnique_slackExtension_iff {m n : ℕ}
    (P : StandardLP m n) {x : Fin n → ℝ} :
    P.IsFeasible x ↔ ∃! s, P.IsSlackExtension x s := by
  constructor
  · intro hx
    refine ⟨P.slack x, slackExtension_of_feasible hx, ?_⟩
    intro s hxs
    exact slackExtension_eq_slack hxs
  · rintro ⟨s, hxs, _⟩
    exact feasible_of_slackExtension hxs

end StandardLP
end Chapter29
end CLRS
