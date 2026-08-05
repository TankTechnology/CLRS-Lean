import CLRSLean.Chapter_29.Section_29_4_Duality.StrongDuality

/-!
# 29.4 The complementary-slackness theorem

This closes the converse direction of the textbook theorem: for feasible
primal and dual assignments, simultaneous optimality is equivalent to the
complementary-slackness equations.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- Any dual-feasible assignment gives a finite upper bound on all primal
feasible objective values. -/
theorem not_isUnbounded_of_isDualFeasible (P : StandardLP m n)
    {y : Fin m → ℝ} (hy : P.IsDualFeasible y) : ¬P.IsUnbounded := by
  intro hunbounded
  obtain ⟨x, hx, hlarge⟩ := hunbounded (P.dualObjective y)
  have hweak := P.weak_duality hx hy
  linarith

/-- CLRS complementary-slackness theorem for an initially basic-feasible
program: feasible primal and dual assignments are both optimal exactly when
their complementary products vanish. -/
theorem complementarySlackness_iff_optimal_of_initialDictionary_isBasicFeasible
    (P : StandardLP m n) (hP : P.initialDictionary.IsBasicFeasible)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.ComplementarySlackness x y ↔
      P.IsOptimal x ∧ P.IsDualOptimal y := by
  constructor
  · intro hcs
    exact ⟨P.optimal_of_complementarySlackness hx hy hcs,
      P.dualOptimal_of_complementarySlackness hx hy hcs⟩
  · rintro ⟨hxoptimal, hyoptimal⟩
    obtain ⟨x₀, y₀, hx₀, hy₀, hvalue₀⟩ :=
      P.strongDuality_of_initialDictionary_isBasicFeasible hP
        (P.not_isUnbounded_of_isDualFeasible hy)
    have hprimal : P.objective x = P.objective x₀ :=
      le_antisymm (hx₀.2 x hx) (hxoptimal.2 x₀ hx₀.1)
    have hdual : P.dualObjective y = P.dualObjective y₀ :=
      le_antisymm (hyoptimal.2 y₀ hy₀.1) (hy₀.2 y hy)
    have hvalue : P.objective x = P.dualObjective y := by
      calc
        P.objective x = P.objective x₀ := hprimal
        _ = P.dualObjective y₀ := hvalue₀
        _ = P.dualObjective y := hdual.symm
    exact (P.complementarySlackness_iff_objective_eq hx hy).2 hvalue

end StandardLP
end Chapter29
end CLRS
