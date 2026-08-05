import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.DualProjection
import CLRSLean.Chapter_29.Section_29_4_Duality.StrongDuality

/-!
# 29.4–29.5 General strong duality

Phase II supplies the equivalent basic-feasible dictionary required by the
finite-SIMPLEX strong-duality proof.  Projecting both primal and dual locked
coordinates yields the unrestricted textbook theorems for the original LP.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- Every feasible standard-form program is either unbounded or has primal
and dual optima with equal values. -/
theorem strongDuality_or_unbounded_of_feasible (P : StandardLP m n)
    (hfeasible : ∃ x, P.IsFeasible x) :
    P.IsUnbounded ∨
      ∃ x y, P.IsOptimal x ∧ P.IsDualOptimal y ∧
        P.objective x = P.dualObjective y := by
  have hlocked :=
    P.lockedAuxiliary.strongDuality_or_unbounded_of_equivalent_isBasicFeasible
      P.phaseTwoStart P.phaseTwoStart_equivalent_lockedAuxiliary
      (P.phaseTwoStart_isBasicFeasible hfeasible)
  rcases hlocked with hunbounded | ⟨z, y, hz, hy, hvalue⟩
  · exact Or.inl (P.lockedAuxiliary_unbounded_to_original hunbounded)
  · let x₀ := auxiliaryTail z
    let y₀ := lockedDualTail y
    have hx₀ : P.IsOptimal x₀ :=
      P.lockedAuxiliary_optimal_to_original hz
    have hy₀feasible : P.IsDualFeasible y₀ :=
      P.lockedAuxiliary_dualFeasible_to_original hy.1
    have hvalue₀ : P.objective x₀ = P.dualObjective y₀ := by
      calc
        P.objective x₀ = P.lockedAuxiliary.objective z :=
          (P.lockedAuxiliary_objective z).symm
        _ = P.lockedAuxiliary.dualObjective y := hvalue
        _ = P.dualObjective y₀ := P.lockedAuxiliary_dualObjective y
    have hy₀ : P.IsDualOptimal y₀ := by
      refine ⟨hy₀feasible, ?_⟩
      intro y' hy'
      calc
        P.dualObjective y₀ = P.objective x₀ := hvalue₀.symm
        _ ≤ P.dualObjective y' := P.weak_duality hx₀.1 hy'
    exact Or.inr ⟨x₀, y₀, hx₀, hy₀, hvalue₀⟩

/-- General strong duality: a feasible, bounded primal program has primal and
dual optima with equal objective values. -/
theorem strongDuality (P : StandardLP m n)
    (hfeasible : ∃ x, P.IsFeasible x) (hbounded : ¬P.IsUnbounded) :
    ∃ x y, P.IsOptimal x ∧ P.IsDualOptimal y ∧
      P.objective x = P.dualObjective y := by
  rcases P.strongDuality_or_unbounded_of_feasible hfeasible with
    hunbounded | hopt
  · exact False.elim (hbounded hunbounded)
  · exact hopt

/-- An attained primal optimum rules out primal unboundedness. -/
theorem not_isUnbounded_of_isOptimal (P : StandardLP m n)
    {x : Fin n → ℝ} (hx : P.IsOptimal x) : ¬P.IsUnbounded := by
  intro hunbounded
  obtain ⟨z, hz, hlarge⟩ := hunbounded (P.objective x)
  exact (not_lt_of_ge (hx.2 z hz)) hlarge

/-- Textbook strong-duality form for a given attained primal optimum. -/
theorem strongDuality_of_isOptimal (P : StandardLP m n)
    {x : Fin n → ℝ} (hx : P.IsOptimal x) :
    ∃ y, P.IsDualOptimal y ∧ P.objective x = P.dualObjective y := by
  obtain ⟨x₀, y, hx₀, hy, hvalue₀⟩ :=
    P.strongDuality ⟨x, hx.1⟩ (P.not_isUnbounded_of_isOptimal hx)
  have hprimal : P.objective x = P.objective x₀ :=
    le_antisymm (hx₀.2 x hx.1) (hx.2 x₀ hx₀.1)
  exact ⟨y, hy, hprimal.trans hvalue₀⟩

/-- CLRS complementary-slackness theorem without an initial-basis
hypothesis: feasible primal and dual assignments are simultaneously optimal
exactly when all complementary products vanish. -/
theorem complementarySlackness_iff_optimal (P : StandardLP m n)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.ComplementarySlackness x y ↔
      P.IsOptimal x ∧ P.IsDualOptimal y := by
  constructor
  · intro hcs
    exact ⟨P.optimal_of_complementarySlackness hx hy hcs,
      P.dualOptimal_of_complementarySlackness hx hy hcs⟩
  · rintro ⟨hxoptimal, hyoptimal⟩
    obtain ⟨y₀, hy₀, hvalue₀⟩ := P.strongDuality_of_isOptimal hxoptimal
    have hdual : P.dualObjective y = P.dualObjective y₀ :=
      le_antisymm (hyoptimal.2 y₀ hy₀.1) (hy₀.2 y hy)
    have hvalue : P.objective x = P.dualObjective y :=
      hvalue₀.trans hdual.symm
    exact (P.complementarySlackness_iff_objective_eq hx hy).2 hvalue

end StandardLP
end Chapter29
end CLRS
