import CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.WeakDuality

/-!
# 29.3 Primal and dual optimality specifications

These predicates state the terminal contracts used by strong duality,
complementary slackness, and the full initialized SIMPLEX solver.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- A feasible primal assignment dominating every other feasible assignment. -/
def IsOptimal (P : StandardLP m n) (x : Fin n → ℝ) : Prop :=
  P.IsFeasible x ∧ ∀ z, P.IsFeasible z → P.objective z ≤ P.objective x

/-- A feasible dual assignment no worse than every other dual assignment. -/
def IsDualOptimal (P : StandardLP m n) (y : Fin m → ℝ) : Prop :=
  P.IsDualFeasible y ∧
    ∀ z, P.IsDualFeasible z → P.dualObjective y ≤ P.dualObjective z

/-- The primal objective exceeds every real bound on feasible assignments. -/
def IsUnbounded (P : StandardLP m n) : Prop :=
  ∀ M : ℝ, ∃ x, P.IsFeasible x ∧ M < P.objective x

end StandardLP
end Chapter29
end CLRS
