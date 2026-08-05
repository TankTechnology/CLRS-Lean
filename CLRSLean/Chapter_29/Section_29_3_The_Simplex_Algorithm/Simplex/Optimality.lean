import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Step

/-!
# 29.3 Optimal exit from SIMPLEX

When every reduced cost is nonpositive, nonnegativity of the nonbasic
variables bounds every represented objective by the basic value {lit}`v`.
-/

namespace CLRS
namespace Chapter29

open scoped BigOperators

namespace Dictionary

/-- A globally optimal nonnegative assignment for the problem represented by
a dictionary. -/
def IsOptimalAssignment (D : Dictionary m n) (x : LPVar m n → ℝ) : Prop :=
  IsNonnegativeAssignment x ∧ D.Satisfies x ∧
    ∀ y, IsNonnegativeAssignment y → D.Satisfies y →
      D.objectiveRhs y ≤ D.objectiveRhs x

/-- The objective expression at a basic assignment is its constant term. -/
@[simp] theorem objectiveRhs_basicAssignment (D : Dictionary m n) :
    D.objectiveRhs D.basicAssignment = D.v := by
  simp [objectiveRhs]

/-- Nonpositive reduced costs bound every nonnegative assignment's objective
expression by the dictionary constant. -/
theorem objectiveRhs_le_v_of_reducedCosts_nonpos (D : Dictionary m n)
    (hc : ∀ j, D.c j ≤ 0) {x : LPVar m n → ℝ}
    (hx : IsNonnegativeAssignment x) :
    D.objectiveRhs x ≤ D.v := by
  have hsum : (∑ j, D.c j * x (D.nonbasicVar j)) ≤ ∑ _j : Fin n, (0 : ℝ) :=
    Finset.sum_le_sum fun j _ =>
      mul_nonpos_of_nonpos_of_nonneg (hc j) (hx (D.nonbasicVar j))
  simp only [Finset.sum_const_zero] at hsum
  rw [objectiveRhs]
  linarith

/-- The basic assignment is optimal when the dictionary is basic feasible and
all reduced costs are nonpositive. -/
theorem basicAssignment_optimal_of_reducedCosts_nonpos (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (hc : ∀ j, D.c j ≤ 0) :
    D.IsOptimalAssignment D.basicAssignment := by
  refine ⟨(D.basicAssignment_nonnegative_iff).2 hD,
    D.basicAssignment_satisfies, ?_⟩
  intro y hy _
  simpa using D.objectiveRhs_le_v_of_reducedCosts_nonpos hc hy

/-- Correctness of the optimal terminal branch returned by {lit}`simplexStep`. -/
theorem simplexStep_optimal_correct (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (hoptimal : D.simplexStep.IsOptimal) :
    D.IsOptimalAssignment D.basicAssignment :=
  D.basicAssignment_optimal_of_reducedCosts_nonpos hD
    ((D.simplexStep_optimal_iff).1 hoptimal)

end Dictionary
end Chapter29
end CLRS
