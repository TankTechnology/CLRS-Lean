import CLRSLean.Chapter_29.Section_29_4_Duality.TerminalCertificate

/-!
# 29.4 Bridge from dictionary assignments to the primal program

The initial dictionary uses one stable assignment containing both original
and slack variables.  This module projects that assignment back to the
standard-form primal variables and transports optimality and unboundedness.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Original-variable coordinates of a complete dictionary assignment. -/
def assignmentOriginal (z : LPVar m n → ℝ) : Fin n → ℝ :=
  fun j => z (.inl j)

/-- Slack-variable coordinates of a complete dictionary assignment. -/
def assignmentSlack (z : LPVar m n → ℝ) : Fin m → ℝ :=
  fun i => z (.inr i)

@[simp] theorem assignmentOriginal_combinedAssignment
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    assignmentOriginal (StandardLP.combinedAssignment x s) = x := by
  funext j
  rfl

@[simp] theorem assignmentSlack_combinedAssignment
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    assignmentSlack (StandardLP.combinedAssignment x s) = s := by
  funext i
  rfl

/-- Splitting and recombining a stable assignment is the identity. -/
theorem combinedAssignment_parts (z : LPVar m n → ℝ) :
    StandardLP.combinedAssignment (assignmentOriginal z)
      (assignmentSlack z) = z := by
  funext q
  cases q <;> rfl

/-- A nonnegative assignment satisfying the initial dictionary projects to
a feasible assignment of the original standard-form program. -/
theorem original_feasible_of_initialDictionary (P : StandardLP m n)
    {z : LPVar m n → ℝ} (hznonneg : IsNonnegativeAssignment z)
    (hzsat : P.initialDictionary.Satisfies z) :
    P.IsFeasible (assignmentOriginal z) := by
  apply StandardLP.feasible_of_slackExtension
  refine ⟨fun j => hznonneg (.inl j), fun i => hznonneg (.inr i), ?_⟩
  apply (P.initialDictionary_satisfies_iff
    (assignmentOriginal z) (assignmentSlack z)).1
  rw [combinedAssignment_parts]
  exact hzsat

/-- On every complete assignment, the initial dictionary objective is the
standard-form objective of its original-variable projection. -/
theorem initialDictionary_objectiveRhs_eq_objective_original
    (P : StandardLP m n) (z : LPVar m n → ℝ) :
    P.initialDictionary.objectiveRhs z =
      P.objective (assignmentOriginal z) := by
  rw [← combinedAssignment_parts z]
  exact P.initialDictionary_objectiveRhs _ _

/-- Dictionary optimality for the initial representation yields primal
optimality for the original standard-form program. -/
theorem initialDictionary_optimal_to_standardLP (P : StandardLP m n)
    {z : LPVar m n → ℝ}
    (hz : P.initialDictionary.IsOptimalAssignment z) :
    P.IsOptimal (assignmentOriginal z) := by
  refine ⟨original_feasible_of_initialDictionary P hz.1 hz.2.1, ?_⟩
  intro x hx
  let w := StandardLP.combinedAssignment x (P.slack x)
  have hwext := P.slackExtension_of_feasible hx
  have hwnonneg : IsNonnegativeAssignment w :=
    (StandardLP.combinedAssignment_nonnegative_iff x (P.slack x)).2
      ⟨hwext.1, hwext.2.1⟩
  have hwsat : P.initialDictionary.Satisfies w :=
    P.initialDictionary_satisfies_of_slackExtension hwext
  have hle := hz.2.2 w hwnonneg hwsat
  calc
    P.objective x = P.initialDictionary.objectiveRhs w := by
      exact (P.initialDictionary_objectiveRhs x (P.slack x)).symm
    _ ≤ P.initialDictionary.objectiveRhs z := hle
    _ = P.objective (assignmentOriginal z) :=
      initialDictionary_objectiveRhs_eq_objective_original P z

/-- Dictionary unboundedness for the initial representation yields
unboundedness of the original standard-form program. -/
theorem initialDictionary_unbounded_to_standardLP (P : StandardLP m n)
    (h : P.initialDictionary.IsUnbounded) : P.IsUnbounded := by
  intro M
  obtain ⟨z, hznonneg, hzsat, hzobj⟩ := h M
  refine ⟨assignmentOriginal z,
    original_feasible_of_initialDictionary P hznonneg hzsat, ?_⟩
  rw [← initialDictionary_objectiveRhs_eq_objective_original P z]
  exact hzobj

end Dictionary
end Chapter29
end CLRS
