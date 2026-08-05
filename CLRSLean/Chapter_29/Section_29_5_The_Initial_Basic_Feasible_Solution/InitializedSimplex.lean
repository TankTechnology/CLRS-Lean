import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.PhaseTwoBridge

/-!
# 29.5 Full initialized SIMPLEX

The public solver combines the auxiliary phase-I feasibility test with the
restored-objective phase II.  Its result type exposes exactly the three CLRS
outcomes and carries a proof of each outcome.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- Certified outcomes of the complete two-phase SIMPLEX algorithm. -/
inductive InitializedSimplexResult (P : StandardLP m n) where
  | infeasible (notFeasible : ¬∃ x, P.IsFeasible x)
  | optimal (assignment : Fin n → ℝ) (isOptimal : P.IsOptimal assignment)
  | unbounded (isUnbounded : P.IsUnbounded)

/-- CLRS INITIALIZE-SIMPLEX followed by finite Bland-SIMPLEX. -/
noncomputable def initializedSimplex (P : StandardLP m n) :
    P.InitializedSimplexResult := by
  classical
  exact if hphaseOne : P.phaseOneTerminal.v = 0 then
    let hfeasible : ∃ x, P.IsFeasible x :=
      P.isFeasible_iff_phaseOneTerminal_v_eq_zero.mpr hphaseOne
    let D := P.phaseTwoStart
    let hD : D.IsBasicFeasible := P.phaseTwoStart_isBasicFeasible hfeasible
    match D.simplex hD with
    | .optimal z hz =>
        let hlockedDictionary :
            P.lockedAuxiliary.initialDictionary.IsOptimalAssignment z :=
          P.phaseTwoStart_equivalent_lockedAuxiliary.isOptimalAssignment hz
        let hlocked :
            P.lockedAuxiliary.IsOptimal (Dictionary.assignmentOriginal z) :=
          Dictionary.initialDictionary_optimal_to_standardLP
            P.lockedAuxiliary hlockedDictionary
        .optimal
          (auxiliaryTail (Dictionary.assignmentOriginal z))
          (P.lockedAuxiliary_optimal_to_original hlocked)
    | .unbounded h =>
        let hlockedDictionary :
            P.lockedAuxiliary.initialDictionary.IsUnbounded :=
          P.phaseTwoStart_equivalent_lockedAuxiliary.isUnbounded h
        let hlocked : P.lockedAuxiliary.IsUnbounded :=
          Dictionary.initialDictionary_unbounded_to_standardLP
            P.lockedAuxiliary hlockedDictionary
        .unbounded (P.lockedAuxiliary_unbounded_to_original hlocked)
  else
    .infeasible (by
      intro hfeasible
      exact hphaseOne
        (P.isFeasible_iff_phaseOneTerminal_v_eq_zero.mp hfeasible))

/-- The initialized solver always certifies infeasibility, returns an optimal
assignment, or proves the objective unbounded. -/
theorem initializedSimplex_complete (P : StandardLP m n) :
    (¬∃ x, P.IsFeasible x) ∨
      (∃ x, P.IsOptimal x) ∨ P.IsUnbounded := by
  cases P.initializedSimplex with
  | infeasible h => exact Or.inl h
  | optimal x hx => exact Or.inr (Or.inl ⟨x, hx⟩)
  | unbounded h => exact Or.inr (Or.inr h)

end StandardLP
end Chapter29
end CLRS
