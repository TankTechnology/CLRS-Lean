import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.InitialPivot

/-!
# 29.5 Phase I

Finite Bland-SIMPLEX optimizes the auxiliary program.  Its terminal value is
always nonpositive and equals zero exactly when the original program is
feasible, which is the textbook phase-I feasibility test.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- The finite basis bound used by phase I. -/
def phaseOneFuel (m n : ℕ) : ℕ :=
  Dictionary.basisCount m (n + 1)

/-- The internal phase-I SIMPLEX run. -/
noncomputable def phaseOneRun (P : StandardLP m n) :
    Dictionary.SimplexRunResult m (n + 1) :=
  P.phaseOneStart.simplexRun (phaseOneFuel m n)

/-- The terminal auxiliary dictionary produced by phase I. -/
noncomputable def phaseOneTerminal (P : StandardLP m n) :
    Dictionary m (n + 1) :=
  P.phaseOneRun.terminalDictionary

/-- The feasible phase-I start cannot represent an unbounded problem because
the auxiliary objective is bounded above by zero. -/
theorem phaseOneStart_not_isUnbounded (P : StandardLP m n) :
    ¬P.phaseOneStart.IsUnbounded := by
  intro hstart
  have hauxDictionary : P.auxiliary.initialDictionary.IsUnbounded :=
    P.phaseOneStart_equivalent_auxiliary.isUnbounded hstart
  have hauxiliary : P.auxiliary.IsUnbounded :=
    Dictionary.initialDictionary_unbounded_to_standardLP P.auxiliary
      hauxDictionary
  exact P.auxiliary_not_isUnbounded hauxiliary

/-- Phase I always reaches the optimal constructor: unboundedness and fuel
exhaustion are both impossible. -/
theorem phaseOneRun_isOptimal (P : StandardLP m n) :
    P.phaseOneRun.IsOptimal := by
  let D := P.phaseOneStart
  let fuel := phaseOneFuel m n
  change (D.simplexRun fuel).IsOptimal
  cases hrun : D.simplexRun fuel with
  | optimal terminal hc => trivial
  | unbounded terminal entering he ha =>
      have hresult : (D.simplexRun fuel).IsUnbounded := by
        rw [hrun]
        trivial
      have hunbounded : D.IsUnbounded :=
        D.simplexRun_unbounded_correct fuel
          P.phaseOneStart_isBasicFeasible hresult
      exact False.elim (P.phaseOneStart_not_isUnbounded hunbounded)
  | exhausted terminal =>
      have hresult : (D.simplexRun fuel).IsExhausted := by
        rw [hrun]
        trivial
      exact False.elim (D.simplexRun_basisCount_not_exhausted
        P.phaseOneStart_isBasicFeasible (by
          simpa [fuel, phaseOneFuel] using hresult))

/-- The terminal phase-I dictionary remains equivalent to the auxiliary
initial dictionary. -/
theorem phaseOneTerminal_equivalent_auxiliary (P : StandardLP m n) :
    P.auxiliary.initialDictionary.Equivalent P.phaseOneTerminal := by
  exact P.phaseOneStart_equivalent_auxiliary.trans (by
    simpa [phaseOneTerminal, phaseOneRun] using
      P.phaseOneStart.simplexRun_equivalent (phaseOneFuel m n))

/-- Phase I preserves basic feasibility. -/
theorem phaseOneTerminal_isBasicFeasible (P : StandardLP m n) :
    P.phaseOneTerminal.IsBasicFeasible := by
  simpa [phaseOneTerminal, phaseOneRun] using
    P.phaseOneStart.simplexRun_isBasicFeasible (phaseOneFuel m n)
      P.phaseOneStart_isBasicFeasible

/-- The phase-I terminal reduced costs are all nonpositive. -/
theorem phaseOneTerminal_reducedCostsNonpositive (P : StandardLP m n) :
    ∀ j, P.phaseOneTerminal.c j ≤ 0 := by
  have hoptimal := P.phaseOneRun_isOptimal
  cases hrun : P.phaseOneRun with
  | optimal terminal hc =>
      simpa [phaseOneTerminal, hrun,
        Dictionary.SimplexRunResult.terminalDictionary] using hc
  | unbounded terminal entering he ha =>
      simp [hrun, Dictionary.SimplexRunResult.IsOptimal] at hoptimal
  | exhausted terminal =>
      simp [hrun, Dictionary.SimplexRunResult.IsOptimal] at hoptimal

/-- The phase-I terminal basic assignment is globally optimal for the
auxiliary program. -/
theorem phaseOneTerminal_basicAssignment_isOptimal (P : StandardLP m n) :
    P.phaseOneTerminal.IsOptimalAssignment
      P.phaseOneTerminal.basicAssignment :=
  P.phaseOneTerminal.basicAssignment_optimal_of_reducedCosts_nonpos
    P.phaseOneTerminal_isBasicFeasible
    P.phaseOneTerminal_reducedCostsNonpositive

/-- The optimal auxiliary value never exceeds zero. -/
theorem phaseOneTerminal_v_nonpositive (P : StandardLP m n) :
    P.phaseOneTerminal.v ≤ 0 := by
  let T := P.phaseOneTerminal
  let z := Dictionary.assignmentOriginal T.basicAssignment
  have hEq : P.auxiliary.initialDictionary.Equivalent T :=
    P.phaseOneTerminal_equivalent_auxiliary
  have hsatInitial :
      P.auxiliary.initialDictionary.Satisfies T.basicAssignment :=
    (hEq.1 T.basicAssignment).2 T.basicAssignment_satisfies
  have hz : P.auxiliary.IsFeasible z :=
    Dictionary.original_feasible_of_initialDictionary P.auxiliary
      ((T.basicAssignment_nonnegative_iff).2
        P.phaseOneTerminal_isBasicFeasible)
      hsatInitial
  have hvalue : P.auxiliary.objective z = T.v := by
    calc
      P.auxiliary.objective z =
          P.auxiliary.initialDictionary.objectiveRhs T.basicAssignment :=
        (Dictionary.initialDictionary_objectiveRhs_eq_objective_original
          P.auxiliary T.basicAssignment).symm
      _ = T.objectiveRhs T.basicAssignment :=
        hEq.2 T.basicAssignment hsatInitial
      _ = T.v := T.objectiveRhs_basicAssignment
  rw [← hvalue]
  exact P.auxiliary_objective_nonpositive_of_feasible hz

/-- The textbook phase-I criterion: the original program is feasible exactly
when the optimized auxiliary objective is zero. -/
theorem isFeasible_iff_phaseOneTerminal_v_eq_zero (P : StandardLP m n) :
    (∃ x, P.IsFeasible x) ↔ P.phaseOneTerminal.v = 0 := by
  let T := P.phaseOneTerminal
  have hEq : P.auxiliary.initialDictionary.Equivalent T :=
    P.phaseOneTerminal_equivalent_auxiliary
  constructor
  · rintro ⟨x, hx⟩
    let u := auxiliaryAssignment 0 x
    let w := combinedAssignment u (P.auxiliary.slack u)
    have huext : P.auxiliary.IsSlackExtension u (P.auxiliary.slack u) :=
      P.auxiliary.slackExtension_of_feasible
        ((P.auxiliary_feasible_lift_iff x).2 hx)
    have hwnonnegative : Dictionary.IsNonnegativeAssignment w :=
      (combinedAssignment_nonnegative_iff u (P.auxiliary.slack u)).2
        ⟨huext.1, huext.2.1⟩
    have hwsatInitial : P.auxiliary.initialDictionary.Satisfies w :=
      P.auxiliary.initialDictionary_satisfies_of_slackExtension huext
    have hwsatT : T.Satisfies w := (hEq.1 w).1 hwsatInitial
    have hwvalue : T.objectiveRhs w = 0 := by
      calc
        T.objectiveRhs w =
            P.auxiliary.initialDictionary.objectiveRhs w :=
          (hEq.2 w hwsatInitial).symm
        _ = P.auxiliary.objective u :=
          P.auxiliary.initialDictionary_objectiveRhs u
            (P.auxiliary.slack u)
        _ = 0 := by simp [u]
    have hle := P.phaseOneTerminal_basicAssignment_isOptimal.2.2
      w hwnonnegative hwsatT
    rw [hwvalue, T.objectiveRhs_basicAssignment] at hle
    have hnonpos := P.phaseOneTerminal_v_nonpositive
    linarith
  · intro hv
    let z := Dictionary.assignmentOriginal T.basicAssignment
    have hsatInitial :
        P.auxiliary.initialDictionary.Satisfies T.basicAssignment :=
      (hEq.1 T.basicAssignment).2 T.basicAssignment_satisfies
    have hz : P.auxiliary.IsFeasible z :=
      Dictionary.original_feasible_of_initialDictionary P.auxiliary
        ((T.basicAssignment_nonnegative_iff).2
          P.phaseOneTerminal_isBasicFeasible)
        hsatInitial
    have hvalue : P.auxiliary.objective z = T.v := by
      calc
        P.auxiliary.objective z =
            P.auxiliary.initialDictionary.objectiveRhs T.basicAssignment :=
          (Dictionary.initialDictionary_objectiveRhs_eq_objective_original
            P.auxiliary T.basicAssignment).symm
        _ = T.objectiveRhs T.basicAssignment :=
          hEq.2 T.basicAssignment hsatInitial
        _ = T.v := T.objectiveRhs_basicAssignment
    have hartificial : z (auxiliaryArtificial n) = 0 := by
      have hobj := P.auxiliary_objective_eq_neg_artificial z
      linarith
    exact ⟨auxiliaryTail z,
      P.auxiliary_feasible_of_artificial_eq_zero hz hartificial⟩

end StandardLP
end Chapter29
end CLRS
