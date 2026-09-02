import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.RestoreObjective

/-!
# 29.5 The phase-II starting dictionary

This module locks the artificial variable at zero, restores the original
objective, and proves that the resulting basic-feasible dictionary represents
the locked auxiliary program used for phase II.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

namespace StandardLP

/-- Add the constraint {lit}`xₑ ≤ 0` as a new first row of a standard program. -/
def lockProgram (Q : StandardLP m n) (e : Fin n) : StandardLP (m + 1) n where
  A := Fin.cases (fun j => -(if j = e then (-1 : ℝ) else 0)) Q.A
  b := Fin.cases 0 Q.b
  c := Q.c

/-- Locking a variable in an initial dictionary is exactly the initial
dictionary of the row-extended program. -/
theorem lockProgram_initialDictionary_eq (Q : StandardLP m n) (e : Fin n) :
    (Q.lockProgram e).initialDictionary =
      Q.initialDictionary.lockVariable (.inl e) := by
  cases Q
  simp [lockProgram, initialDictionary, Dictionary.lockVariable,
    Dictionary.lockLabels, Dictionary.finAddOneEquiv,
    Dictionary.variableRowCoeff, Dictionary.basicAssignment]
  apply Equiv.ext
  intro s
  rcases s with i | j
  · refine Fin.cases ?_ (fun k => ?_) i <;>
      simp
  · simp

/-- The prepended lock row evaluates the selected variable. -/
theorem lockProgram_mulVec_zero (Q : StandardLP m n) (e : Fin n)
    (z : Fin n → ℝ) :
    ((Q.lockProgram e).A *ᵥ z) 0 = z e := by
  simp [Matrix.mulVec, dotProduct, lockProgram]

/-- Every old constraint row is preserved by the lock extension. -/
theorem lockProgram_mulVec_succ (Q : StandardLP m n) (e : Fin n)
    (z : Fin n → ℝ) (i : Fin m) :
    ((Q.lockProgram e).A *ᵥ z) i.succ = (Q.A *ᵥ z) i :=
  rfl

/-- The phase-II program: the old auxiliary constraints, {lit}`x₀ ≤ 0`, and
the original objective with zero weight on {lit}`x₀`. -/
def lockedAuxiliary (P : StandardLP m n) : StandardLP (m + 1) (n + 1) where
  A := (P.auxiliary.lockProgram (auxiliaryArtificial n)).A
  b := (P.auxiliary.lockProgram (auxiliaryArtificial n)).b
  c := Fin.cases 0 P.c

@[simp] theorem lockedAuxiliary_c_artificial (P : StandardLP m n) :
    P.lockedAuxiliary.c (auxiliaryArtificial n) = 0 :=
  rfl

@[simp] theorem lockedAuxiliary_c_original (P : StandardLP m n) (j : Fin n) :
    P.lockedAuxiliary.c (auxiliaryOriginal j) = P.c j :=
  rfl

@[simp] theorem lockedAuxiliary_mulVec_zero (P : StandardLP m n)
    (z : Fin (n + 1) → ℝ) :
    (P.lockedAuxiliary.A *ᵥ z) 0 = z (auxiliaryArtificial n) :=
  P.auxiliary.lockProgram_mulVec_zero (auxiliaryArtificial n) z

@[simp] theorem lockedAuxiliary_mulVec_succ (P : StandardLP m n)
    (z : Fin (n + 1) → ℝ) (i : Fin m) :
    (P.lockedAuxiliary.A *ᵥ z) i.succ = (P.auxiliary.A *ᵥ z) i :=
  rfl

@[simp] theorem lockedAuxiliary_b_zero (P : StandardLP m n) :
    P.lockedAuxiliary.b 0 = 0 :=
  rfl

@[simp] theorem lockedAuxiliary_b_succ (P : StandardLP m n) (i : Fin m) :
    P.lockedAuxiliary.b i.succ = P.b i :=
  rfl

/-- Locked feasibility is exactly original feasibility with artificial
coordinate zero. -/
theorem lockedAuxiliary_feasible_iff (P : StandardLP m n)
    (z : Fin (n + 1) → ℝ) :
    P.lockedAuxiliary.IsFeasible z ↔
      z (auxiliaryArtificial n) = 0 ∧ P.IsFeasible (auxiliaryTail z) := by
  constructor
  · intro hz
    have hnonnegative := hz.1 (auxiliaryArtificial n)
    have hlocked := hz.2 (0 : Fin (m + 1))
    have hartificial : z (auxiliaryArtificial n) = 0 := by
      have hnonpositive : z (auxiliaryArtificial n) ≤ 0 := by
        simpa using hlocked
      exact le_antisymm hnonpositive hnonnegative
    refine ⟨hartificial, ?_⟩
    apply P.auxiliary_feasible_of_artificial_eq_zero
      ⟨?_, ?_⟩ hartificial
    · exact hz.1
    · intro i
      have hi := hz.2 i.succ
      exact hi
  · rintro ⟨hartificial, hx⟩
    have haux : P.auxiliary.IsFeasible z := by
      rw [← auxiliaryAssignment_parts z, hartificial]
      exact (P.auxiliary_feasible_lift_iff (auxiliaryTail z)).2 hx
    refine ⟨haux.1, ?_⟩
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [hartificial]
    · exact haux.2 k

/-- The locked phase-II objective is exactly the original objective on the
tail variables. -/
theorem lockedAuxiliary_objective (P : StandardLP m n)
    (z : Fin (n + 1) → ℝ) :
    P.lockedAuxiliary.objective z = P.objective (auxiliaryTail z) := by
  simp [objective, dotProduct, lockedAuxiliary, auxiliaryTail,
    auxiliaryOriginal, Fin.sum_univ_succ]

/-- Original feasibility makes the artificial variable zero in the phase-I
terminal basic assignment. -/
theorem phaseOneTerminal_artificial_eq_zero (P : StandardLP m n)
    (hfeasible : ∃ x, P.IsFeasible x) :
    P.phaseOneTerminal.basicAssignment (.inl (auxiliaryArtificial n)) = 0 := by
  let T := P.phaseOneTerminal
  let z := Dictionary.assignmentOriginal T.basicAssignment
  have hEq : P.auxiliary.initialDictionary.Equivalent T :=
    P.phaseOneTerminal_equivalent_auxiliary
  have hsatInitial : P.auxiliary.initialDictionary.Satisfies T.basicAssignment :=
    (hEq.1 T.basicAssignment).2 T.basicAssignment_satisfies
  have hvalue : P.auxiliary.objective z = T.v := by
    calc
      P.auxiliary.objective z =
          P.auxiliary.initialDictionary.objectiveRhs T.basicAssignment :=
        (Dictionary.initialDictionary_objectiveRhs_eq_objective_original
          P.auxiliary T.basicAssignment).symm
      _ = T.objectiveRhs T.basicAssignment :=
        hEq.2 T.basicAssignment hsatInitial
      _ = T.v := T.objectiveRhs_basicAssignment
  have hv : T.v = 0 :=
    (P.isFeasible_iff_phaseOneTerminal_v_eq_zero).1 hfeasible
  have hobjective := P.auxiliary_objective_eq_neg_artificial z
  change z (auxiliaryArtificial n) = 0
  linarith

/-- Restore the original objective in the locked phase-I terminal
dictionary. -/
noncomputable def phaseTwoStart (P : StandardLP m n) :
    Dictionary (m + 1) (n + 1) :=
  (P.phaseOneTerminal.lockVariable (.inl (auxiliaryArtificial n))).withObjective
    P.lockedAuxiliary.objectiveWeight

/-- For a feasible original program, the phase-II starting dictionary is
basic feasible. -/
theorem phaseTwoStart_isBasicFeasible (P : StandardLP m n)
    (hfeasible : ∃ x, P.IsFeasible x) :
    P.phaseTwoStart.IsBasicFeasible := by
  apply Dictionary.lockVariable_isBasicFeasible_of_value_eq_zero
    P.phaseOneTerminal (.inl (auxiliaryArtificial n))
    P.phaseOneTerminal_isBasicFeasible
  exact P.phaseOneTerminal_artificial_eq_zero hfeasible

/-- The locked auxiliary initial dictionary and the phase-II start represent
the same equations and restored objective. -/
theorem phaseTwoStart_equivalent_lockedAuxiliary (P : StandardLP m n) :
    P.lockedAuxiliary.initialDictionary.Equivalent P.phaseTwoStart := by
  have hlocked :=
    P.phaseOneTerminal_equivalent_auxiliary.lockVariable
      (.inl (auxiliaryArtificial n))
  have hrestored := hlocked.withObjective P.lockedAuxiliary.objectiveWeight
  have hleft :
      (P.auxiliary.initialDictionary.lockVariable
          (.inl (auxiliaryArtificial n))).withObjective
          P.lockedAuxiliary.objectiveWeight =
        P.lockedAuxiliary.initialDictionary := by
    rw [← P.auxiliary.lockProgram_initialDictionary_eq
      (auxiliaryArtificial n)]
    cases P
    simp [lockedAuxiliary, lockProgram, objectiveWeight,
      Dictionary.withObjective, initialDictionary,
      Dictionary.basicVar, Dictionary.nonbasicVar]
  rw [hleft] at hrestored
  exact hrestored

end StandardLP
end Chapter29
end CLRS
