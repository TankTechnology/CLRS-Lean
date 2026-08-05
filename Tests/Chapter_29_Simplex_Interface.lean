import CLRSLean.Chapter_29

/-!
# Chapter 29 SIMPLEX Interface Test

Verifies the public dictionary and PIVOT declarations represented from
Section 29.3 through the Chapter 29 guide.
-/

namespace CLRS
namespace Chapter29

#check LPVar
#check Dictionary
#check Dictionary.basicVar
#check Dictionary.nonbasicVar
#check Dictionary.rowRhs
#check Dictionary.objectiveRhs
#check Dictionary.Satisfies
#check Dictionary.IsBasicFeasible
#check Dictionary.IsNonnegativeAssignment
#check Dictionary.basicAssignment
#check Dictionary.basicAssignment_basicVar
#check Dictionary.basicAssignment_nonbasicVar
#check Dictionary.basicAssignment_satisfies
#check Dictionary.basicAssignment_nonnegative_iff

example {m n : ℕ} (D : Dictionary m n) :
    D.Satisfies D.basicAssignment :=
  D.basicAssignment_satisfies

#check StandardLP.initialDictionary
#check StandardLP.combinedAssignment
#check StandardLP.combinedAssignment_nonnegative_iff
#check StandardLP.initialDictionary_satisfies_iff
#check StandardLP.initialDictionary_satisfies_of_slackExtension
#check StandardLP.initialDictionary_objectiveRhs
#check StandardLP.initialDictionary_isBasicFeasible_iff

#check Dictionary.pivotSwap
#check Dictionary.pivotRowB
#check Dictionary.pivotRowCoeff
#check Dictionary.pivot
#check Dictionary.pivot_basicVar_leaving
#check Dictionary.pivot_nonbasicVar_entering
#check Dictionary.pivot_basicVar_of_ne
#check Dictionary.pivot_nonbasicVar_of_ne
#check Dictionary.pivot_b_leaving
#check Dictionary.pivot_b_of_ne
#check Dictionary.pivot_a_leaving_entering
#check Dictionary.pivot_a_leaving_of_ne
#check Dictionary.pivot_a_of_ne_entering
#check Dictionary.pivot_a_of_ne
#check Dictionary.pivot_v_apply
#check Dictionary.pivot_c_entering
#check Dictionary.pivot_c_of_ne

noncomputable def pivotExample : Dictionary 1 1 where
  labels := Equiv.refl _
  b := fun _ => 6
  a := fun _ _ => 2
  v := 1
  c := fun _ => 3

example :
    let h : pivotExample.a 0 0 ≠ 0 := by norm_num [pivotExample]
    (pivotExample.pivot 0 0 h).b 0 = 3 ∧
      (pivotExample.pivot 0 0 h).v = 10 := by
  norm_num [pivotExample, Dictionary.pivot, Dictionary.pivotRowB]

#check Dictionary.pivot_satisfies_iff
#check Dictionary.pivot_objectiveRhs_eq
#check Dictionary.IsMinimumRatio
#check Dictionary.IsMinimumRatio.pivotCoefficient_pos
#check Dictionary.IsMinimumRatio.ratio_le
#check Dictionary.pivot_isBasicFeasible
#check Dictionary.pivot_v_eq
#check Dictionary.pivot_v_mono
#check Dictionary.pivot_v_strict
#check variableIndex
#check variableIndex_injective
#check Dictionary.basicVariableIndex
#check Dictionary.nonbasicVariableIndex
#check Dictionary.basicVariableIndex_injective
#check Dictionary.nonbasicVariableIndex_injective
#check Dictionary.enteringCandidates
#check Dictionary.IsBlandEntering
#check Dictionary.blandEntering?
#check Dictionary.blandEntering?_eq_none_iff
#check Dictionary.blandEntering?_spec
#check Dictionary.positiveRows
#check Dictionary.minimumRatioRows
#check Dictionary.exists_isMinimumRatio_of_exists_pos
#check Dictionary.IsBlandLeaving
#check Dictionary.blandLeaving?
#check Dictionary.blandLeaving?_eq_none_iff
#check Dictionary.blandLeaving?_spec
#check Dictionary.SimplexStepResult
#check Dictionary.SimplexStepResult.nextDictionary
#check Dictionary.simplexStep
#check Dictionary.simplexStep_optimal_iff
#check Dictionary.IsOptimalAssignment
#check Dictionary.objectiveRhs_basicAssignment
#check Dictionary.objectiveRhs_le_v_of_reducedCosts_nonpos
#check Dictionary.basicAssignment_optimal_of_reducedCosts_nonpos
#check Dictionary.simplexStep_optimal_correct
#check Dictionary.enteringRay
#check Dictionary.enteringRay_basicVar
#check Dictionary.enteringRay_nonbasicVar_same
#check Dictionary.enteringRay_nonbasicVar_of_ne
#check Dictionary.enteringRay_satisfies
#check Dictionary.enteringRay_nonnegative
#check Dictionary.enteringRay_objectiveRhs
#check Dictionary.IsUnbounded
#check Dictionary.unbounded_of_entering_column
#check Dictionary.SimplexStepResult.unboundedEntering
#check Dictionary.simplexStep_unbounded_correct
#check Dictionary.Equivalent
#check Dictionary.Equivalent.refl
#check Dictionary.Equivalent.symm
#check Dictionary.Equivalent.trans
#check Dictionary.pivot_equivalent
#check Dictionary.basicVariables
#check Dictionary.eq_basicAssignment_of_satisfies_of_nonbasic_zero
#check Dictionary.Equivalent.basicAssignment_eq_of_basicVariables_eq
#check Dictionary.Equivalent.v_eq_of_basicVariables_eq
#check Dictionary.Equivalent.isOptimalAssignment
#check Dictionary.Equivalent.isUnbounded
#check Dictionary.SimplexRunResult
#check Dictionary.SimplexRunResult.terminalDictionary
#check Dictionary.SimplexRunResult.IsOptimal
#check Dictionary.SimplexRunResult.IsUnbounded
#check Dictionary.SimplexRunResult.IsExhausted
#check Dictionary.simplexRun
#check Dictionary.simplexRun_equivalent
#check Dictionary.simplexRun_isBasicFeasible
#check Dictionary.simplexRun_v_mono
#check Dictionary.simplexRun_optimal_correct
#check Dictionary.simplexRun_unbounded_correct
#check Dictionary.IsBlandPivot
#check Dictionary.mem_basicVariables_pivot_iff
#check Dictionary.BlandPivot.equivalent
#check Dictionary.BlandPivot.isBasicFeasible
#check Dictionary.BlandPivot.v_mono
#check Dictionary.BlandPivot.basicAssignment_eq_of_v_eq
#check Dictionary.BlandReachable
#check Dictionary.BlandReachable.equivalent
#check Dictionary.BlandReachable.isBasicFeasible
#check Dictionary.BlandReachable.v_mono
#check Dictionary.BlandReachable.basicAssignment_eq_of_v_eq
#check Dictionary.BlandReachable.exists_entering_of_not_mem_mem
#check Dictionary.BlandReachable.exists_leaving_of_mem_not_mem
#check Dictionary.OnBlandPath
#check Dictionary.IsFickle
#check Dictionary.fickleVariables
#check Dictionary.fickleVariables_nonempty_of_cycle
#check Dictionary.greatestFickle
#check Dictionary.greatestFickle_mem
#check Dictionary.variableIndex_le_greatestFickle
#check Dictionary.objectiveCoeff
#check Dictionary.objectiveCoeff_basicVar
#check Dictionary.objectiveCoeff_nonbasicVar
#check Dictionary.objectiveRhs_eq_fullSum
#check Dictionary.objectiveRhs_enteringRay_as_coeff
#check Dictionary.Equivalent.entering_coefficient_identity
#check Dictionary.IsBlandEntering.objectiveCoeff_nonpos_of_index_lt
#check Dictionary.exists_negative_coefficient_product
#check Dictionary.bland_no_repeated_basis
#check Dictionary.bland_acyclic
#check Dictionary.simplexTrace
#check Dictionary.simplexTrace_isChain
#check Dictionary.simplexTrace_basis_nodup
#check Dictionary.basisCount
#check Dictionary.simplexTrace_length_le_basisCount
#check Dictionary.simplexRun_basisCount_not_exhausted
#check Dictionary.SimplexResult
#check Dictionary.simplex
#check Dictionary.simplex_optimal_or_unbounded

#print axioms Dictionary.bland_no_repeated_basis
#print axioms Dictionary.simplexRun_basisCount_not_exhausted
#print axioms Dictionary.simplex_optimal_or_unbounded

#print axioms Dictionary.simplexRun_equivalent
#print axioms Dictionary.simplexRun_isBasicFeasible
#print axioms Dictionary.simplexRun_optimal_correct
#print axioms Dictionary.simplexRun_unbounded_correct

example {m n : ℕ} (D : Dictionary m n) (x : LPVar m n → ℝ)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    D.Satisfies x ↔ (D.pivot l e h).Satisfies x :=
  D.pivot_satisfies_iff x l e h

#print axioms Dictionary.pivot_satisfies_iff
#print axioms Dictionary.pivot_objectiveRhs_eq
#print axioms Dictionary.pivot_isBasicFeasible
#print axioms Dictionary.pivot_v_mono
#print axioms Dictionary.pivot_v_strict
#print axioms Dictionary.basicAssignment_optimal_of_reducedCosts_nonpos
#print axioms Dictionary.simplexStep_optimal_correct
#print axioms Dictionary.unbounded_of_entering_column
#print axioms Dictionary.simplexStep_unbounded_correct
#print axioms Dictionary.pivot_equivalent
#print axioms Dictionary.Equivalent.basicAssignment_eq_of_basicVariables_eq
#print axioms Dictionary.Equivalent.isOptimalAssignment
#print axioms Dictionary.Equivalent.isUnbounded

end Chapter29
end CLRS
