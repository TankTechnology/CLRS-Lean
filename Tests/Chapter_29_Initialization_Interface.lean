import CLRSLean.Chapter_29

/-!
# Chapter 29 initialization interface test

Verifies the public phase-I and full initialized-SIMPLEX declarations from
Section 29.5 through the Chapter 29 guide.
-/

namespace CLRS
namespace Chapter29

#check StandardLP.auxiliary
#check StandardLP.auxiliaryArtificial
#check StandardLP.auxiliaryOriginal
#check StandardLP.auxiliaryAssignment
#check StandardLP.auxiliary_objective
#check StandardLP.auxiliary_feasible_lift_iff
#check StandardLP.auxiliaryTail
#check StandardLP.auxiliaryAssignment_parts
#check StandardLP.auxiliary_objective_eq_neg_artificial
#check StandardLP.auxiliary_objective_nonpositive_of_feasible
#check StandardLP.auxiliary_not_isUnbounded
#check StandardLP.auxiliary_feasible_of_artificial_eq_zero
#check StandardLP.MostNegativeRow
#check StandardLP.mostNegativeRow
#check StandardLP.auxiliaryPivotedDictionary
#check StandardLP.auxiliaryPivotedDictionary_isBasicFeasible
#check StandardLP.phaseOneStart
#check StandardLP.phaseOneStart_isBasicFeasible
#check StandardLP.phaseOneStart_equivalent_auxiliary
#check StandardLP.phaseOneFuel
#check StandardLP.phaseOneRun
#check StandardLP.phaseOneTerminal
#check StandardLP.phaseOneRun_isOptimal
#check StandardLP.phaseOneTerminal_equivalent_auxiliary
#check StandardLP.phaseOneTerminal_isBasicFeasible
#check StandardLP.phaseOneTerminal_reducedCostsNonpositive
#check StandardLP.phaseOneTerminal_v_nonpositive
#check StandardLP.isFeasible_iff_phaseOneTerminal_v_eq_zero
#check Dictionary.embedOldVar
#check Dictionary.dropAddedSlack
#check Dictionary.addedSlackVar
#check Dictionary.lockVariable
#check Dictionary.lockVariable_satisfies_iff
#check Dictionary.lockVariable_isBasicFeasible_of_value_eq_zero
#check Dictionary.Equivalent.lockVariable
#check Dictionary.withObjective
#check Dictionary.withObjective_satisfies_iff
#check Dictionary.withObjective_objectiveRhs
#check Dictionary.Equivalent.withObjective
#check StandardLP.objectiveWeight
#check StandardLP.initialDictionary_withObjective_eq
#check StandardLP.lockProgram
#check StandardLP.lockProgram_initialDictionary_eq
#check StandardLP.lockedAuxiliary
#check StandardLP.lockedAuxiliary_feasible_iff
#check StandardLP.phaseOneTerminal_artificial_eq_zero
#check StandardLP.phaseTwoStart
#check StandardLP.phaseTwoStart_isBasicFeasible
#check StandardLP.phaseTwoStart_equivalent_lockedAuxiliary
#check StandardLP.lockedAuxiliary_objective
#check StandardLP.lockedAuxiliary_optimal_to_original
#check StandardLP.lockedAuxiliary_unbounded_to_original
#check StandardLP.InitializedSimplexResult
#check StandardLP.initializedSimplex
#check StandardLP.initializedSimplex_complete

#print axioms StandardLP.initializedSimplex_complete

#print axioms StandardLP.phaseOneRun_isOptimal
#print axioms StandardLP.isFeasible_iff_phaseOneTerminal_v_eq_zero

end Chapter29
end CLRS
