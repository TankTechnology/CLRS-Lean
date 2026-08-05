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

#print axioms StandardLP.phaseOneRun_isOptimal
#print axioms StandardLP.isFeasible_iff_phaseOneTerminal_v_eq_zero

end Chapter29
end CLRS
