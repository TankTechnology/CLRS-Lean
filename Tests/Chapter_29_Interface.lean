import CLRSLean.Chapter_29

/-!
# Chapter 29 Interface Test

Verifies that the represented Chapter 29 standard/slack and weak-duality
declarations are available through the chapter guide.
-/

namespace CLRS
namespace Chapter29

#check IsNonnegative
#check StandardLP
#check StandardLP.IsFeasible
#check StandardLP.objective
#check StandardLP.slack
#check StandardLP.IsSlackExtension
#check StandardLP.slack_nonnegative_of_feasible
#check StandardLP.slack_equation
#check StandardLP.slackExtension_of_feasible
#check StandardLP.feasible_of_slackExtension
#check StandardLP.isFeasible_iff_exists_slackExtension
#check StandardLP.slackExtension_eq_slack
#check StandardLP.existsUnique_slackExtension_iff

example {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) :
    P.objective x = P.c ⬝ᵥ x := rfl

example {m n : ℕ} {P : StandardLP m n} {x : Fin n → ℝ} :
    P.IsFeasible x ↔ ∃! s, P.IsSlackExtension x s :=
  P.existsUnique_slackExtension_iff

#print axioms StandardLP.isFeasible_iff_exists_slackExtension
#print axioms StandardLP.existsUnique_slackExtension_iff

#check StandardLP.IsDualFeasible
#check StandardLP.dualObjective
#check StandardLP.IsDualFeasible.nonnegative
#check StandardLP.IsDualFeasible.coefficient_le

#check StandardLP.dotProduct_mono_right_of_nonnegative
#check StandardLP.dotProduct_mono_left_of_nonnegative
#check StandardLP.transpose_mulVec_dotProduct
#check StandardLP.weak_duality
#check StandardLP.IsOptimal
#check StandardLP.IsDualOptimal
#check StandardLP.IsUnbounded
#check StandardLP.primalSlack
#check StandardLP.dualSlack
#check StandardLP.ComplementarySlackness
#check StandardLP.dualityGap_eq_slackSums
#check StandardLP.complementarySlackness_iff_objective_eq
#check StandardLP.optimal_of_complementarySlackness
#check StandardLP.dualOptimal_of_complementarySlackness
#check Dictionary.objectiveCoeff_nonpos_of_reducedCosts
#check Dictionary.dualCertificate
#check Dictionary.dualCertificate_isDualFeasible
#check Dictionary.dualCertificate_objective_eq_v
#check Dictionary.assignmentOriginal
#check Dictionary.assignmentSlack
#check Dictionary.combinedAssignment_parts
#check Dictionary.original_feasible_of_initialDictionary
#check Dictionary.initialDictionary_objectiveRhs_eq_objective_original
#check Dictionary.initialDictionary_optimal_to_standardLP
#check Dictionary.initialDictionary_unbounded_to_standardLP
#check StandardLP.strongDuality_or_unbounded_of_initialDictionary_isBasicFeasible
#check StandardLP.strongDuality_of_initialDictionary_isBasicFeasible
#check StandardLP.not_isUnbounded_of_isDualFeasible
#check StandardLP.complementarySlackness_iff_optimal_of_initialDictionary_isBasicFeasible

example {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.objective x ≤ P.dualObjective y :=
  P.weak_duality hx hy

#print axioms StandardLP.weak_duality
#print axioms StandardLP.complementarySlackness_iff_objective_eq
#print axioms Dictionary.dualCertificate_isDualFeasible
#print axioms Dictionary.initialDictionary_optimal_to_standardLP
#print axioms StandardLP.strongDuality_or_unbounded_of_initialDictionary_isBasicFeasible
#print axioms StandardLP.complementarySlackness_iff_optimal_of_initialDictionary_isBasicFeasible

end Chapter29
end CLRS
