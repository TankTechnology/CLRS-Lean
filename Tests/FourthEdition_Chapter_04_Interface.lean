import CLRSLean.FourthEdition.Chapter_04

/-!
# Fourth-edition Chapter 4 interface checks

These checks pin the public theorem interface of the native fourth-edition
sections §4.1 (multiplying square matrices), §4.6 (continuous master theorem),
and §4.7 (Akra–Bazzi recurrences).
-/

namespace CLRS
namespace Chapter04

-- §4.1 Multiplying square matrices
#check mul2
#check mul2_eq_mul
#check mulRec
#check mulRec_correct
#check mulRec_padOne
#check mulRec_padOne_corner
#check mulWork
#check mulWork_floorRec
#check mul_runtime_bigTheta
#check realLogScale_eight_two

-- §4.6 Continuous master theorem
#check geomSum
#check geomSum_nonneg
#check geomSum_le_of_lt_one
#check geomSum_eq_of_one
#check geomSum_bigTheta_of_gt_one
#check continuousWork
#check continuousRatio
#check continuousWork_nonneg
#check continuousWork_eq_geomSum
#check continuous_master_case1
#check continuous_master_case2
#check continuous_master_case3
#check continuous_case1_scale_eq_criticalPowerScale
#check continuous_case2_criticalPowerLogScale_eq

-- §4.7 Akra–Bazzi recurrences
#check AkraBazziBranch
#check AkraBazziRecurrence
#check charTerm
#check charFun
#check IsAkraBazziRoot
#check BranchValid
#check BranchesValid
#check rpow_realLogExponent
#check akraBazziRoot_single
#check akraBazziRoot_single_unique
#check akraBazziRoot_two_thirds_one
#check akraBazzi_single_branch_corollary
#check akraBazziRoot_unique
#check akraBazziRoot_nonneg
#check akraBazzi_root_scale_invariance
#check akraBazziIntegral
#check akraBazziScale
#check PolynomialGrowth
#check SatisfiesAkraBazzi
#check floor_div_lt_self
#check akraBazziIntegral_nonneg
#check akraBazziIntegral_mono
#check akraBazziIntegral_sub
#check akraBazziIntegral_lower_const
#check akraBazziScale_nonneg
#check akraBazziIntegral_bounded_of_lt
#check akraBazziIntegral_tail_lower
#check akraBazzi_increment_lower
#check akraBazziIncrement
#check akraBazziIntegral_tail_upper
#check akraBazzi_increment_upper_single
#check akraBazzi_increment_upper
#check akraBazzi_increment_lower_multi
#check akraBazzi_scale_ge_one
#check akraBazzi_scale_decomp
#check akraBazzi_T_nonneg
#check akraBazzi_T_ge_g
#check akraBazzi_integral_le_poly
#check akraBazzi_upper_bound
#check akraBazzi_lower_bound
#check akraBazzi_power_floor_loss
#check akraBazzi_scale_factor_le_linear
#check akraBazzi_scale_floor_decomp
#check akraBazzi_lower_bound_critical
#check akraBazzi_bigTheta
#check akraBazziSmoothingFn
#check akraBazzi_smoothing_gain_ge_loss
#check akraBazzi_smoothing_scale_floor_ge
#check akraBazzi_smoothing_scale_floor_ge_multi
#check akraBazzi_lower_bound_leaf
#check akraBazzi_bigTheta_leaf

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms mul_runtime_bigTheta
#print axioms continuous_master_case1
#print axioms continuous_master_case2
#print axioms continuous_master_case3
#print axioms akraBazziRoot_single
#print axioms akraBazziRoot_two_thirds_one
#print axioms akraBazziRoot_unique
#print axioms akraBazziRoot_nonneg
#print axioms akraBazzi_root_scale_invariance
#print axioms akraBazziIntegral_bounded_of_lt
#print axioms akraBazzi_increment_lower
#print axioms akraBazzi_increment_upper
#print axioms akraBazzi_increment_lower_multi
#print axioms akraBazzi_upper_bound
#print axioms akraBazzi_lower_bound
#print axioms akraBazzi_lower_bound_critical
#print axioms akraBazzi_bigTheta
#print axioms akraBazzi_lower_bound_leaf
#print axioms akraBazzi_bigTheta_leaf

end Chapter04
end CLRS
