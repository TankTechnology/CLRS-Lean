import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_03

/-! # Chapter 3 flagship trust surface -/

#check CLRS.Chapter03.isBigTheta_iff_sharedThreshold
#check CLRS.Chapter03.isBigTheta_log_factorial
#check CLRS.Chapter03.isLittleO_lgStar_log
#check CLRS.Chapter03.isBigTheta_iff_clrs
#check CLRS.Chapter03.polynomial_isBigTheta_degree
#check CLRS.Chapter03.complete_growth_hierarchy
#check CLRS.Chapter03.factorial_eq_stirling_mul_exp_robbinsAlpha
#check CLRS.Chapter03.robbinsAlpha_bounds

#assert_axioms CLRS.Chapter03.isBigTheta_iff_sharedThreshold
#assert_axioms CLRS.Chapter03.isBigTheta_log_factorial
#assert_axioms CLRS.Chapter03.isLittleO_lgStar_log
#assert_axioms CLRS.Chapter03.isBigTheta_iff_clrs
#assert_axioms CLRS.Chapter03.polynomial_isBigTheta_degree
#assert_axioms CLRS.Chapter03.complete_growth_hierarchy
#assert_axioms CLRS.Chapter03.factorial_eq_stirling_mul_exp_robbinsAlpha
#assert_axioms CLRS.Chapter03.robbinsAlpha_bounds
