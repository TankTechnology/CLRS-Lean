import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_03

/-! # Chapter 3 flagship trust surface -/

#check CLRS.Chapter03.isBigTheta_iff_sharedThreshold
#check CLRS.Chapter03.isBigTheta_log_factorial
#check CLRS.Chapter03.isLittleO_lgStar_log

#assert_axioms CLRS.Chapter03.isBigTheta_iff_sharedThreshold
#assert_axioms CLRS.Chapter03.isBigTheta_log_factorial
#assert_axioms CLRS.Chapter03.isLittleO_lgStar_log
