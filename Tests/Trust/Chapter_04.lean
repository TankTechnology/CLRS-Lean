import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_04

/-! # Chapter 4 flagship trust surface -/

#check CLRS.Chapter04.strassen_runtime_bigTheta
#check CLRS.Chapter04.continuous_master_case1
#check CLRS.Chapter04.akraBazzi_bigTheta

#assert_axioms CLRS.Chapter04.strassen_runtime_bigTheta
#assert_axioms CLRS.Chapter04.continuous_master_case1
#assert_axioms CLRS.Chapter04.akraBazzi_bigTheta
