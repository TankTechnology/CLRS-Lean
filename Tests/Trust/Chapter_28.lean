import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_28

/-! # Chapter 28 flagship trust surface -/

#check CLRS.Chapter28.lupSolve_correct
#check CLRS.Chapter28.inv_eq_lup
#check CLRS.Chapter28.cholesky_decomposition

#assert_axioms CLRS.Chapter28.lupSolve_correct
#assert_axioms CLRS.Chapter28.inv_eq_lup
#assert_axioms CLRS.Chapter28.cholesky_decomposition

example : CLRS.Chapter28.substitutionCost 4 = 8 := by
  norm_num [CLRS.Chapter28.substitutionCost]
