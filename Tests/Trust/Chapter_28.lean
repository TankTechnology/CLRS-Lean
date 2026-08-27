import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_28

/-! # Chapter 28 flagship trust surface -/

#check CLRS.Chapter28.lupSolve_correct
#check CLRS.Chapter28.inv_eq_lup
#check CLRS.Chapter28.cholesky_decomposition
#check CLRS.Chapter28.lupDecomposeWithCost_correct
#check CLRS.Chapter28.lupDecomposeWithCost_eq_none_iff
#check CLRS.Chapter28.lupDecomposeWithCost_work_le
#check CLRS.Chapter28.permuteVector_eq_permMatrix_mulVec
#check CLRS.Chapter28.lupSolveWithCost_correct
#check CLRS.Chapter28.lupSolveWithCost_work_le

#assert_axioms CLRS.Chapter28.lupSolve_correct
#assert_axioms CLRS.Chapter28.inv_eq_lup
#assert_axioms CLRS.Chapter28.cholesky_decomposition
#assert_axioms CLRS.Chapter28.lupDecomposeWithCost_correct
#assert_axioms CLRS.Chapter28.lupDecomposeWithCost_eq_none_iff
#assert_axioms CLRS.Chapter28.lupDecomposeWithCost_work_le
#assert_axioms CLRS.Chapter28.permuteVector_eq_permMatrix_mulVec
#assert_axioms CLRS.Chapter28.lupSolveWithCost_correct
#assert_axioms CLRS.Chapter28.lupSolveWithCost_work_le

example : CLRS.Chapter28.substitutionCost 4 = 8 := by
  norm_num [CLRS.Chapter28.substitutionCost]
