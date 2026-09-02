import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_32

/-! # Chapter 32 flagship trust surface -/

#check CLRS.Chapter32.rabinKarpRollingMatches_correct
#check CLRS.Chapter32.kmpTotalCost_le
#check CLRS.Chapter32.suffixArrayFast_work_isBigO_nlogn

#assert_axioms CLRS.Chapter32.rabinKarpRollingMatches_correct
#assert_axioms CLRS.Chapter32.kmpTotalCost_le
#assert_axioms CLRS.Chapter32.suffixArrayFast_work_isBigO_nlogn

example : CLRS.Chapter32.naiveMatcher ([0, 1, 0, 1] : List Nat) [0, 1] = [0, 2] := by
  decide
