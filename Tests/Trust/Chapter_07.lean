import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_07

/-! # Chapter 7 flagship trust surface -/

#check CLRS.Chapter07.quickSort_correct
#check CLRS.Chapter07.sum_compared_prob_eq_expectedComparisons
#check CLRS.Chapter07.expectedRunningTime_isBigTheta_nlogn
#check CLRS.Chapter07.explicitRandomizedQuicksortExpectedComparisons_eq
#check CLRS.Chapter07.explicitRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn

#assert_axioms CLRS.Chapter07.quickSort_correct
#assert_axioms CLRS.Chapter07.sum_compared_prob_eq_expectedComparisons
#assert_axioms CLRS.Chapter07.expectedRunningTime_isBigTheta_nlogn
#assert_axioms CLRS.Chapter07.explicitRandomizedQuicksortExpectedComparisons_eq
#assert_axioms CLRS.Chapter07.explicitRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn

example : CLRS.Chapter07.quickSort [5, 2, 4, 1, 3] = [1, 2, 3, 4, 5] := by
  decide
