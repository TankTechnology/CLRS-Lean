import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_09

/-! # Chapter 9 flagship trust surface -/

#check CLRS.Chapter09.minMax?_correct
#check CLRS.Chapter09.randomizedSelectExpectedCost_linear_bound
#check CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound

#assert_axioms CLRS.Chapter09.minMax?_correct
#assert_axioms CLRS.Chapter09.randomizedSelectExpectedCost_linear_bound
#assert_axioms CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound

example : CLRS.Chapter09.selectByRank? 2 [5, 2, 4, 1, 3] = some 3 := by
  norm_num [CLRS.Chapter09.selectByRank?, CLRS.Chapter09.sortedCopy, List.mergeSort]
