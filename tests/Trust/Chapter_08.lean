import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_08

/-! # Chapter 8 flagship trust surface -/

#check CLRS.Chapter08.comparisonSort_worstCase_lowerBound
#check CLRS.Chapter08.MutableOutput.countingSortArrayCost_bigO
#check CLRS.Chapter08.expectedBucketSortByRankCost_isBigO

#assert_axioms CLRS.Chapter08.comparisonSort_worstCase_lowerBound
#assert_axioms CLRS.Chapter08.MutableOutput.countingSortArrayCost_bigO
#assert_axioms CLRS.Chapter08.expectedBucketSortByRankCost_isBigO

example : CLRS.Chapter08.countingSortBy 5 id [5, 2, 4, 1, 3] = [1, 2, 3, 4, 5] := by
  decide
