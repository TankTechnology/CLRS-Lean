import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_06

/-! # Chapter 6 flagship trust surface -/

#check CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_log_cost
#check CLRS.Chapter06.buildMaxHeapLinearBound_isBigO_n
#check CLRS.Chapter06.heapSortNLogNBound_isBigO_nlogn

#assert_axioms CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_log_cost
#assert_axioms CLRS.Chapter06.buildMaxHeapLinearBound_isBigO_n
#assert_axioms CLRS.Chapter06.heapSortNLogNBound_isBigO_nlogn

example : CLRS.Chapter06.arrayHeapSortInPlace [4, 1, 3, 2] = [1, 2, 3, 4] := by
  decide
