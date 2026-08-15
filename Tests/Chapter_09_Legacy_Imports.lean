import CLRSLean.Chapter_09.Section_09_1_Minimum_And_Maximum
import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select.Randomized_Select

/-!
# Chapter 9 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter09.minMax?_correct
#check CLRS.Chapter09.minMax?_comparisons_le
#check CLRS.Chapter09.randomizedSelectCostWithSchedule_rankCorrect
#check CLRS.Chapter09.randomizedSelectExpectedCost_linear_bound
#check CLRS.Chapter09.recursiveMedianOfMediansSelect?_correct
#check CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound
