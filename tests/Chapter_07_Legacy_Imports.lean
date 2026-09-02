import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort
import CLRSLean.Chapter_07.Section_07_2_Performance_Of_Quicksort
import CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort
import CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability
import CLRSLean.Chapter_07.Section_07_4_Analysis_Of_Quicksort

/-!
# Chapter 7 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter07.quickSort_correct
#check CLRS.Chapter07.quickSortComparisons_quadratic
#check CLRS.Chapter07.expectedComparisons_closed_form
#check CLRS.Chapter07.expectedComparisons_isBigTheta_nlogn
#check CLRS.Chapter07.expectedRunningTime_eq_sum_compared_prob
#check CLRS.Chapter07.expectedRunningTime_isBigTheta_nlogn
