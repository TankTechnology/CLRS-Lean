import CLRSLean.Chapter_02.Section_02_1_Insertion_Sort
import CLRSLean.Chapter_02.Section_02_2_Analyzing_Algorithms
import CLRSLean.Chapter_02.Section_02_3_Designing_Algorithms
import CLRSLean.Chapter_02.Section_02_3_Designing_Algorithms.Merge_Sort_Recurrence

/-!
# Chapter 2 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter02.insertionSort_sorted
#check CLRS.Chapter02.insertionSort_perm
#check CLRS.Chapter02.insertionSortWorstComparisons_quadratic
#check CLRS.Chapter02.mergeSort_sortedLE
#check CLRS.Chapter02.mergeSort_perm
#check CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm
#check CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_on_exact_powers
#check CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_all_inputs
