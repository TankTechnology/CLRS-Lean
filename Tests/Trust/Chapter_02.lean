import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_02

/-! # Chapter 2 flagship trust surface -/

#check CLRS.Chapter02.insertionSort_sorted
#check CLRS.Chapter02.mergeSort_perm
#check CLRS.Chapter02.merge_correct
#check CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_all_inputs

#assert_axioms CLRS.Chapter02.insertionSort_sorted
#assert_axioms CLRS.Chapter02.mergeSort_perm
#assert_axioms CLRS.Chapter02.merge_correct
#assert_axioms CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_all_inputs

example : CLRS.Chapter02.insertionSort [5, 2, 4, 1, 3] = [1, 2, 3, 4, 5] := by
  decide

example : CLRS.Chapter02.mergeSort [5, 2, 4, 1, 3] = [1, 2, 3, 4, 5] := by
  norm_num [CLRS.Chapter02.mergeSort, List.mergeSort]

example : CLRS.Chapter02.merge [1, 4, 7] [2, 3, 9] = [1, 2, 3, 4, 7, 9] := by
  norm_num [CLRS.Chapter02.merge, CLRS.Chapter02.mergeWithCost]
