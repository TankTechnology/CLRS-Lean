import CLRSLean.FourthEdition.Chapter_02

#check CLRS.Chapter02.mergeWithCost
#check CLRS.Chapter02.mergeWithCost_value
#check CLRS.Chapter02.merge_perm
#check CLRS.Chapter02.merge_sorted
#check CLRS.Chapter02.merge_comparisons_le
#check CLRS.Chapter02.merge_outputWrites_eq
#check CLRS.Chapter02.merge_correct

-- The top-level execution must recurse through the verified local MERGE,
-- rather than stop at the compatibility wrapper around `List.mergeSort`.
#check CLRS.Chapter02.MergeSortExecution
#check CLRS.Chapter02.mergeSortWithCost
#check CLRS.Chapter02.mergeSortWithCost_perm
#check CLRS.Chapter02.mergeSortWithCost_sorted
#check CLRS.Chapter02.mergeSortWithCost_eq_mergeSort
#check CLRS.Chapter02.mergeSortWithCost_work_eq_length
#check CLRS.Chapter02.mergeSortWithCost_comparisons_two_or_more
#check CLRS.Chapter02.mergeSortWithCost_outputWrites_two_or_more
#check CLRS.Chapter02.mergeSortWithCost_comparisons_le_work
#check CLRS.Chapter02.mergeSortWork_recurrence
#check CLRS.Chapter02.mergeSortWork_isBigTheta_nlogn

example : CLRS.Chapter02.merge [1, 4, 7] [2, 3, 9] = [1, 2, 3, 4, 7, 9] := by
  norm_num [CLRS.Chapter02.merge, CLRS.Chapter02.mergeWithCost]
