import CLRSLean.FourthEdition.Chapter_02

#check CLRS.Chapter02.mergeWithCost
#check CLRS.Chapter02.mergeWithCost_value
#check CLRS.Chapter02.merge_perm
#check CLRS.Chapter02.merge_sorted
#check CLRS.Chapter02.merge_comparisons_le
#check CLRS.Chapter02.merge_outputWrites_eq
#check CLRS.Chapter02.merge_correct

example : CLRS.Chapter02.merge [1, 4, 7] [2, 3, 9] = [1, 2, 3, 4, 7, 9] := by
  norm_num [CLRS.Chapter02.merge, CLRS.Chapter02.mergeWithCost]
