import CLRSLean.FourthEdition.Chapter_35

/-! # Chapter 35 costed APPROX-SUBSET-SUM public interface -/

#check CLRS.ApproxSubsetSum.mergeWithCost_value
#check CLRS.ApproxSubsetSum.mergeWithCost_work_le
#check CLRS.ApproxSubsetSum.trimWithCost_value
#check CLRS.ApproxSubsetSum.trimWithCost_work_le
#check CLRS.ApproxSubsetSum.approxListsWithCost_value
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_value
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_work_le
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_fptas

open CLRS.ApproxSubsetSum

example : (mergeWithCost [1, 3, 5] [2, 4]).value = [1, 2, 3, 4, 5] := by
  native_decide

example : (mergeWithCost [1, 3, 5] [2, 4]).work = 4 := by
  native_decide

example : (filterAtMostWithCost 3 [0, 2, 5]).work = 3 := by
  native_decide
