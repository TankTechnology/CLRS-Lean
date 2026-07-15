import CLRSLean.Chapter_08

open CLRS Probability Chapter08

#check CLRS.Chapter08.textbookBucketSortCost
#check CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost
#check CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO

example : fintypeExpect (textbookBucketSortCost 1) = expectedBucketSortCost 1 := by
  exact fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost 1 (by omega)
