import CLRSLean.Chapter_08

open CLRS Probability Chapter08

#check CLRS.Chapter08.comparisonSort_worstCase_lowerBound
#check CLRS.Chapter08.height_le_logb_factorial
#check CLRS.Chapter08.factorial_le_leafCount_of_correctSort
#check CLRS.Chapter08.textbookBucketSortCost
#check CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost
#check CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO

example : fintypeExpect (textbookBucketSortCost 1) = expectedBucketSortCost 1 := by
  exact fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost 1 (by omega)
