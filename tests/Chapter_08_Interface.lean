import CLRSLean.Chapter_08

open CLRS Probability Chapter08

#check CLRS.Chapter08.comparisonSort_worstCase_lowerBound
#check CLRS.Chapter08.height_le_logb_factorial
#check CLRS.Chapter08.factorial_le_leafCount_of_correctSort
#check CLRS.Chapter08.textbookBucketSortCost
#check CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost
#check CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO

-- §8.2 counting-sort linear work bound (already present)
#check CLRS.Chapter08.MutableOutput.countingSortArrayCost_bigO

-- §8.3 radix-sort cost layer
#check CLRS.Chapter08.radixSortByWithCost
#check CLRS.Chapter08.radixSortByWithCost_result
#check CLRS.Chapter08.radixSortByWithCost_cost_eq
#check CLRS.Chapter08.radixSortNatByCost
#check CLRS.Chapter08.radixSortNatBy_cost_eq
#check CLRS.Chapter08.radixSortNatByCost_bigO

-- §8.4 bucket-sort cost layer
#check CLRS.Chapter08.distributeBuckets
#check CLRS.Chapter08.distributeBuckets_size
#check CLRS.Chapter08.sortBucketByRankWithCost
#check CLRS.Chapter08.bucketSortByRankCost
#check CLRS.Chapter08.bucketSortByRankWithCost
#check CLRS.Chapter08.bucketSortByRankCost_eq_textbookBucketSortCost
#check CLRS.Chapter08.fintypeExpect_bucketSortByRankCost_eq_expectedBucketSortCost
#check CLRS.Chapter08.expectedBucketSortByRankCost_isBigO

example : fintypeExpect (textbookBucketSortCost 1) = expectedBucketSortCost 1 := by
  exact fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost 1 (by omega)

example : fintypeExpect (fun a : Fin 1 → Fin 1 =>
    (bucketSortByRankCost 1 (fun i : Fin 1 => (a i : Nat)) (List.finRange 1) : ℝ)) =
    expectedBucketSortCost 1 := by
  exact fintypeExpect_bucketSortByRankCost_eq_expectedBucketSortCost 1 (by omega)
