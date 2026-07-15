import CLRSLean.Chapter_09

-- Section 9.1: simultaneous minimum and maximum.
#check CLRS.Chapter09.MinMaxResult
#check CLRS.Chapter09.MinMaxCertificate
#check CLRS.Chapter09.minMax?
#check CLRS.Chapter09.minMax?_isSome_iff
#check CLRS.Chapter09.minMax?_correct
#check CLRS.Chapter09.minMax?_minimum_mem
#check CLRS.Chapter09.minMax?_maximum_mem
#check CLRS.Chapter09.minMax?_minimum_le
#check CLRS.Chapter09.minMax?_le_maximum
#check CLRS.Chapter09.minMax?_comparisons_le

-- Section 9.2: selection in expected linear time.
#check CLRS.Chapter09.selectByRank?_correct
#check CLRS.Chapter09.quickSelect?_correct
#check CLRS.Chapter09.randomizedSelectMajorizer_bigO_linear

-- Section 9.3: selection in worst-case linear time.
#check CLRS.Chapter09.PivotTotal
#check CLRS.Chapter09.selectWithPivot?_isSome_of_lt
#check CLRS.Chapter09.medianOfMediansPivot?_isSome_of_ne_nil
#check CLRS.Chapter09.medianOfMediansSelect?_isSome_of_lt
#check CLRS.Chapter09.medianOfMediansSelect?_correct
#check CLRS.Chapter09.medianOfMediansPartitionPathCost_linear_bound

-- Recursive median-of-medians implementation layer.
#check CLRS.Chapter09.recursiveMedianOfMediansPivot?
#check CLRS.Chapter09.recursiveMedianOfMediansPivot?_mem
#check CLRS.Chapter09.recursiveMedianOfMediansPivot?_isSome_of_ne_nil
#check CLRS.Chapter09.recursiveMedianOfMediansPivot?_partition_size_bound
#check CLRS.Chapter09.recursiveMedianOfMediansSelect?
#check CLRS.Chapter09.recursiveMedianOfMediansSelect?_isSome_of_lt
#check CLRS.Chapter09.recursiveMedianOfMediansSelect?_correct
#check CLRS.Chapter09.recursiveMedianOfMediansPartitionPathCost_linear_bound
#check CLRS.Chapter09.recursiveMedianOfMediansComparisonCost
#check CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound

-- Fresh uniform pivot choice at every recursive RANDOMIZED-SELECT call.
#check CLRS.Chapter09.freshRandomizedSelectWithRanks?
#check CLRS.Chapter09.freshRandomizedSelectWithRanks?_correct
#check CLRS.Chapter09.freshRandomizedSelectContinuationSize_le_subproblemSize
#check CLRS.Chapter09.freshRandomizedSelectExpectedComparisons
#check CLRS.Chapter09.freshRandomizedSelectExpectedComparisons_linear_bound

-- Fresh schedule execution and its state-dependent nested expected cost.
#check CLRS.Chapter09.randomizedSelectCostWithSchedule
#check CLRS.Chapter09.randomizedSelectExpectedCostFuel
#check CLRS.Chapter09.randomizedSelectExpectedCostFuel_succ
#check CLRS.Chapter09.randomizedSelectExpectedCost
#check CLRS.Chapter09.randomizedSelectExpectedCost_nonneg
#check CLRS.Chapter09.randomizedSelectExpectedCost_le_randSelectExpectedCost
#check CLRS.Chapter09.randomizedSelectExpectedCost_linear_bound

example :
    CLRS.Chapter09.randomizedSelectCostWithSchedule
      1 0 [1, 2] [1, 0] = some 3 := by
  native_decide

example :
    CLRS.Chapter09.randomizedSelectCostWithSchedule
      1 0 [1, 2] [1, 1] = none := by
  native_decide

example :
    CLRS.Chapter09.randomizedSelectExpectedCost 1 0 [1, 2] =
      (5 : Real) / 2 := by
  have hfirst : CLRS.Chapter09.selectByRank? 0 [1, 2] = some 1 := by
    native_decide
  have hsecond : CLRS.Chapter09.selectByRank? 1 [1, 2] = some 2 := by
    native_decide
  have hsingleton : CLRS.Chapter09.selectByRank? 0 [1] = some 1 := by
    native_decide
  norm_num [CLRS.Chapter09.randomizedSelectExpectedCost,
    CLRS.Chapter09.randomizedSelectExpectedCostFuel,
    CLRS.Probability.expect, CLRS.Chapter09.ltCount,
    CLRS.Chapter09.leCount, Finset.sum_range_succ,
    hfirst, hsecond, hsingleton]
