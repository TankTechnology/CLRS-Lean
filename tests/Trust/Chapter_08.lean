import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_08

/-! # Chapter 8 flagship trust surface -/

#check CLRS.Chapter08.comparisonSort_worstCase_lowerBound
#check CLRS.Chapter08.MutableOutput.countingSortArrayCost_bigO
#check CLRS.Chapter08.expectedBucketSortByRankCost_isBigO

#assert_axioms CLRS.Chapter08.comparisonSort_worstCase_lowerBound
#assert_axioms CLRS.Chapter08.MutableOutput.countingSortArrayCost_bigO
#assert_axioms CLRS.Chapter08.expectedBucketSortByRankCost_isBigO

example : CLRS.Chapter08.countingSortBy 5 id [5, 2, 4, 1, 3] = [1, 2, 3, 4, 5] := by
  decide

-- Repair #351: actual returned values and counters.
#assert_axioms CLRS.Chapter08.SortTree.runWithCost_result
#assert_axioms CLRS.Chapter08.comparisonSort_exists_run_lowerBound
#assert_axioms CLRS.Chapter08.CountingExecution.execute_result
#assert_axioms CLRS.Chapter08.CountingExecution.execute_controllerVisits
#assert_axioms CLRS.Chapter08.CountingExecution.execute_indexedWork
#assert_axioms CLRS.Chapter08.MutableOutput.countingSortArray_eq_scatter
#assert_axioms CLRS.Chapter08.radixSortByWithCost_cost_eq
#assert_axioms CLRS.Chapter08.radixSortByWithIndexedWork_cost_eq
#assert_axioms CLRS.Chapter08.BucketExecution.insertionWithCost_work_le_sq
#assert_axioms CLRS.Chapter08.bucketSortByRank_correct
#assert_axioms CLRS.Chapter08.bucketSortByRankWithCost_work_le
#assert_axioms CLRS.Chapter08.expectedBucketExecutionWork_isBigO
