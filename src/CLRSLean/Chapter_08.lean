import CLRSLean.Chapter_08.Section_08_1_Lower_Bound_For_Sorting
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.CountTables
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray
import CLRSLean.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.Chapter_08.Section_08_4_Bucket_Sort

import CLRSLean.FourthEdition.Chapter_08.Section_08_1_Lower_Bound_For_Sorting.Execution
import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort.ExpectedExecution

/-!
# Chapter 8 — Compatibility guide

The canonical reader guide is {lit}`CLRSLean.FourthEdition.Chapter_08`.
Legacy section imports continue to expose the native declarations in
{lit}`CLRS.Chapter08`.

The comparison lower bound now has an actual reachable-run witness through
{lit}`comparisonSort_exists_run_lowerBound`. Counting and radix use one stable
indexed distribution per pass, with counters read from that execution.
The public bucket sorter uses the same distributor and counted insertion sort;
{lit}`expectedBucketExecutionWork_isBigO` bounds its actual work under independent
uniform bucket assignments. The older {lit}`bucketSortByRankCost` and its
expectation theorems describe the abstract occupancy budget.

These are declared controller/indexed-operation models. Array/list conversion,
persistent storage copying, allocation internals, key-function internals, and
full RAM execution are outside the model. Counting's indexed stable-bucket
controller is distinct from the retained cumulative-count/scatter specification.
-/
