import CLRSLean.FourthEdition.Chapter_08.Section_08_1_Lower_Bound_For_Sorting
import CLRSLean.FourthEdition.Chapter_08.Section_08_1_Lower_Bound_For_Sorting.Execution
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.CountTables
import CLRSLean.FourthEdition.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray
import CLRSLean.FourthEdition.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort
import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort.ExpectedExecution

/-!
# Chapter 8 — Sorting in Linear Time

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 8.1--8.4 are native fourth-edition sections (lower bounds for sorting,
counting sort, radix sort, and bucket sort), imported directly from
[Section 8.1](CLRSLean/FourthEdition/Chapter_08/Section_08_1_Lower_Bound_For_Sorting/),
[Section 8.2](CLRSLean/FourthEdition/Chapter_08/Section_08_2_Counting_Sort/),
[Section 8.3](CLRSLean/FourthEdition/Chapter_08/Section_08_3_Radix_Sort/), and
[Section 8.4](CLRSLean/FourthEdition/Chapter_08/Section_08_4_Bucket_Sort/).
Section 8.2 includes the nested count-table and mutable output-array
refinements.  Declarations retain the `CLRS.Chapter08` namespace during the
compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_08` and {lit}`CLRSLean.Chapter_08.Section_08_*` forward
to these sources.

## Coverage boundary

The comparison-tree interpreter returns its actual leaf and comparison count;
{lit}`comparisonSort_exists_run_lowerBound` gives a reachable input witness.
Counting sort uses one indexed stable-bucket distribution and one output
traversal. Its output refines the original stable filter specification, including
out-of-range omissions, and radix passes consume that same execution. This is
an indexed stable-bucket implementation, not the literal cumulative-counter
decrement program; the old count-table and scatter developments remain
specification helpers.

The public bucket sorter shares the stable distributor, executes counted
insertion sort, and emits the sorted buckets. Its actual work is bounded by
{lit}`2m + 6n + 2Σ n_j²`; with {lit}`m = n` independent uniform bucket choices,
{lit}`expectedBucketExecutionWork_isBigO` proves linear expected work. Output
sortedness additionally assumes the cross-bucket rank condition. The legacy
{lit}`bucketSortByRankCost` denotes the abstract occupancy budget.

All these ledgers count declared controller/indexed primitives. Persistent-array
copying, array/list view conversion, allocation internals, and key-function
implementation costs are outside the model.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
