import CLRSLean.Chapter_08.Section_08_1_Lower_Bound_For_Sorting
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.CountTables
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray
import CLRSLean.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.Chapter_08.Section_08_4_Bucket_Sort

/-!
# Chapter 8 - Sorting in Linear Time

The first Chapter 8 pass focuses on pure correctness for stable linear-time
sorting primitives, with a finite-uniform expected-cost interface for the
bucket-sort second-moment argument and its CLRS abstract unit-cost random
variable.  Section 8.1 proves the decision-tree lower bound that any
comparison-based sort needs at least `(n/2)·(log₂ n - 1)` comparisons in the
worst case.

## Sections

* 8.1 Lower bounds for sorting: {lit}`proved` for the decision-tree model over
  {lit}`Fin n` distinct elements.
  Main results:
  {lit}`CLRS.Chapter08.leafCount_le_two_pow_height`,
  {lit}`CLRS.Chapter08.run_injective_of_correctSort`,
  {lit}`CLRS.Chapter08.factorial_le_leafCount_of_correctSort`,
  {lit}`CLRS.Chapter08.height_le_logb_factorial`,
  {lit}`CLRS.Chapter08.factorial_sq_ge_pow_self`,
  {lit}`CLRS.Chapter08.logb_factorial_ge_half_mul_logb`, and
  {lit}`CLRS.Chapter08.comparisonSort_worstCase_lowerBound`.
* 8.2 Counting sort: {lit}`proved` for a stable bucket specification, a
  count-table/prefix-count refinement layer, and a mutable output-array
  refinement filled by a cumulative-count reverse scan.
  Main results:
  {lit}`CLRS.Chapter08.countingSortBy_ordered`,
  {lit}`CLRS.Chapter08.countingSortBy_bucket_eq`,
  {lit}`CLRS.Chapter08.countingSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.countingSortBy_perm`, and
  {lit}`CLRS.Chapter08.countingSortBy_correct`;
  {lit}`CLRS.Chapter08.countTable_sum_eq_countingSortBy_length`,
  {lit}`CLRS.Chapter08.cumulativeCountTable_length`, and
  {lit}`CLRS.Chapter08.countingSortByTable_correct`;
  {lit}`CLRS.Chapter08.MutableOutput.countingSortArray_toList`,
  {lit}`CLRS.Chapter08.MutableOutput.countingSortArray_correct`,
  {lit}`CLRS.Chapter08.MutableOutput.countingSortArray_size`, and
  {lit}`CLRS.Chapter08.MutableOutput.countingSortArrayCost_bigO`.
* 8.3 Radix sort: {lit}`proved` for an abstract stable digit-pass model with
  complete digit-signature stability and a concrete base-{lit}`b` digit
  extraction wrapper for natural-number keys, including an ordinary key-order
  wrapper and bounded fixed-width arithmetic discharge, plus an {lit}`O(d(n+k))`
  running-time layer.
  Main results:
  {lit}`CLRS.Chapter08.radixPass_orderedRel`,
  {lit}`CLRS.Chapter08.radixSortBy_ordered`,
  {lit}`CLRS.Chapter08.radixSortBy_stable`,
  {lit}`CLRS.Chapter08.radixSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.radixSortBy_perm`,
  {lit}`CLRS.Chapter08.radixSortBy_correct_stable`,
  {lit}`CLRS.Chapter08.radixDigitOrderRespectsKey_of_bounded`,
  {lit}`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_bounded`,
  {lit}`CLRS.Chapter08.radixSortByWithCost`, and
  {lit}`CLRS.Chapter08.radixSortNatByCost_bigO`.
* 8.4 Bucket sort: {lit}`proved` for a deterministic bucket-index model, plus
  {lit}`proved-abstract` for the finite-uniform collision/second-moment
  interface and the CLRS textbook unit-cost random variable, now bound to the
  executable construction by a single-pass builder and a costed per-bucket
  sorter.
  Main results:
  {lit}`CLRS.Chapter08.bucketSortBy_correct` and
  {lit}`CLRS.Chapter08.bucketSortByRank_correct`;
  {lit}`CLRS.Chapter08.uniformAverageFin2_collision`,
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_eq`,
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`,
  {lit}`CLRS.Chapter08.textbookBucketSortCost`,
  {lit}`CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost`,
  {lit}`CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO`,
  {lit}`CLRS.Chapter08.distributeBuckets`,
  {lit}`CLRS.Chapter08.sortBucketByRankWithCost`,
  {lit}`CLRS.Chapter08.bucketSortByRankCost`,
  {lit}`CLRS.Chapter08.bucketSortByRankCost_eq_textbookBucketSortCost`, and
  {lit}`CLRS.Chapter08.expectedBucketSortByRankCost_isBigO`.

## Current Gaps

* Section 8.1 is complete for the decision-tree model; RAM-level bookkeeping
  of individual comparisons is out of scope.
* The linear-time running-time layers are complete: counting sort has its
  {lit}`O(n+k)` mutable work bound, radix sort its {lit}`O(d(n+k))` pass-cost
  bound, and bucket sort its expected-{lit}`O(n)` bound against the real
  single-pass construction.  Remaining: a full RAM/step-count operational cost
  semantics (charging individual array reads/writes) is out of scope.
-/

namespace CLRS
namespace Chapter08
end Chapter08
end CLRS
