import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort_Array
import CLRSLean.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.Chapter_08.Section_08_4_Bucket_Sort

/-!
# Chapter 8 - Sorting in Linear Time

The first Chapter 8 pass focuses on pure correctness for stable linear-time
sorting primitives, with a first finite-uniform expected-cost interface for the
bucket-sort second-moment argument.

## Sections

* 8.2 Counting sort: {lit}`proved` for a stable bucket specification and a
  count-table/prefix-count refinement layer.
  Main results:
  {lit}`CLRS.Chapter08.countingSortBy_ordered`,
  {lit}`CLRS.Chapter08.countingSortBy_bucket_eq`,
  {lit}`CLRS.Chapter08.countingSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.countingSortBy_perm`, and
  {lit}`CLRS.Chapter08.countingSortBy_correct`;
  {lit}`CLRS.Chapter08.countTable_sum_eq_countingSortBy_length`,
  {lit}`CLRS.Chapter08.cumulativeCountTable_length`, and
  {lit}`CLRS.Chapter08.countingSortByTable_correct`.
* 8.3 Radix sort: {lit}`proved` for an abstract stable digit-pass model with
  complete digit-signature stability and a concrete base-{lit}`b` digit
  extraction wrapper for natural-number keys, including an ordinary key-order
  wrapper and bounded fixed-width arithmetic discharge.
  Main results:
  {lit}`CLRS.Chapter08.radixPass_orderedRel`,
  {lit}`CLRS.Chapter08.radixSortBy_ordered`,
  {lit}`CLRS.Chapter08.radixSortBy_stable`,
  {lit}`CLRS.Chapter08.radixSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.radixSortBy_perm`,
  {lit}`CLRS.Chapter08.radixSortBy_correct_stable`,
  {lit}`CLRS.Chapter08.radixDigitOrderRespectsKey_of_bounded`, and
  {lit}`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_of_bounded`.
* 8.4 Bucket sort: {lit}`proved` for a deterministic bucket-index model, plus
  a finite-uniform collision/second-moment interface for the expected-time
  argument.
  Main results:
  {lit}`CLRS.Chapter08.bucketSortBy_correct` and
  {lit}`CLRS.Chapter08.bucketSortByRank_correct`;
  {lit}`CLRS.Chapter08.uniformAverageFin2_collision`,
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_eq`, and
  {lit}`CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`.

## Current Gaps

* Imperative reverse-scan output-array implementation of {lit}`COUNTING-SORT`.
* Full bucket-sort probabilistic expected-time analysis over an explicit input
  distribution and independence model.
-/

namespace CLRS
namespace Chapter08
end Chapter08
end CLRS
