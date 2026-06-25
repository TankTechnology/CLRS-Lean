import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.Chapter_08.Section_08_4_Bucket_Sort

/-!
# Chapter 8 - Sorting in Linear Time

The first Chapter 8 pass focuses on pure correctness for stable linear-time
sorting primitives before cost models.

## Sections

* 8.2 Counting sort: {lit}`proved` for a stable bucket specification.
  Main results:
  {lit}`CLRS.Chapter08.countingSortBy_ordered`,
  {lit}`CLRS.Chapter08.countingSortBy_bucket_eq`,
  {lit}`CLRS.Chapter08.countingSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.countingSortBy_perm`, and
  {lit}`CLRS.Chapter08.countingSortBy_correct`.
* 8.3 Radix sort: {lit}`proved` for an abstract stable digit-pass model with
  complete digit-signature stability and a concrete base-{lit}`b` digit
  extraction wrapper for natural-number keys, including an ordinary key-order
  wrapper and its one-digit arithmetic discharge.
  Main results:
  {lit}`CLRS.Chapter08.radixPass_orderedRel`,
  {lit}`CLRS.Chapter08.radixSortBy_ordered`,
  {lit}`CLRS.Chapter08.radixSortBy_stable`,
  {lit}`CLRS.Chapter08.radixSortBy_mem_iff`,
  {lit}`CLRS.Chapter08.radixSortBy_perm`,
  {lit}`CLRS.Chapter08.radixSortBy_correct_stable`, and
  {lit}`CLRS.Chapter08.radixSortNatBy_correct_keyOrdered_singleDigit`.
* 8.4 Bucket sort: {lit}`proved` for a deterministic bucket-index model.
  Main results:
  {lit}`CLRS.Chapter08.bucketSortBy_correct` and
  {lit}`CLRS.Chapter08.bucketSortByRank_correct`.

## Current Gaps

* Array-level count table and prefix-sum implementation of {lit}`COUNTING-SORT`.
* Multi-digit numeric-key ordering refinement for concrete radix sort.
* Bucket-sort probabilistic expected-time analysis.
-/

namespace CLRS
namespace Chapter08
end Chapter08
end CLRS
