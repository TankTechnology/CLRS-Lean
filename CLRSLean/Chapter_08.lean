import CLRSLean.Chapter_08.Section_08_2_Counting_Sort

/-!
# Chapter 8 - Sorting in Linear Time

The first Chapter 8 pass focuses on pure correctness for stable linear-time
sorting primitives before cost models.

## Sections

* 8.2 Counting sort: {lit}`proved` for a stable bucket specification.
  Main results:
  {lit}`CLRS.Chapter08.countingSortBy_ordered`,
  {lit}`CLRS.Chapter08.countingSortBy_bucket_eq`,
  {lit}`CLRS.Chapter08.countingSortBy_mem_iff`, and
  {lit}`CLRS.Chapter08.countingSortBy_correct`.

## Current Gaps

* Array-level count table and prefix-sum implementation of {lit}`COUNTING-SORT`.
* 8.3 Radix sort, using stable counting sort as a subroutine.
* 8.4 Bucket sort and probabilistic expected-time analysis.
-/

namespace CLRS
namespace Chapter08
end Chapter08
end CLRS
