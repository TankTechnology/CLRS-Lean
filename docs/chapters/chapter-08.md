# Chapter 8 - Sorting in Linear Time

Chapter 8 now has compiler-clean correctness spines for counting sort and
radix sort.

## Section 8.2 - Counting sort

- Lean source: `CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean`
- Status: `proved` for the stable bucket specification
- Main theorem: `CLRS.Chapter08.countingSortBy_correct`

The model uses the stable bucket view of counting sort.  Given a key function
and a maximum key, `countingSortBy` scans keys in increasing order and emits
the input bucket for each key.

The theorem layer proves:

- `CLRS.Chapter08.countingSortBy_ordered`: output is ordered by key.
- `CLRS.Chapter08.countingSortBy_bucket_eq`: each equal-key bucket in the
  output is exactly the corresponding input bucket, preserving equal-key order.
- `CLRS.Chapter08.countingSortBy_mem_iff`: membership is preserved when input
  keys are bounded by the declared maximum.
- `CLRS.Chapter08.countingSortBy_correct`: the reader-facing conjunction of
  sortedness, stability, and membership preservation.

## Section 8.3 - Radix sort

- Lean source: `CLRSLean/Chapter_08/Section_08_3_Radix_Sort.lean`
- Status: `proved` for the abstract stable digit-pass model
- Main theorem: `CLRS.Chapter08.radixSortBy_correct`

The model takes digit functions in least-significant to most-significant order.
Each pass is a stable `countingSortBy`, and the final order is expressed as the
induced most-significant-first lexicographic relation.

The theorem layer proves:

- `CLRS.Chapter08.radixPass_orderedRel`: one stable digit pass upgrades an
  existing lower-priority relation to a lexicographic relation with the new
  digit as the higher-priority key.
- `CLRS.Chapter08.radixSortBy_ordered`: repeated passes return a list ordered
  by the induced radix lexicographic relation.
- `CLRS.Chapter08.radixSortBy_mem_iff`: membership is preserved when all digit
  functions are bounded by the declared maximum digit.
- `CLRS.Chapter08.radixSortBy_correct`: the reader-facing conjunction of
  lexicographic ordering and membership preservation.

## Hard Follow-Up Work

- Array-level `COUNTING-SORT`: requires count-array and prefix-sum invariants
  and a refinement theorem to the stable bucket specification.
- Concrete radix keys: requires base-`b` digit extraction for natural-number
  keys and a refinement theorem to the abstract digit-function interface.
- Bucket sort expected time: requires a probability model for the input
  distribution.
