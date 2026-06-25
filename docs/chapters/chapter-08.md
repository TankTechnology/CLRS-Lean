# Chapter 8 - Sorting in Linear Time

Chapter 8 now has a first compiler-clean correctness spine for counting sort.

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

## Hard Follow-Up Work

- Array-level `COUNTING-SORT`: requires count-array and prefix-sum invariants
  and a refinement theorem to the stable bucket specification.
- Radix sort: should reuse `countingSortBy_bucket_eq` as the stable digit-pass
  theorem.
- Bucket sort expected time: requires a probability model for the input
  distribution.
