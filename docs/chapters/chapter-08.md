# Chapter 8 - Sorting in Linear Time

Chapter 8 now has compiler-clean correctness spines for counting sort, radix
sort, and deterministic bucket sort.  The radix-sort layer includes an explicit
complete-signature stability theorem, and the bucket-sort layer includes the
finite-uniform collision and second-moment core plus the CLRS textbook
unit-cost random variable.  Its linear expectation is proved only at that
abstract layer.

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
- `CLRS.Chapter08.countingSortBy_perm`: the output is a permutation of the
  input, so duplicates are preserved with their multiplicities.
- `CLRS.Chapter08.countingSortBy_correct`: the reader-facing conjunction of
  sortedness, stability, membership preservation, and permutation preservation.

## Section 8.3 - Radix sort

- Lean source: `CLRSLean/Chapter_08/Section_08_3_Radix_Sort.lean`
- Status: `proved` for the abstract stable digit-pass model with
  complete digit-signature stability
- Main theorem: `CLRS.Chapter08.radixSortBy_correct_stable`

The model takes digit functions in least-significant to most-significant order.
Each pass is a stable `countingSortBy`, and the final order is expressed as the
induced most-significant-first lexicographic relation.  Stability is stated by
filtering the input and output to all elements that match a fixed sample on
every digit; the two filtered lists are exactly equal.

The theorem layer proves:

- `CLRS.Chapter08.radixPass_orderedRel`: one stable digit pass upgrades an
  existing lower-priority relation to a lexicographic relation with the new
  digit as the higher-priority key.
- `CLRS.Chapter08.radixSortBy_ordered`: repeated passes return a list ordered
  by the induced radix lexicographic relation.
- `CLRS.Chapter08.radixSortBy_stable`: for each complete digit signature, the
  output subsequence is exactly the corresponding input subsequence.
- `CLRS.Chapter08.radixSortBy_mem_iff`: membership is preserved when all digit
  functions are bounded by the declared maximum digit.
- `CLRS.Chapter08.radixSortBy_perm`: repeated stable digit passes preserve the
  input as a permutation.
- `CLRS.Chapter08.radixSortBy_correct`: the reader-facing conjunction of
  lexicographic ordering, membership preservation, and permutation preservation.
- `CLRS.Chapter08.radixSortBy_correct_stable`: the same reader-facing
  correctness theorem with the explicit stability clause.

## Section 8.4 - Bucket sort

- Lean source: `CLRSLean/Chapter_08/Section_08_4_Bucket_Sort.lean`
- Status: `proved` for deterministic bucket-index correctness and
  `proved-abstract` for the textbook expected-cost model
- Main theorem: `CLRS.Chapter08.bucketSortByRank_correct`

The model separates the deterministic correctness theorem from the CLRS
probabilistic analysis.  It assumes a bucket-index function and a final rank
function.  The cross-bucket hypothesis says that every element in an earlier
bucket is no larger than every element in a later bucket.

The theorem layer proves:

- `CLRS.Chapter08.bucketSortBy_ordered`: abstract bucket sort returns output
  ordered by the final rank when each bucket sorter is correct and bucket
  indices respect the rank order.
- `CLRS.Chapter08.bucketSortBy_perm`: abstract bucket sort preserves the input
  as a permutation.
- `CLRS.Chapter08.bucketSortBy_correct`: the reader-facing correctness wrapper
  for any correct per-bucket sorter.
- `CLRS.Chapter08.bucketSortByRank_correct`: an executable wrapper that sorts
  each bucket with Lean's verified `mergeSort`.
- `CLRS.Chapter08.uniformAverageFin2_collision`: two independent finite-uniform
  bucket choices collide with probability `1 / m`.
- `CLRS.Chapter08.expectedBucketQuadraticCost_self_eq`: the exact
  second-moment identity for the bucket occupancy square sum.
- `CLRS.Chapter08.expectedBucketQuadraticCost_self_linear_bound`: the linear
  bound when the number of buckets matches the number of inputs.
- `CLRS.Chapter08.expectedBucketSortCost_self_eq`: the abstract scan plus
  bucket-occupancy expected-cost expression is exactly `3n - 1`.
- `CLRS.Chapter08.expectedBucketSortCost_linear_bound`: the same expression is
  bounded by `3n`, matching the CLRS linear expected-time conclusion at this
  abstraction layer.
- `CLRS.Chapter08.textbookBucketSortCost`: the CLRS unit-cost random variable
  `n + Σⱼ nⱼ²` over uniformly random bucket assignments.
- `CLRS.Chapter08.fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost`:
  its expectation is exactly the existing abstract expected-cost expression.
- `CLRS.Chapter08.expectedTextbookBucketSortCost_isBigO`: the textbook random
  variable has linear expectation.

## Hard Follow-Up Work

- Array-level `COUNTING-SORT`: requires count-array and prefix-sum invariants
  and a refinement theorem to the stable bucket specification.
- Bucket sort expected time: the CLRS unit-cost random variable has linear
  expectation.  Remaining: a single-pass executable bucket builder, a costed
  per-bucket sorter, and a refinement theorem connecting their execution cost
  to the abstract model.  In particular, the current `bucketSortByRank`
  repeatedly filters the input and is not instrumented by the textbook random
  variable.
