# Chapter 7 - Quicksort

Chapter 7 now has three compiler-clean proof layers: the quicksort correctness
spine, a deterministic comparison-count upper bound, and the
randomized-quicksort expected-comparison recurrence with harmonic bounds.  The
remaining gap is not the recurrence algebra itself, but the lower-level CLRS
array refinement and an explicit probability-space interpretation of random
pivot choices.

## Section 7.1 - Description of quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_1_Description_Of_Quicksort.lean`
- Status: `proved` for the current functional-list model, scan-state partition
  loop, and returned pivot-index wrapper with an explicit adjacent-swap trace
- Main theorems: `CLRS.Chapter07.partitionAround_correct`,
  `CLRS.Chapter07.partitionLoop_correct`,
  `CLRS.Chapter07.clrsPartition_correct`,
  `CLRS.Chapter07.clrsPartitionArray_correct_with_trace`, and
  `CLRS.Chapter07.quickSort_correct`

The first model uses a stable pivot partition.  The proved partition facts are:

- `CLRS.Chapter07.partitionAround_left_eq_filter`: the left partition is
  exactly the stable filter of elements at most the pivot.
- `CLRS.Chapter07.partitionAround_right_eq_filter`: the right partition is
  exactly the stable filter of elements greater than the pivot.
- `CLRS.Chapter07.mem_partitionAround_left_iff`: membership in the left
  partition is equivalent to input membership plus `≤ pivot`.
- `CLRS.Chapter07.mem_partitionAround_right_iff`: membership in the right
  partition is equivalent to input membership plus `> pivot`.
- `CLRS.Chapter07.partitionAround_perm`: the two partition lists contain exactly
  the original tail elements.
- `CLRS.Chapter07.partitionAround_left_allLeUpper`: every left-partition element
  is at most the pivot.
- `CLRS.Chapter07.partitionAround_right_allGt`: every right-partition element is
  greater than the pivot.
- `CLRS.Chapter07.partitionAround_correct`: the reader-facing bundle of the
  partition classification, bounds, and permutation facts.

The section also uses an explicit finite adjacent-swap trace:

- `CLRS.Chapter07.AdjacentSwapTrace.to_perm`: every adjacent-swap trace
  preserves the list elements as a permutation.
- `CLRS.Chapter07.AdjacentSwapTrace.of_perm`: any list permutation can be
  represented as a finite adjacent-swap trace.

The section also proves a CLRS-style scan loop for partition:

- `CLRS.Chapter07.partitionLoop_invariant`: the loop maintains exact low/high
  filter regions for the processed prefix.
- `CLRS.Chapter07.partitionLoop_eq_partitionAround`: the loop computes the same
  regions as the stable specification partition.
- `CLRS.Chapter07.partitionLoop_correct`: the final loop state satisfies
  bounds, membership classification, and permutation preservation.
- `CLRS.Chapter07.clrsPartition_correct`: putting the pivot between the final
  low/high regions gives a permutation of the pivot followed by the scanned
  tail.

The array-facing wrapper exposes the returned-index postcondition:

- `CLRS.Chapter07.clrsPartitionArray_pivot`: the pivot is stored at the
  returned index.
- `CLRS.Chapter07.clrsPartitionArray_left_bound`: every element before the
  returned index is at most the pivot.
- `CLRS.Chapter07.clrsPartitionArray_right_bound`: every element after the
  returned index is greater than the pivot.
- `CLRS.Chapter07.clrsPartitionArray_perm`: the output segment is a permutation
  of the pivot followed by the scanned tail.
- `CLRS.Chapter07.clrsPartitionArray_swapTrace`: the output segment is reachable
  from the input segment by adjacent swaps.
- `CLRS.Chapter07.clrsPartitionArray_correct`: the reader-facing bundle of the
  returned-index, bounds, and permutation facts.
- `CLRS.Chapter07.clrsPartitionArray_correct_with_trace`: the same bundle with
  the adjacent-swap trace in place of the abstract permutation fact.

The quicksort theorem layer proves:

- `CLRS.Chapter07.quickSort_perm`: quicksort preserves the input elements up to
  permutation.
- `CLRS.Chapter07.quickSort_ordered`: quicksort returns an ordered list.
- `CLRS.Chapter07.quickSort_correct`: the reader-facing conjunction of
  sortedness and permutation preservation.

## Section 7.2 - Performance of quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_2_Performance_Of_Quicksort.lean`
- Status: `proved` for the deterministic comparison-count model
- Main theorem: `CLRS.Chapter07.quickSortComparisons_quadratic`

The section counts one pivot comparison against every element in the current
tail, proves partition length accounting, and uses fuel induction to bound the
total functional quicksort comparison count by a quadratic expression.

The theorem layer proves:

- `CLRS.Chapter07.partitionAround_length_add`: the two partition sides account
  for exactly the current tail.
- `CLRS.Chapter07.quickSortComparisonsFuel_quadratic`: the fuelled comparison
  counter is quadratically bounded.
- `CLRS.Chapter07.quickSortComparisons_quadratic`: the reader-facing
  comparison-count upper bound.

## Section 7.3 - Randomized quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort.lean`
- Status: `proved` for the expected-comparison recurrence model
- Main theorem: `CLRS.Chapter07.expectedComparisons_harmonic_bound`

The section formalizes the CLRS expected-comparison sequence as a deterministic
recurrence over rationals.  It proves the recurrence identity, a telescoping
closed form, and the harmonic envelope used for the `O(n log n)` bound.

The theorem layer proves:

- `CLRS.Chapter07.harmonic_succ`: the harmonic-number successor identity.
- `CLRS.Chapter07.sum_mul_harmonic_eq`: the finite-sum identity needed for
  telescoping.
- `CLRS.Chapter07.sum_expectedComparisons_eq`: the recurrence sum is
  normalized into the closed-form expression.
- `CLRS.Chapter07.expectedComparisons_recurrence`: the CLRS expected-comparison
  recurrence is satisfied.
- `CLRS.Chapter07.expectedComparisons_telescope`: the telescoping closed form.
- `CLRS.Chapter07.expectedComparisons_harmonic_bound`: the harmonic upper
  bound.
- `CLRS.Chapter07.expectedComparisons_quadratic`: a coarse quadratic fallback
  bound.
- `CLRS.Chapter07.expectedComparisons_monotone`: monotonicity of the expected
  comparison sequence.

## Hard Follow-Up Work

- Mutable-array `PARTITION` refinement: the scan-state loop invariant,
  returned-index postcondition, and adjacent-swap trace are proved, but the
  concrete index-level CLRS loop over an array segment remains.
- Cost refinement: the current comparison counter is mathematical; a future
  pass should connect it to a concrete mutable-array execution cost model.
- Randomized quicksort probability semantics: the expected-comparison
  recurrence and harmonic bound are proved, but a future pass should derive
  that recurrence from an explicit probability space for random pivots or
  random permutations.
