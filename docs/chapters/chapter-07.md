# Chapter 7 - Quicksort

Chapter 7 now has a compiler-clean correctness spine for quicksort, including
the functional partition specification, a scan-state proof spine for the CLRS
partition loop, and a returned pivot-index partition wrapper.

## Section 7.1 - Description of quicksort

- Lean source: `CLRSLean/Chapter_07/Section_07_1_Description_Of_Quicksort.lean`
- Status: `proved` for the current functional-list model, scan-state partition
  loop, and returned pivot-index wrapper
- Main theorems: `CLRS.Chapter07.partitionAround_correct`,
  `CLRS.Chapter07.partitionLoop_correct`,
  `CLRS.Chapter07.clrsPartition_correct`,
  `CLRS.Chapter07.clrsPartitionArray_correct`, and
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
- `CLRS.Chapter07.clrsPartitionArray_correct`: the reader-facing bundle of the
  returned-index, bounds, and permutation facts.

The quicksort theorem layer proves:

- `CLRS.Chapter07.quickSort_perm`: quicksort preserves the input elements up to
  permutation.
- `CLRS.Chapter07.quickSort_ordered`: quicksort returns an ordered list.
- `CLRS.Chapter07.quickSort_correct`: the reader-facing conjunction of
  sortedness and permutation preservation.

## Hard Follow-Up Work

- Mutable-array `PARTITION` refinement: the scan-state loop invariant and
  returned-index postcondition are proved, but a true swap trace over an
  array-segment model remains.
- Deterministic performance analysis: requires a cost recurrence tied to the
  partition sizes.
- Randomized quicksort expected time: requires a probability model for random
  pivots or random permutations plus a recurrence or indicator-variable proof.
