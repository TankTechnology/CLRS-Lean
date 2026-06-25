# Chapter 9 - Medians and Order Statistics

Chapter 9 now has compiler-clean correctness interfaces for the specification
selector, a pivot-style quickselect model, and a pivot-parametric deterministic
SELECT model.  It also now proves the local five-element median certificate
and executable grouped split-count core that start the CLRS median-of-medians
split-size argument, including the CLRS-style partition-size bound.

## Section 9.2 - Selection by rank

- Lean source: `CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean`
- Status: `proved` for the specification selector and pivot-style quickselect
- Main theorem: `CLRS.Chapter09.quickSelect?_correct`

The section keeps the simple specification selector: sort the input list and
read the zero-based rank `k`.  It also proves a fuelled quickselect model that
uses the first element as a pivot and recursively keeps the `< pivot` or
`> pivot` side, with the middle pivot block represented by the interval
`ltCount pivot xs ≤ k < leCount pivot xs`.

The theorem layer proves:

- `CLRS.Chapter09.sortedCopy_perm`: sorting preserves exactly the input
  elements.
- `CLRS.Chapter09.sortedCopy_pairwise`: the sorted copy is pairwise ordered.
- `CLRS.Chapter09.selectByRank?_mem`: any returned value came from the input.
- `CLRS.Chapter09.selectByRank?_rankCorrect`: the returned value satisfies the
  order-statistic count certificate.
- `CLRS.Chapter09.selectByRank?_correct`: the reader-facing correctness wrapper.
- `CLRS.Chapter09.quickSelect?_mem`: any quickselect result came from the input.
- `CLRS.Chapter09.quickSelect?_rankCorrect`: pivot-style quickselect satisfies
  the same rank certificate.
- `CLRS.Chapter09.quickSelect?_correct`: the reader-facing quickselect wrapper.

The rank certificate handles duplicates in the standard way.  If the returned
value is `x`, then the number of input elements strictly smaller than `x` is at
most `k`, and the number of input elements at most `x` is greater than `k`.

## Section 9.3 - Deterministic selection

- Lean source: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean`
- Status: `proved` for pivot-parametric deterministic SELECT correctness and
  the executable grouped median-of-medians split-count core
- Main theorem: `CLRS.Chapter09.deterministicSelect?_correct`

The section abstracts SELECT over a pivot rule.  The only required hypothesis is
that the pivot rule returns a member of the current input list.  Under that
assumption, the recursive selector preserves the Chapter 9.2 rank certificate
through the `< pivot`, pivot-block, and `> pivot` branches.

The theorem layer proves:

- `CLRS.Chapter09.selectWithPivot?_mem`: any successful pivot-parametric SELECT
  result came from the input.
- `CLRS.Chapter09.selectWithPivot?_rankCorrect`: pivot-parametric SELECT
  satisfies the order-statistic count certificate.
- `CLRS.Chapter09.selectWithPivot?_correct`: the reader-facing wrapper for any
  membership-safe pivot rule.
- `CLRS.Chapter09.medianOfFive?_certificate`: for any five-element group, the
  rank-2 selector returns an input median with at least three elements at most
  it and at least three elements at least it.
- `CLRS.Chapter09.fullGroupsOfFive_lengths`: every executable full group has
  length five.
- `CLRS.Chapter09.fullGroupsOfFive_length_mul_five_le`: executable full groups
  consume no more than the input length.
- `CLRS.Chapter09.fullGroupsOfFive_length_near`: executable full grouping
  drops at most four trailing input elements.
- `CLRS.Chapter09.fullGroupsOfFive_flatten_sublist`: the flattened executable
  full groups form a sublist of the original input.
- `CLRS.Chapter09.leCount_le_of_sublist` and
  `CLRS.Chapter09.geCount_le_of_sublist`: count lower bounds lift along
  sublists.
- `CLRS.Chapter09.gtCount_eq_length_sub_leCount`: the strict-greater branch
  length is the complement of the weak-lower count.
- `CLRS.Chapter09.medianOfFiveGroups?_certificates`: mapping the five-element
  median selector across length-five groups constructs grouped certificates.
- `CLRS.Chapter09.fullGroupsOfFive_medianGroupCertificates`: executable
  grouping plus median mapping constructs the abstract certificate layer.
- `CLRS.Chapter09.medianGroupCertificates_leCount_lower_bound`: certified
  five-element groups contribute three original elements for every group median
  at most a pivot.
- `CLRS.Chapter09.medianGroupCertificates_geCount_lower_bound`: the symmetric
  lower bound for group medians at least a pivot.
- `CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`: if the
  pivot has a rank certificate among the group medians, the flattened original
  groups inherit the corresponding three-per-group lower bounds.
- `CLRS.Chapter09.fullGroupsOfFive_selectPivot_split_counts`: the same
  split-count theorem specialized to executable full groups.
- `CLRS.Chapter09.fullGroupsOfFive_medianPivot_split_counts`: the same
  split-count theorem specialized to selecting the median of the group medians.
- `CLRS.Chapter09.fullGroupsOfFive_medianPivot_fullInput_split_counts`: the
  median-of-medians split counts lifted from full groups to the original input.
- `CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_lengths`: raw length
  bounds for the strict `< pivot` and `> pivot` recursive branches.
- `CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_size_bound`: the
  CLRS-style `10 * branchSize ≤ 7 * n + 12` packaging for both branches.
- `CLRS.Chapter09.deterministicPivot?_mem`: the deterministic median-pivot rule
  returns only input elements.
- `CLRS.Chapter09.deterministicSelect?_correct`: the deterministic median-pivot
  SELECT instance satisfies the same rank certificate.

## Hard Follow-Up Work

- Randomized SELECT expected time: requires a probability model for randomized
  pivots and a cost recurrence or indicator argument.
- Deterministic linear-time SELECT: the rank-correct deterministic interface,
  local five-element median certificate, executable grouping, and grouped
  split-count core are proved all the way to the `7n/10 + O(1)` partition-size
  bound, but recurrence analysis remains.
