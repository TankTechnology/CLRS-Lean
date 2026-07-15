import CLRSLean.Chapter_09.Section_09_1_Minimum_And_Maximum
import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select.Randomized_Select

/-!
# Chapter 9 - Medians and Order Statistics

Chapter 9 is structurally represented by Sections 9.1--9.3.  Section 9.1 is
complete for the simultaneous pairwise minimum/maximum algorithm and the CLRS
{lit}`3 * floor(n / 2)` comparison bound.  Sections 9.2 and 9.3 are complete
for the advertised functional and comparison-cost models: RANDOMIZED-SELECT
has fresh per-call uniform choices with expected cost at most {lit}`4n`, and
recursive median-of-medians SELECT has an end-to-end cost at most {lit}`100n`.

## Sections

* 9.1 Minimum and maximum: {lit}`proved` for the pairwise simultaneous-extrema
  algorithm.  Main results:
  {lit}`CLRS.Chapter09.minMax?_correct` and
  {lit}`CLRS.Chapter09.minMax?_comparisons_le`.
* 9.2 Selection in expected linear time: rank correctness is proved for the
  specification selector and pivot-style quickselect model.  The standard
  uniform-pivot majorizing recurrence is linear, and a fresh-choice stochastic
  execution is coupled pointwise to its larger-side argument.  Main results:
  {lit}`CLRS.Chapter09.selectByRank?_mem`,
  {lit}`CLRS.Chapter09.selectByRank?_rankCorrect`, and
  {lit}`CLRS.Chapter09.selectByRank?_correct`;
  {lit}`CLRS.Chapter09.quickSelect?_mem`,
  {lit}`CLRS.Chapter09.quickSelect?_rankCorrect`, and
  {lit}`CLRS.Chapter09.quickSelect?_correct`,
  {lit}`CLRS.Chapter09.randomizedSelectMajorizer_bigO_linear`,
  {lit}`CLRS.Chapter09.freshRandomizedSelectWithRanks?_correct`,
  {lit}`CLRS.Chapter09.freshRandomizedSelectContinuationSize_le_subproblemSize`,
  and
  {lit}`CLRS.Chapter09.freshRandomizedSelectExpectedComparisons_linear_bound`.
* 9.3 Selection in worst-case linear time: the pivot-parametric selector and
  recursively pivoted executable selector are total and rank-correct, grouped
  split-count bounds and the abstract linear recurrence are proved, and the
  complete comparison cost includes every nested pivot construction.  Main results:
  {lit}`CLRS.Chapter09.selectWithPivot?_correct`,
  {lit}`CLRS.Chapter09.medianOfFive?_certificate`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianGroupCertificates`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_split_counts`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_fullInput_split_counts`,
  {lit}`CLRS.Chapter09.fullGroupsOfFive_medianPivot_partition_size_bound`,
  {lit}`CLRS.Chapter09.selectRecurrence_linear_step`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_recursive_branch_size_bound`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_low_branch_linear_work_step`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_high_branch_linear_work_step`,
  {lit}`CLRS.Chapter09.selectRecurrence_linear_induction`,
  {lit}`CLRS.Chapter09.medianOfMedians_linear_bound`,
  {lit}`CLRS.Chapter09.clrsSelectRecurrence_linear_bound`,
  {lit}`CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`,
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`, and
  {lit}`CLRS.Chapter09.medianOfMediansSelect?_isSome_of_lt` and
  {lit}`CLRS.Chapter09.medianOfMediansSelect?_correct`; the partition-path cost
  semantics {lit}`CLRS.Chapter09.medianOfMediansPartitionPathCost` with its
  explicit bound
  {lit}`CLRS.Chapter09.medianOfMediansPartitionPathCost_linear_bound`, built on
  the generic
  {lit}`CLRS.Chapter09.selectCost_linear_bound`; and the recursive layer
  {lit}`CLRS.Chapter09.recursiveMedianOfMediansPivot?_partition_size_bound`,
  {lit}`CLRS.Chapter09.recursiveMedianOfMediansSelect?_isSome_of_lt`,
  {lit}`CLRS.Chapter09.recursiveMedianOfMediansSelect?_correct`, and
  {lit}`CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound`.

## Completion boundary

The chapter is complete for pure functional correctness and CLRS comparison
costs.  Mutable arrays, in-place partitioning, random-number generators, and
hardware-level RAM accounting are implementation refinements and do not reopen
this theorem boundary.
-/

namespace CLRS
namespace Chapter09
end Chapter09
end CLRS
