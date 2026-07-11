import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select.Randomized_Select

/-!
# Chapter 9 - Medians and Order Statistics

Chapter 9 now has four compiler-clean correctness interfaces for selection: a
specification selector obtains the zero-based rank by sorting and indexing, a
pivot-style quickselect model recursively partitions around the first element,
a pivot-parametric deterministic SELECT model abstracts over the pivot rule,
and a median-of-medians pivot instance specializes that interface.  All public
theorem layers prove that any returned value satisfies the usual
order-statistic count certificate.  Section 9.3 also proves the local
five-element median certificate, executable five-element grouping, grouped
split-count core, and CLRS-style partition-size bound for the
median-of-medians pivot, plus the abstract recurrence induction and concrete
linear-bound wrapper used by the textbook linear-time argument.

## Sections

* 9.2 Selection by rank: {lit}`proved` for the specification selector and the
  pivot-style quickselect model.  Main results:
  {lit}`CLRS.Chapter09.selectByRank?_mem`,
  {lit}`CLRS.Chapter09.selectByRank?_rankCorrect`, and
  {lit}`CLRS.Chapter09.selectByRank?_correct`;
  {lit}`CLRS.Chapter09.quickSelect?_mem`,
  {lit}`CLRS.Chapter09.quickSelect?_rankCorrect`, and
  {lit}`CLRS.Chapter09.quickSelect?_correct`.
* 9.3 Deterministic selection: {lit}`proved` for a pivot-parametric SELECT
  interface, a five-element median certificate, executable five-element
  grouping, grouped split-count bounds, a deterministic median-pivot instance,
  and a median-of-medians pivot/select wrapper.  Main results:
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
  {lit}`CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`, and
  {lit}`CLRS.Chapter09.medianOfMediansPivot?_partition_size_bound`, and
  {lit}`CLRS.Chapter09.medianOfMediansSelect?_correct`.
* 9.2 Randomized SELECT expected time: {lit}`proved` for the uniform
  independent-pivot expected-comparison model, its derived recurrence, and the
  CLRS Theorem 9.2 linear expected-time bound, built on the
  {lit}`CLRS.Probability.expect` / {lit}`CLRS.Probability.fintypeExpect` toolkit.
  Main results:
  {lit}`CLRS.Chapter09.randSelectExpectedCost_recurrence`,
  {lit}`CLRS.Chapter09.randSelectExpectedCost_recurrence_fintype`,
  {lit}`CLRS.Chapter09.randSelectExpectedCost_le`, and
  {lit}`CLRS.Chapter09.randomizedSelect_expected_bigO_linear`; rank correctness
  is inherited via {lit}`CLRS.Chapter09.randomizedSelectAtIndex?_rankCorrect`.

## Current Gaps

* Deterministic linear-time SELECT still needs a concrete executable cost
  semantics connected to the proved abstract recurrence theorem.
* The randomized SELECT model charges the larger partition side (the standard
  majorizing recurrence); a full joint distribution over all recursion levels
  and a concrete step-count cost model remain future refinements.
-/

namespace CLRS
namespace Chapter09
end Chapter09
end CLRS
