import CLRSLean.Chapter_09.Section_09_2_Select_By_Rank
import CLRSLean.Chapter_09.Section_09_3_Deterministic_Select

/-!
# Chapter 9 - Medians and Order Statistics

Chapter 9 now has three compiler-clean correctness interfaces for selection: a
specification selector obtains the zero-based rank by sorting and indexing, a
pivot-style quickselect model recursively partitions around the first element,
and a pivot-parametric deterministic SELECT model abstracts over the pivot rule.
All public theorem layers prove that any returned value satisfies the usual
order-statistic count certificate.  Section 9.3 also proves the local
five-element median certificate and the grouped split-count core for the CLRS
median-of-medians split-size proof.

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
  interface, a five-element median certificate, grouped split-count bounds, and
  a deterministic median-pivot instance.  Main results:
  {lit}`CLRS.Chapter09.selectWithPivot?_correct`,
  {lit}`CLRS.Chapter09.medianOfFive?_certificate`,
  {lit}`CLRS.Chapter09.medianGroupCertificates_selectPivot_split_counts`, and
  {lit}`CLRS.Chapter09.deterministicSelect?_correct`.

## Current Gaps

* Randomized SELECT and expected running time require a probability model.
* Deterministic linear-time SELECT still needs the executable grouping wrapper,
  the final {lit}`7n/10` partition-size arithmetic, and recurrence analysis.
-/

namespace CLRS
namespace Chapter09
end Chapter09
end CLRS
