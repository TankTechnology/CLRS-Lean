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

* 9.1 proves simultaneous minimum/maximum correctness and the pairwise
  comparison bound.
* 9.2 proves duplicate-aware rank selection, pivot-style SELECT correctness,
  and the fresh-choice randomized expected bound.
* 9.3 proves recursive median-of-medians SELECT correctness and its complete
  worst-case comparison bound.

## Closure interface

The chapter's main public results are
{lit}`CLRS.Chapter09.minMax?_correct`,
{lit}`CLRS.Chapter09.minMax?_comparisons_le`,
{lit}`CLRS.Chapter09.freshRandomizedSelectWithRanks?_correct`,
{lit}`CLRS.Chapter09.freshRandomizedSelectExpectedComparisons_linear_bound`,
{lit}`CLRS.Chapter09.recursiveMedianOfMediansSelect?_correct`, and
{lit}`CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound`.
The proof map records the supporting theorem inventory.

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
