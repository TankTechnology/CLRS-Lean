# Chapter 9 - Medians and Order Statistics

Chapter 9 has a clean Section 9.1--9.3 structure and is complete for its
advertised pure functional and comparison-cost models.

- Closure audit: `docs/proof-audits/chapter-09-closure-2026-07-15.md`

## Section 9.1 - Minimum and maximum

- Lean source: `CLRSLean/Chapter_09/Section_09_1_Minimum_And_Maximum.lean`
- Status: `proved`
- Main theorems: `CLRS.Chapter09.minMax?_correct` and
  `CLRS.Chapter09.minMax?_comparisons_le`

The executable algorithm groups the input into pairs. It compares each pair
once, then compares only the smaller member with the running minimum and only
the larger member with the running maximum. A successful result contains two
input members that bound every input element, and its recorded comparison
count is at most `3 * floor(n / 2)`.

## Section 9.2 - Selection in expected linear time

- Lean source: `CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean`
- Expected-cost support:
  `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select.lean`
- Status: `proved`
- Main theorems: `CLRS.Chapter09.quickSelect?_correct`,
  `CLRS.Chapter09.randomizedSelectMajorizer_bigO_linear`,
  `CLRS.Chapter09.randomizedSelectCostWithSchedule_rankCorrect`,
  `CLRS.Chapter09.freshRandomizedSelectContinuationSize_le_subproblemSize`,
  `CLRS.Chapter09.randomizedSelectExpectedCost_le_randSelectExpectedCost`, and
  `CLRS.Chapter09.randomizedSelectExpectedCost_linear_bound`

The common rank certificate handles duplicates by requiring that the number
of strictly smaller values is at most the requested zero-based rank and that
the number of weakly smaller values is greater than the rank. The expected-cost
support first derives the uniform-pivot larger-side recurrence and proves that
it is `O(n)`. The schedule interpreter
`randomizedSelectCostWithSchedule c k xs choices` consumes one occurrence rank
per visited state, charges exactly `c * currentLength`, rejects exhausted or
out-of-range schedules, and erases every successful cost run to the same
rank-correct SELECT path.

The expected semantics is recursively state-dependent: every recursive call
samples a fresh uniform occurrence rank from the current `Fin n`, partitions
the current input, and follows only the branch selected by the requested rank.
This is a nested conditional-uniform process, not a flat uniform distribution
over variable-length schedules. Each real continuation is bounded by
`max i (n - 1 - i)` even with duplicate values. The theorem
`randomizedSelectExpectedCost_le_randSelectExpectedCost` couples every input,
rank, fuel value, and natural local-work constant to the CLRS majorizer;
`randomizedSelectExpectedCost_linear_bound` then proves
`E[C] ≤ 4 * c * xs.length`. The older unit-charge theorem
`freshRandomizedSelectExpectedComparisons_linear_bound` remains compatible via
`randomizedSelectExpectedCost_one`.

The metric is deliberately a partition-work abstraction. It does not charge
the specification implementation of `selectByRank?` (which sorts to expose an
occurrence rank), random-number generation, `List` primitives, allocation, or
RAM instructions.

## Section 9.3 - Selection in worst-case linear time

- Lean source: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean`
- Status: `proved`
- Main theorems: `CLRS.Chapter09.medianOfMediansSelect?_isSome_of_lt`,
  `CLRS.Chapter09.recursiveMedianOfMediansSelect?_correct`,
  `CLRS.Chapter09.recursiveMedianOfMediansPivot?_partition_size_bound`, and
  `CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound`

The section proves the pivot-parametric selector correct and total under an
explicit pivot-totality hypothesis. It specializes that interface to the
current executable median selector, proves the five-element median certificate,
grouped split counts, the `7n/10 + O(1)` branch bound, and the abstract linear
recurrence. The older partition-path diagnostic remains bounded by
`17 * xs.length`.

The executable recursive layer now selects the median of the group medians by
recursively using the same safe, total pivot interface; it is total,
rank-correct, and satisfies the same branch bound. The end-to-end cost
`recursiveMedianOfMediansComparisonCost` charges all four components at every
node: full-group median work, recursive selection of the median of group
medians, the current partition scan, and the selected strict branch. A
strengthened induction over input size and both fuel parameters proves
`recursiveMedianOfMediansComparisonCost k xs ≤ 100 * xs.length`.

## Current completion boundary

The chapter is `main-proof-complete` for pure functional correctness and CLRS
comparison costs. Mutable-array partitioning, an implementation of the random
number generator, the internal cost of the rank-coordinate analysis function,
allocation, and hardware-level RAM timing are lower-level engineering
refinements and do not reopen this proof boundary.
