# Chapter 9 Closure Audit

Date: 2026-07-15

Status: `main-proof-complete`

Core completion commit: `353ec4a`

## Acceptance Boundary

This audit seals Sections 9.1--9.3 for the repository's pure functional list
model and CLRS comparison-cost claims. It covers simultaneous minimum/maximum,
rank selection, fresh-choice randomized SELECT, and recursive
median-of-medians SELECT. It does not claim mutable-array refinement, a random
number generator implementation, allocation accounting, or hardware-level RAM
timing.

## Source Directory

| Section | Source | Responsibility |
| --- | --- | --- |
| 9.1 | `CLRSLean/Chapter_09/Section_09_1_Minimum_And_Maximum.lean` | Pairwise simultaneous extrema, correctness, and comparison bound |
| 9.2 | `CLRSLean/Chapter_09/Section_09_2_Select_By_Rank.lean` | Rank certificates, specification selection, and quickselect correctness |
| 9.2 | `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select.lean` | Uniform-pivot majorizer, executable fresh-choice paths, and expected comparison bound |
| 9.3 | `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean` | Pivot-parametric selection, recursive median of medians, partition bounds, and total comparison cost |

## Closure Theorems

- `CLRS.Chapter09.minMax?_correct` and
  `CLRS.Chapter09.minMax?_comparisons_le`: simultaneous extrema are correct and
  use at most `3 * floor(n / 2)` comparisons.
- `CLRS.Chapter09.quickSelect?_correct`: a successful selector result satisfies
  the duplicate-aware rank certificate.
- `CLRS.Chapter09.freshRandomizedSelectWithRanks?_correct`: every successful
  finite fresh-choice execution path is rank-correct.
- `CLRS.Chapter09.freshRandomizedSelectContinuationSize_le_subproblemSize` and
  `CLRS.Chapter09.freshRandomizedSelectExpectedComparisons_linear_bound`: every
  actual continuation is coupled to the CLRS larger-side recurrence and has
  expected comparison cost at most `4n`.
- `CLRS.Chapter09.recursiveMedianOfMediansSelect?_correct` and
  `CLRS.Chapter09.recursiveMedianOfMediansComparisonCost_linear_bound`: the
  executable recursive median-of-medians selector is rank-correct, and its
  end-to-end comparison cost, including nested pivot construction, is at most
  `100n`.

## Verification Evidence

- `lake build CLRSLean.Chapter_09`
- `lake env lean Tests/Chapter_09_Interface.lean`
- `lake env lean Tests/Chapter_09_Closure.lean`
- unfinished-proof marker scan over `CLRSLean/Chapter_09` and both Chapter 9
  tests
- `git diff --check`
- `uv run python scripts/check_progress_csv.py`
- `uv run python scripts/gen_readme_table.py --check`
- `uv run python scripts/check_site_consistency.py`
- `uv run python scripts/test_literate_config.py`
- `uv run python scripts/test_literate_navigation.py`

`Tests/Chapter_09_Closure.lean` prints the axiom dependencies of the closure
theorems. They use only `propext`, `Classical.choice`, and `Quot.sound`; no
project-specific axiom is introduced.

## Deferred Refinements

- Mutable-array partitioning and in-place execution.
- Concrete random-number generation.
- Allocation, instruction-level traces, and RAM-cost constants.

These are lower-level engineering refinements and do not reopen the sealed
Chapter 9 proof boundary.
