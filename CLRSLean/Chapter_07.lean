import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort
import CLRSLean.Chapter_07.Section_07_2_Performance_Of_Quicksort
import CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort
import CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability

/-!
# Chapter 7 - Quicksort

Chapter 7 now has three compiler-clean proof layers: the functional quicksort
correctness spine, a deterministic comparison-count upper bound, and the
expected-comparison recurrence with a named closed form and harmonic bounds for
the current randomized-quicksort model.  The remaining gap is not the recurrence
algebra itself, but the lower-level CLRS array refinement and an explicit
probability space for random pivot choices.

## Sections

* 7.1 Description of quicksort: {lit}`proved` for the current functional-list
  model, scan-state partition loop, and returned pivot-index wrapper with an
  explicit adjacent-swap trace.  Main results:
  {lit}`CLRS.Chapter07.partitionAround_left_eq_filter`,
  {lit}`CLRS.Chapter07.partitionAround_right_eq_filter`,
  {lit}`CLRS.Chapter07.partitionAround_correct`,
  {lit}`CLRS.Chapter07.partitionAround_perm`,
  {lit}`CLRS.Chapter07.partitionLoop_invariant`,
  {lit}`CLRS.Chapter07.partitionLoop_correct`,
  {lit}`CLRS.Chapter07.clrsPartition_correct`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_correct`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_correct_with_trace`,
  {lit}`CLRS.Chapter07.quickSort_perm`,
  {lit}`CLRS.Chapter07.quickSort_ordered`, and
  {lit}`CLRS.Chapter07.quickSort_correct`.

* 7.2 Performance of quicksort: {lit}`proved` for a deterministic
  comparison-count quadratic upper bound.  Main results:
  {lit}`CLRS.Chapter07.partitionAround_length_add`,
  {lit}`CLRS.Chapter07.quickSortComparisons_quadratic`.

* 7.3 Randomized quicksort: {lit}`proved` for the expected-comparison closed
  form and {lit}`O(n log n)` harmonic bound.  Main results:
  {lit}`CLRS.Chapter07.harmonic_succ`,
  {lit}`CLRS.Chapter07.sum_mul_harmonic_eq`,
  {lit}`CLRS.Chapter07.sum_expectedComparisons_eq`,
  {lit}`CLRS.Chapter07.expectedComparisons_closed_form`,
  {lit}`CLRS.Chapter07.expectedComparisons_recurrence`,
  {lit}`CLRS.Chapter07.expectedComparisons_telescope`,
  {lit}`CLRS.Chapter07.expectedComparisons_clrs_harmonic_bound`,
  {lit}`CLRS.Chapter07.expectedComparisons_harmonic_bound`,
  {lit}`CLRS.Chapter07.expectedComparisons_quadratic`, and
  {lit}`CLRS.Chapter07.expectedComparisons_monotone`.

## Current Gaps

* Index-level mutable-array {lit}`PARTITION` loop refinement.
* Probabilistic model (explicit probability space, independence of pivot
  choices) — currently folded into the deterministic recurrence coefficients.
* Sharp {lit}`n log n` tail bound (Chernoff/Hoeffding) and lower bound
  ({lit}`Omega(n log n)` for comparison sorting).
-/

namespace CLRS
namespace Chapter07
end Chapter07
end CLRS
