import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort
import CLRSLean.Chapter_07.Section_07_2_Performance_Of_Quicksort
import CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort
import CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability
import CLRSLean.Chapter_07.Section_07_4_Analysis_Of_Quicksort

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
  form and {lit}`Θ(n log n)` asymptotic bound, including the bridge between the
  random-permutation probability model and the algebraic closed form.  Main results:
  {lit}`CLRS.Chapter07.harmonic_succ`,
  {lit}`CLRS.Chapter07.sum_mul_harmonic_eq`,
  {lit}`CLRS.Chapter07.sum_expectedComparisons_eq`,
  {lit}`CLRS.Chapter07.expectedComparisons_closed_form`,
  {lit}`CLRS.Chapter07.expectedComparisons_recurrence`,
  {lit}`CLRS.Chapter07.expectedComparisons_telescope`,
  {lit}`CLRS.Chapter07.expectedComparisons_clrs_harmonic_bound`,
  {lit}`CLRS.Chapter07.expectedComparisons_harmonic_bound`,
  {lit}`CLRS.Chapter07.expectedComparisons_quadratic`,
  {lit}`CLRS.Chapter07.expectedComparisons_monotone`,
  {lit}`CLRS.Chapter07.expectedComparisons_isBigTheta_nlogn`,
  {lit}`CLRS.Chapter07.expectedComparisons_succ_add_two`, and
  {lit}`CLRS.Chapter07.sum_compared_prob_eq_expectedComparisons`.

* 7.4 Analysis of quicksort: {lit}`proved` for the expected running time.
  The section identifies the expected running time with the expected number of
  comparisons `E[X]` (each comparison performs `O(1)` work and dominates all
  other operations), proves the indicator decomposition
  `E[X] = Σ_{i<j} P[z_i and z_j are compared] = Σ_{i<j} 2/(j-i+1)` through
  {lit}`CLRS.Chapter07.expectedRunningTime_eq_sum_compared_prob`, and closes
  with CLRS Theorem 7.1: the expected running time is `Θ(n log n)`
  ({lit}`CLRS.Chapter07.expectedRunningTime_isBigTheta_nlogn`), with the
  explicit harmonic upper bound
  {lit}`CLRS.Chapter07.expectedRunningTime_le_two_mul`.

## Current Gaps

* Index-level mutable-array {lit}`PARTITION` loop refinement and RAM cost model.
* Sharp {lit}`n log n` tail bound (Chernoff/Hoeffding) and lower bound
  ({lit}`Omega(n log n)` for comparison sorting).

The expected-comparison closed form, the {lit}`Θ(n log n)` asymptotic, and the
bridge between the random-permutation probability model and the algebraic formula
({lit}`sum_compared_prob_eq_expectedComparisons`) are now proved.  The remaining
random pivot-choice independence assertion and expectation-of-sum theorem are
deferred refinements.
-/

namespace CLRS
namespace Chapter07
end Chapter07
end CLRS
