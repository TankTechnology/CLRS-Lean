import CLRSLean.FourthEdition.Chapter_07.Section_07_1_Description_Of_Quicksort
import CLRSLean.FourthEdition.Chapter_07.Section_07_2_Performance_Of_Quicksort
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.OperationalBridge
import CLRSLean.FourthEdition.Chapter_07.Section_07_4_Analysis_Of_Quicksort

/-!
# Chapter 7 — Quicksort

Native fourth-edition chapter guide.

## Current source

This guide sources fourth-edition §7.1–§7.4 from the native section modules
under {lit}`CLRSLean.FourthEdition.Chapter_07`.  Declarations retain the
{lit}`CLRS.Chapter07` namespace; the legacy import {lit}`CLRSLean.Chapter_07`
and its {lit}`Section_07_*` modules forward to these sources during the
compatibility period.

Chapter 7 now has four compiler-clean proof layers: the functional quicksort
correctness spine, a deterministic comparison-count upper bound, the
expected-comparison recurrence with a named closed form and harmonic bounds,
and an explicit finite random-priority semantics whose pair trace is proved
pointwise equal to the recursive quicksort comparison counter and whose
expected comparison count is proved equal to that closed form.

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
  form and {lit}`Θ(n log n)` asymptotic bound, including an explicit uniform
  sample space {lit}`Equiv.Perm (Fin n)`, its concrete permutation input to the
  executable first-pivot quicksort, an executable natural pair-trace counter,
  the pivot-symmetry theorem, and the exact expectation bridge.  Main results:
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
  {lit}`CLRS.Chapter07.expectedComparisons_succ_add_two`,
  {lit}`CLRS.Chapter07.sum_compared_prob_eq_expectedComparisons`,
  {lit}`CLRS.Chapter07.priorityPivot_uniform`,
  {lit}`CLRS.Chapter07.randomizedQuicksortOutput_correct`,
  {lit}`CLRS.Chapter07.randomizedQuicksortComparisonCount_eq_quickSortComparisons`,
  {lit}`CLRS.Chapter07.explicitRandomizedQuicksortExpectedComparisons_eq`,
  {lit}`CLRS.Chapter07.operationalRandomizedQuicksortExpectedComparisons_eq`, and
  {lit}`CLRS.Chapter07.operationalRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn`.

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

The expected-comparison closed form, the {lit}`Θ(n log n)` asymptotic, the
pointwise bridge from the CLRS pair trace to recursive execution, and the
expectation bridge through pairwise indicators are proved.  Independence of
pair indicators is neither assumed nor needed: finite linearity of expectation
and the proved transposition symmetry suffice.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
