import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort
import CLRSLean.Chapter_07.Section_07_2_Performance_Of_Quicksort

/-!
# Chapter 7 - Quicksort

Chapter 7 begins the sorting-and-selection gap in the current CLRS-Lean tree.
The first pass focuses on pure correctness before randomized or expected-time
analysis.

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

## Current Gaps

* Index-level mutable-array {lit}`PARTITION` loop refinement.
* Randomized quicksort and expected running time.
-/

namespace CLRS
namespace Chapter07
end Chapter07
end CLRS
