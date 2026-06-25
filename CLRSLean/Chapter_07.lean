import CLRSLean.Chapter_07.Section_07_1_Description_Of_Quicksort

/-!
# Chapter 7 - Quicksort

Chapter 7 begins the sorting-and-selection gap in the current CLRS-Lean tree.
The first pass focuses on pure correctness before randomized or expected-time
analysis.

## Sections

* 7.1 Description of quicksort: {lit}`proved` for the current functional-list
  model, scan-state partition loop, and returned pivot-index wrapper.  Main
  results:
  {lit}`CLRS.Chapter07.partitionAround_left_eq_filter`,
  {lit}`CLRS.Chapter07.partitionAround_right_eq_filter`,
  {lit}`CLRS.Chapter07.partitionAround_correct`,
  {lit}`CLRS.Chapter07.partitionAround_perm`,
  {lit}`CLRS.Chapter07.partitionLoop_invariant`,
  {lit}`CLRS.Chapter07.partitionLoop_correct`,
  {lit}`CLRS.Chapter07.clrsPartition_correct`,
  {lit}`CLRS.Chapter07.clrsPartitionArray_correct`,
  {lit}`CLRS.Chapter07.quickSort_perm`,
  {lit}`CLRS.Chapter07.quickSort_ordered`, and
  {lit}`CLRS.Chapter07.quickSort_correct`.

## Current Gaps

* Mutable-array {lit}`PARTITION` refinement with an explicit swap trace.
* Performance analysis for deterministic quicksort.
* Randomized quicksort and expected running time.
-/

namespace CLRS
namespace Chapter07
end Chapter07
end CLRS
