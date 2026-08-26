import CLRSLean.Chapter_02.Section_02_1_Insertion_Sort
import CLRSLean.Chapter_02.Section_02_2_Analyzing_Algorithms
import CLRSLean.Chapter_02.Section_02_3_Designing_Algorithms
import CLRSLean.Chapter_02.Section_02_3_Designing_Algorithms.Merge_Sort_Recurrence

/-!
# Chapter 2 - Getting Started

Chapter 2 is the first complete workflow pilot for CLRSLean.  It establishes the
basic pattern used throughout the project:

1. Textbook claim.
2. Lean-friendly mathematical model.
3. Public theorem interface.
4. Local proof.
5. Status map update.

## Sections

* 2.1 Insertion sort: {lit}`proved`.
  Main results: {lit}`CLRS.Chapter02.insertionSort_sorted`,
  {lit}`CLRS.Chapter02.insertionSort_perm`.
* 2.2 Analyzing algorithms: {lit}`proved`.
  Main result: {lit}`CLRS.Chapter02.insertionSortWorstComparisons_quadratic`.
* 2.3 Designing algorithms: {lit}`proved`.
  Main results: {lit}`CLRS.Chapter02.merge_correct`,
  {lit}`CLRS.Chapter02.merge_comparisons_le`,
  {lit}`CLRS.Chapter02.mergeSort_sortedLE`,
  {lit}`CLRS.Chapter02.mergeSort_perm`,
  {lit}`CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`,
  {lit}`CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_on_exact_powers`, and
  {lit}`CLRS.Chapter02.MergeSortRecurrence.theta_n_log_n_all_inputs`.

## Proof Themes

Insertion sort is modeled as a functional list algorithm.  The textbook loop
invariant becomes two structural claims: inserting into an ordered list
preserves orderedness, and insertion preserves the input elements up to
permutation.

The algorithm-analysis section deliberately starts with a lightweight cost
model.  It proves the standard quadratic upper bound for the insertion-sort
worst-case comparison count without committing the project to a full RAM
semantics.

The section now contains an explicit list-level MERGE execution whose value and
comparison counter are computed together.  Its public contract proves sorted
output, exact permutation and length preservation, and a linear comparison
bound.  The top-level sort still uses Lean's verified List.mergeSort and exposes
CLRS-facing theorem names for sortedness, permutation preservation, the exact
closed form of the power-of-two recurrence, and the all-input Θ(n log n) bound
for the arbitrary-size floor/ceiling recurrence (via the Chapter 4.6
Master-theorem sandwich bridge).

## Strengthening Targets

Future Chapter 2 work should keep the main theorem pages stable while adding
stronger optional layers:

* a full pseudocode-line or RAM cost semantics beyond head comparisons;
* selected exercises after the main section interfaces remain stable.
-/
