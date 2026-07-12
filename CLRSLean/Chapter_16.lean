import CLRSLean.Chapter_16.Section_16_1_Activity_Selection
import CLRSLean.Chapter_16.Section_16_3_Huffman_Codes
import CLRSLean.Chapter_16.Section_16_4_Matroids
import CLRSLean.Chapter_16.Section_16_5_Task_Scheduling

/-!
# Chapter 16 - Greedy Algorithms

The current Chapter 16 site contains four proved greedy-algorithm tracks.
Section 16.1 proves the finite sorted-list activity-selection theorem for the
executable greedy selector; Section 16.3 is the project's strongest completed
greedy-algorithm case study; Section 16.4 formalizes matroid theory and the
general greedy meta-theorem; Section 16.5 applies the matroid framework to
unit-time task scheduling, proving the scheduling instance forms a matroid
and reusing the §16.4 greedy optimality theorem.

## Sections

* 16.1 Activity selection: {lit}`proved` for finite sorted lists.
  Main results: {name}`CLRS.ActivitySelection.finishSorted_head_minFinish`,
  {name}`CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`,
  {name}`CLRS.ActivitySelection.activitySelection`,
  {name}`CLRS.ActivitySelection.activitySelection_cons_eq`,
  {name}`CLRS.ActivitySelection.greedySelect_cons_eq`,
  {name}`CLRS.ActivitySelection.greedySelect_sublist`,
  {name}`CLRS.ActivitySelection.greedySelect_feasible`,
  {name}`CLRS.ActivitySelection.greedySelect_after_maxCardinality`,
  {name}`CLRS.ActivitySelection.greedySelect_cons_maxCardinality`,
  {name}`CLRS.ActivitySelection.greedySelect_maxCardinality`,
  {name}`CLRS.ActivitySelection.activitySelection_cons_maxCardinality`,
  {name}`CLRS.ActivitySelection.activitySelection_maxCardinality`,
  {name}`CLRS.ActivitySelection.greedySelect_optimal_length`,
  {name}`CLRS.ActivitySelection.greedySelect_cons_recursive_correct`,
  {name}`CLRS.ActivitySelection.activitySelection_cons_recursive_correct`,
  {name}`CLRS.ActivitySelection.activitySelection_cons_correct`, and
  {name}`CLRS.ActivitySelection.activitySelection_correct`.
* 16.3 Huffman codes: {lit}`proved`.
  Main results: {name}`CLRS.HuffmanV2.optimum_huffman_freqs`,
  {name}`CLRS.HuffmanV2.huffmanOfFreqs_correct`, and
  {name}`CLRS.HuffmanV2.huffmanOfFreqs_cost_le`.
* 16.4 Matroids and greedy methods: {lit}`proved` (builds on Mathlib's matroid
  library).
  Main results: {name}`CLRS.Matroid16.greedy_isBasis`,
  {name}`CLRS.Matroid16.greedy_optimal` (CLRS Theorem 16.10 / Corollary 16.11),
  {name}`CLRS.Matroid16.greedy_choice` (CLRS Theorem 16.6),
  {name}`CLRS.Matroid16.optimal_substructure` (CLRS Lemma 16.7), and
  {name}`CLRS.Matroid16.greedyRun_optimal`.
* 16.5 Task scheduling as a matroid: {lit}`proved`.
  Main results:
  {name}`CLRS.SchedulingMatroid.schedulingMatroid`
  (CLRS Theorem 16.13) and
  {name}`CLRS.SchedulingMatroid.minPenaltySchedule_correct`.

## Proof Theme

All sections expose the same high-level CLRS pattern: make a greedy choice,
turn the textbook exchange argument into a reusable certificate, then compose it
with the recursive subproblem.

For Huffman, the key move is a split-leaf transformation:

1. Merge the two least frequent symbols.
2. Use the inductive optimum for the merged instance.
3. Split the merged leaf back into the two original leaves.
4. Compare costs against every competing tree.

The final public theorems are stated over a frequency table.  Readers can use
{name}`CLRS.HuffmanV2.huffmanOfFreqs_correct` for the bundled correctness
statement or {name}`CLRS.HuffmanV2.huffmanOfFreqs_cost_le` for the direct
minimum-cost comparison against any consistent tree with the same frequencies.

## Why This Page Matters

Huffman is a useful benchmark for CLRS-Lean because it proves true optimality,
not only functional correctness.  Activity selection is the lighter companion:
it proves the sorted-list greedy recursion directly.  The matroid layer
(§16.4) captures the greedy meta-theorem used in §16.5 to solve the
task-scheduling problem, closing the loop from matroid theory to a concrete
CLRS application.
it proves the sorted-list greedy recursion directly.  The proof first builds
the exchange certificate from sorted order, then composes it with the recursive
tail optimum to obtain maximum cardinality for {name}`CLRS.ActivitySelection.greedySelect`.
The theorem {name}`CLRS.ActivitySelection.greedySelect_cons_recursive_correct`
exposes the nonempty recursive step itself: choose the first finish-sorted
activity, solve the filtered compatible tail, and bundle the exact recursion
equation with tail optimality, full optimality, feasibility, sublist membership,
and the optimal-length inequality.
The public wrapper {name}`CLRS.ActivitySelection.activitySelection` carries the
same recursion equation and maximum-cardinality certificates under the
CLRS-facing algorithm name.
The theorem {name}`CLRS.ActivitySelection.activitySelection_correct` exposes
the reader-facing theorem bundle: the greedy output is a feasible sublist and
no feasible sublist is longer.  The theorem
{name}`CLRS.ActivitySelection.activitySelection_cons_correct` gives the same
bundle for the nonempty recursive step.
-/
