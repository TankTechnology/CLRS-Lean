import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms

/-! # Chapter 27 - Multithreaded Algorithms

Chapter 27 opens Part VII (Parallel Algorithms) of CLRS.  It develops the
dynamic-multithreading model and analyzes parallel algorithms in terms of
**work** (T₁, total operations) and **span** (T∞, critical-path length).

## Sections

* 27.1 The basics of dynamic multithreading.
  The computation-DAG model with forward (topologically ordered) edges, an
  honestly computed longest-path span, and the spawn/sync tree model with
  unit spawn overhead; the balanced parallel-loop spawn tree comes with exact
  work and span characterizations.
  Main declarations:
  {lit}`CLRS.Chapter27.Strand`,
  {lit}`CLRS.Chapter27.CompDAG`,
  {lit}`CLRS.Chapter27.CompDAG.work`,
  {lit}`CLRS.Chapter27.CompDAG.longestTo`,
  {lit}`CLRS.Chapter27.CompDAG.span`,
  {lit}`CLRS.Chapter27.CompDAG.span_le_work`,
  {lit}`CLRS.Chapter27.SpawnTree`,
  {lit}`CLRS.Chapter27.SpawnTree.span_le_work`,
  {lit}`CLRS.Chapter27.parallelLoopTree`,
  {lit}`CLRS.Chapter27.parallelLoop_work`,
  {lit}`CLRS.Chapter27.parallelLoop_span`,
  {lit}`CLRS.Chapter27.parallelLoopDepth_pow`.

* 27.2–27.4 Multithreaded algorithms.
  Executable work/span recurrences for P-MATMUL, P-MERGE, P-MERGE-SORT, and
  parallel Strassen, each with an exact closed form on powers of two (and
  all-input upper bounds for P-MATMUL).
  Main declarations:
  {lit}`CLRS.Chapter27.pMatMulWork`, {lit}`CLRS.Chapter27.pMatMulWork_pow_two`,
  {lit}`CLRS.Chapter27.pMatMulWork_le`,
  {lit}`CLRS.Chapter27.pMatMulSpan`, {lit}`CLRS.Chapter27.pMatMulSpan_pow_two`,
  {lit}`CLRS.Chapter27.pMatMulSpan_le`,
  {lit}`CLRS.Chapter27.pMergeWork`, {lit}`CLRS.Chapter27.pMergeWork_pow_two`,
  {lit}`CLRS.Chapter27.pMergeSpan`, {lit}`CLRS.Chapter27.pMergeSpan_pow_two`,
  {lit}`CLRS.Chapter27.pMergeSortWork`,
  {lit}`CLRS.Chapter27.pMergeSortWork_pow_two`,
  {lit}`CLRS.Chapter27.pMergeSortSpan`,
  {lit}`CLRS.Chapter27.pMergeSortSpan_pow_two`,
  {lit}`CLRS.Chapter27.strassenWork`, {lit}`CLRS.Chapter27.strassenWork_pow_two`,
  {lit}`CLRS.Chapter27.strassenSpan`, {lit}`CLRS.Chapter27.strassenSpan_pow_two`.

## Deferred work

* The greedy-scheduler bound (CLRS Theorem 27.1/27.2) requires an explicit
  time-step execution model and is not claimed.
* All-input Θ-bounds for the merge-based costs (power-sandwich transfer as
  in Chapter 4) need monotonicity lemmas for the cost functions.
* Executable P-MERGE / P-MERGE-SORT implementations refining the recurrences.
-/

namespace CLRS
namespace Chapter27

end Chapter27
end CLRS
