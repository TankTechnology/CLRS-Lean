import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S1_ComputationDAG
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S2_ReadyExecution
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S3_GreedyAccounting
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S4_ExecutableScheduler
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S5_SpawnTreeAndLoops
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
  work and span characterizations.  Complete/incomplete greedy-schedule
  accounting is connected to an explicit ready-set execution of the weighted
  computation DAG, proving `Tₚ ≤ T₁ / p + T∞`.
  Main declarations:
  {lit}`CLRS.Chapter27.Strand`,
  {lit}`CLRS.Chapter27.CompDAG`,
  {lit}`CLRS.Chapter27.CompDAG.work`,
  {lit}`CLRS.Chapter27.CompDAG.longestTo`,
  {lit}`CLRS.Chapter27.CompDAG.span`,
  {lit}`CLRS.Chapter27.CompDAG.span_le_work`,
  {lit}`CLRS.Chapter27.CompDAG.ready`,
  {lit}`CLRS.Chapter27.DAGScheduleStep`,
  {lit}`CLRS.Chapter27.DAGSchedule`,
  {lit}`CLRS.Chapter27.DAGSchedule.time_le_work_div_add_span`,
  {lit}`CLRS.Chapter27.GreedyScheduleAccounting.time_le_work_div_add_span`,
  {lit}`CLRS.Chapter27.GreedyScheduleTrace.time_le_work_div_add_span`,
  {lit}`CLRS.Chapter27.GreedyScheduleRun.time_le_work_div_add_span`,
  {lit}`CLRS.Chapter27.SpawnTree`,
  {lit}`CLRS.Chapter27.SpawnTree.span_le_work`,
  {lit}`CLRS.Chapter27.parallelLoopTree`,
  {lit}`CLRS.Chapter27.parallelLoop_work`,
  {lit}`CLRS.Chapter27.parallelLoop_span`,
  {lit}`CLRS.Chapter27.parallelLoopDepth_pow`.

* 27.2–27.4 Multithreaded algorithms.
  Executable work/span recurrences for P-MATMUL, P-MERGE, P-MERGE-SORT, and
  parallel Strassen, each with an exact closed form on powers of two.  The
  merge-based and parallel-Strassen recurrences also have monotonicity,
  adjacent-power sandwich, and all-input Θ theorems; P-MATMUL has all-input
  upper bounds.
  Main declarations:
  {lit}`CLRS.Chapter27.pMatMulWork`, {lit}`CLRS.Chapter27.pMatMulWork_pow_two`,
  {lit}`CLRS.Chapter27.pMatMulWork_le`,
  {lit}`CLRS.Chapter27.pMatMulSpan`, {lit}`CLRS.Chapter27.pMatMulSpan_pow_two`,
  {lit}`CLRS.Chapter27.pMatMulSpan_le`,
  {lit}`CLRS.Chapter27.pMergeWork`, {lit}`CLRS.Chapter27.pMergeWork_pow_two`,
  {lit}`CLRS.Chapter27.pMergeWork_monotone`,
  {lit}`CLRS.Chapter27.pMergeWork_power_sandwich`,
  {lit}`CLRS.Chapter27.pMergeWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMergeSpan`, {lit}`CLRS.Chapter27.pMergeSpan_pow_two`,
  {lit}`CLRS.Chapter27.pMergeSpan_monotone`,
  {lit}`CLRS.Chapter27.pMergeSpan_power_sandwich`,
  {lit}`CLRS.Chapter27.pMergeSpan_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMergeSortWork`,
  {lit}`CLRS.Chapter27.pMergeSortWork_pow_two`,
  {lit}`CLRS.Chapter27.pMergeSortWork_monotone`,
  {lit}`CLRS.Chapter27.pMergeSortWork_power_sandwich`,
  {lit}`CLRS.Chapter27.pMergeSortWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMergeSortSpan`,
  {lit}`CLRS.Chapter27.pMergeSortSpan_pow_two`,
  {lit}`CLRS.Chapter27.pMergeSortSpan_monotone`,
  {lit}`CLRS.Chapter27.pMergeSortSpan_power_sandwich`,
  {lit}`CLRS.Chapter27.pMergeSortSpan_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.strassenWork`, {lit}`CLRS.Chapter27.strassenWork_pow_two`,
  {lit}`CLRS.Chapter27.strassenWork_monotone`,
  {lit}`CLRS.Chapter27.strassenWork_power_sandwich`,
  {lit}`CLRS.Chapter27.strassenWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.strassenSpan`, {lit}`CLRS.Chapter27.strassenSpan_pow_two`,
  {lit}`CLRS.Chapter27.strassenSpan_monotone`,
  {lit}`CLRS.Chapter27.strassenSpan_power_sandwich`,
  {lit}`CLRS.Chapter27.strassenSpan_allInput_bigTheta`.

## Deferred work

* Executable P-MERGE / P-MERGE-SORT implementations refining the recurrences.
-/

namespace CLRS
namespace Chapter27

end Chapter27
end CLRS
