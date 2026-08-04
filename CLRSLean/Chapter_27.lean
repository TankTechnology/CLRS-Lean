import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S1_ComputationDAG
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S2_ReadyExecution
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S3_GreedyAccounting
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S4_ExecutableScheduler
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S5_SpawnTreeAndLoops
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S1_CostModel
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S2_Recurrences
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S3_AllInputBounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs.ExecutionEqualities
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs.Monotonicity
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs.PowerBounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs.AllInputBounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.LowerBound
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.LowerBound.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.LowerBound.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.LowerBound.Costs
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.MergeSplit
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Correctness.Boundaries
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Correctness.Permutation
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.PMerge.Correctness.Main
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Structure
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Step
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Work
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Work.LogPotential
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Work.Bounds

/-! # Chapter 27 - Multithreaded Algorithms

Chapter 27 opens Part VII (Parallel Algorithms) of CLRS.  It develops the
dynamic-multithreading model and analyzes parallel algorithms in terms of
**work** (T₁, total operations) and **span** (T∞, critical-path length).

## Sections

* 27.1 The basics of dynamic multithreading.
  The computation-DAG model with forward (topologically ordered) edges, an
  honestly computed longest-path span, and the spawn/sync tree model with
  unit spawn overhead; the balanced parallel-loop spawn tree comes with exact
  work and span characterizations and all-input logarithmic depth and span
  upper bounds.  Complete/incomplete greedy-schedule accounting is connected
  to an explicit ready-set execution of the weighted computation DAG, proving
  `Tₚ ≤ T₁ / p + T∞`.
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
  {lit}`CLRS.Chapter27.parallelLoopDepth_pow`,
  {lit}`CLRS.Chapter27.parallelLoopDepth_le_log`,
  {lit}`CLRS.Chapter27.parallelLoop_span_le_log`.

* 27.2–27.4 Multithreaded algorithms.
  An executable {lit}`Costed` layer attaches values to their work and span, with
  sequential and balanced parallel composition.  The main-text P-ADD and
  P-MATMUL execute quadrant operations through balanced fork/join trees, and
  {name}`CLRS.Chapter27.pAdd_correct` and
  {name}`CLRS.Chapter27.pMatMul_correct` prove their matrix values correct over
  any ring.  Their execution-attached work/span recurrences are monotone, have
  exact power-of-two solutions or constant-factor bounds, and lift to
  all-input Θ theorems: P-ADD has quadratic work and logarithmic span, while
  P-MATMUL has cubic work and log-squared span ({lit}`Theta(log^2 n)`).  The earlier
  idealized P-MATMUL recurrence retains its logarithmic-span upper bound.  The
  executable binary lower bound used by P-MERGE has a proved strict-left,
  nonstrict-right partition and logarithmic work/span.  The
  {name}`CLRS.Chapter27.MergeSplit` and {name}`CLRS.Chapter27.pMerge` layer
  implements the actual midpoint/binary-search P-MERGE control structure;
  {name}`CLRS.Chapter27.pMerge_correct` proves its value is a sorted
  permutation of the two sorted inputs with exact output length.  Its actual
  execution also has pointwise linear work, proved by logarithmic-potential
  strong induction.  The merge-based and parallel-Strassen recurrences also
  have monotonicity, adjacent-power sandwich, and all-input Θ theorems.
  Main declarations:
  {lit}`CLRS.Chapter27.Costed`,
  {lit}`CLRS.Chapter27.Costed.seq`, {lit}`CLRS.Chapter27.Costed.par`,
  {lit}`CLRS.Chapter27.Costed.par4`, {lit}`CLRS.Chapter27.Costed.par8`,
  {lit}`CLRS.Chapter27.pAdd`, {lit}`CLRS.Chapter27.pAdd_value`,
  {lit}`CLRS.Chapter27.pAdd_correct`,
  {lit}`CLRS.Chapter27.pMatMul`, {lit}`CLRS.Chapter27.pMatMul_value`,
  {lit}`CLRS.Chapter27.pMatMul_correct`,
  {lit}`CLRS.Chapter27.pAddWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pAddSpan_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMatMulExecWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMatMulExecSpan_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMatMulWork`, {lit}`CLRS.Chapter27.pMatMulWork_pow_two`,
  {lit}`CLRS.Chapter27.pMatMulWork_le`,
  {lit}`CLRS.Chapter27.pMatMulSpan`, {lit}`CLRS.Chapter27.pMatMulSpan_pow_two`,
  {lit}`CLRS.Chapter27.pMatMulSpan_le`,
  {lit}`CLRS.Chapter27.binaryLowerBound`,
  {lit}`CLRS.Chapter27.binaryLowerBound_partition`,
  {lit}`CLRS.Chapter27.binaryLowerBound_work_le_log`,
  {lit}`CLRS.Chapter27.binaryLowerBound_span_le_log`,
  {lit}`CLRS.Chapter27.MergeSplit`,
  {lit}`CLRS.Chapter27.pMerge`,
  {lit}`CLRS.Chapter27.PMergeSpec`,
  {lit}`CLRS.Chapter27.pMerge_correct`,
  {lit}`CLRS.Chapter27.pMerge_value_sorted`,
  {lit}`CLRS.Chapter27.pMerge_value_perm`,
  {lit}`CLRS.Chapter27.pMerge_value_length`,
  {lit}`CLRS.Chapter27.pMerge_childSizes_add_one`,
  {lit}`CLRS.Chapter27.pMerge_childSize_le_threeQuarters`,
  {lit}`CLRS.Chapter27.pMerge_work_step_eq`,
  {lit}`CLRS.Chapter27.pMerge_span_step_eq`,
  {lit}`CLRS.Chapter27.pMerge_work_lower`,
  {lit}`CLRS.Chapter27.pMerge_work_upper`,
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

* P-MERGE now has exact one-step execution costs, the actual three-quarter
  child bound, and global pointwise linear work.  Its quadratic-log-span proof
  and the full executable P-MERGE-SORT implementation remain open.
-/

namespace CLRS
namespace Chapter27

end Chapter27
end CLRS
