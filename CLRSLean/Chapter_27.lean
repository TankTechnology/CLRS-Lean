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
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Span
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Span.Envelope
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Span.Bounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Span.WitnessLists
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Span.LowerBound
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Correctness.Spec
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Correctness.Main
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Step
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.RecurrenceLinks
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Work
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Work.Bounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span.Bounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span.WitnessInput
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span.MapInvariance
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span.LowerBound
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelStrassen
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelStrassen.Recurrences
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelStrassen.Recurrences.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelStrassen.Recurrences.Monotonicity
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelStrassen.Recurrences.AllInputBounds

/-! # Chapter 27 - Multithreaded Algorithms

Chapter 27 opens Part VII (Parallel Algorithms) of CLRS.  It develops the
dynamic-multithreading model and analyzes parallel algorithms in terms of
**work** (T₁, total operations) and **span** (T∞, critical-path length).

## Sections

* 27.1 The basics of dynamic multithreading.
  The computation-DAG model has forward (topologically ordered) edges and an
  honestly computed longest-weighted-path span.  Its ready-set semantics feeds
  the total executable {lit}`CLRS.Chapter27.CompDAG.greedySchedule`: the final
  residual work is zero and its time satisfies `Tₚ ≤ T₁ / p + T∞`.
  The spawn/sync-tree model has unit spawn overhead, and the balanced
  parallel-loop tree has exact work/span formulas together with all-input
  logarithmic depth and span upper bounds.  Main declarations:
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
  {lit}`CLRS.Chapter27.CompDAG.greedySchedule`,
  {lit}`CLRS.Chapter27.CompDAG.greedySchedule_final_work_eq_zero`,
  {lit}`CLRS.Chapter27.CompDAG.greedySchedule_time_le_work_div_add_span`,
  {lit}`CLRS.Chapter27.SpawnTree`,
  {lit}`CLRS.Chapter27.SpawnTree.span_le_work`,
  {lit}`CLRS.Chapter27.parallelLoopTree`,
  {lit}`CLRS.Chapter27.parallelLoop_work`,
  {lit}`CLRS.Chapter27.parallelLoop_span`,
  {lit}`CLRS.Chapter27.parallelLoopDepth_pow`,
  {lit}`CLRS.Chapter27.parallelLoopDepth_le_log`,
  {lit}`CLRS.Chapter27.parallelLoop_span_le_log`.

* 27.2 Multithreaded matrix multiplication.
  An executable {lit}`Costed` layer attaches a pure value to exact work and
  span, with sequential and balanced parallel composition.  P-ADD and the
  race-free P-MATMUL execute quadrant operations through deterministic
  fork/join trees; {name}`CLRS.Chapter27.pAdd_correct` and
  {name}`CLRS.Chapter27.pMatMul_correct` prove ordinary matrix addition and
  multiplication over any ring.  Execution equalities connect their carried
  costs to {lit}`CLRS.Chapter27.pAddWork`,
  {lit}`CLRS.Chapter27.pAddSpan`,
  {lit}`CLRS.Chapter27.pMatMulExecWork`, and
  {lit}`CLRS.Chapter27.pMatMulExecSpan`.  The resulting all-input bounds are
  Θ(n²) work / Θ(log n) span for P-ADD and Θ(n³) work /
  Θ(log² n) span for executable P-MATMUL.  The legacy
  {lit}`CLRS.Chapter27.pMatMulSpan` recurrence instead models a constant-time
  combine and therefore has Θ(log n) span; it is intentionally not the runtime
  of the implementation, whose sequential P-ADD combine phase yields the
  log-squared span.  Main declarations:
  {lit}`CLRS.Chapter27.Costed`,
  {lit}`CLRS.Chapter27.Costed.seq`, {lit}`CLRS.Chapter27.Costed.par`,
  {lit}`CLRS.Chapter27.Costed.par4`, {lit}`CLRS.Chapter27.Costed.par8`,
  {lit}`CLRS.Chapter27.pAdd`, {lit}`CLRS.Chapter27.pAdd_correct`,
  {lit}`CLRS.Chapter27.pMatMul`, {lit}`CLRS.Chapter27.pMatMul_correct`,
  {lit}`CLRS.Chapter27.pAdd_work_eq`, {lit}`CLRS.Chapter27.pAdd_span_eq`,
  {lit}`CLRS.Chapter27.pMatMul_work_eq`,
  {lit}`CLRS.Chapter27.pMatMul_span_eq`,
  {lit}`CLRS.Chapter27.pAddWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pAddSpan_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMatMulExecWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMatMulExecSpan_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.pMatMulSpan_le`.

* 27.3 Multithreaded merge sort.
  The executable binary lower bound used by P-MERGE has a proved strict-left,
  nonstrict-right partition and logarithmic work/span.  The
  {name}`CLRS.Chapter27.MergeSplit` and {name}`CLRS.Chapter27.pMerge` layer
  implements the actual midpoint/binary-search P-MERGE control structure;
  {name}`CLRS.Chapter27.pMerge_correct` proves its value is a sorted
  permutation of the two sorted inputs with exact output length.  Its actual
  execution also has pointwise linear work, proved by logarithmic-potential
  strong induction, and pointwise quadratic-logarithmic span.  A monotone
  three-quarter envelope proves the upper bound, while sorted interleaved
  even/odd power-of-two inputs provide the matching lower witness.
  {name}`CLRS.Chapter27.pMergeSort` now implements the full midpoint-split,
  parallel-recursive, P-MERGE-based sorting control structure, and
  {name}`CLRS.Chapter27.pMergeSort_correct` proves that every result is a
  sorted permutation of its input with unchanged length.  Exact one-step cost
  equations connect this execution to its recurrence: the pointwise work
  bounds give Θ(n log n), the universal span upper bound is cubic-logarithmic,
  and {name}`CLRS.Chapter27.worstMergeSortInput` supplies a matching recursive
  lower-witness family.  Thus the executable P-MERGE-SORT cost gap is closed.
  The merge-based recurrences also have monotonicity, adjacent-power
  sandwiches, and all-input Θ theorems.  Main declarations:
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
  {lit}`CLRS.Chapter27.pMerge_span_upper`,
  {lit}`CLRS.Chapter27.evenKeys`, {lit}`CLRS.Chapter27.oddKeys`,
  {lit}`CLRS.Chapter27.pMerge_interleaved_span_lower`,
  {lit}`CLRS.Chapter27.pMergeSort`,
  {lit}`CLRS.Chapter27.PMergeSortSpec`,
  {lit}`CLRS.Chapter27.pMergeSort_correct`,
  {lit}`CLRS.Chapter27.pMergeSort_value_sorted`,
  {lit}`CLRS.Chapter27.pMergeSort_value_perm`,
  {lit}`CLRS.Chapter27.pMergeSort_value_length`,
  {lit}`CLRS.Chapter27.pMergeSort_work_step_eq`,
  {lit}`CLRS.Chapter27.pMergeSort_span_step_eq`,
  {lit}`CLRS.Chapter27.pMergeSort_work_lower`,
  {lit}`CLRS.Chapter27.pMergeSort_work_upper`,
  {lit}`CLRS.Chapter27.pMergeSort_span_upper`,
  {lit}`CLRS.Chapter27.worstMergeSortInput`,
  {lit}`CLRS.Chapter27.worstMergeSortInput_length`,
  {lit}`CLRS.Chapter27.pMergeSort_worstFamily_span_lower`,
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
  {lit}`CLRS.Chapter27.pMergeSortSpan_allInput_bigTheta`.

* Parallel Strassen compatibility extension.
  The historical Chapter 27 import surface retains a separate recurrence-only
  analysis for a parallelized Strassen variant.  It is not presented as a
  Chapter 27 main-text section.  Main declarations:
  {lit}`CLRS.Chapter27.strassenWork`, {lit}`CLRS.Chapter27.strassenWork_pow_two`,
  {lit}`CLRS.Chapter27.strassenWork_monotone`,
  {lit}`CLRS.Chapter27.strassenWork_power_sandwich`,
  {lit}`CLRS.Chapter27.strassenWork_allInput_bigTheta`,
  {lit}`CLRS.Chapter27.strassenSpan`, {lit}`CLRS.Chapter27.strassenSpan_pow_two`,
  {lit}`CLRS.Chapter27.strassenSpan_monotone`,
  {lit}`CLRS.Chapter27.strassenSpan_power_sandwich`,
  {lit}`CLRS.Chapter27.strassenSpan_allInput_bigTheta`.

The filesystem name {lit}`Section_27_2_4_Algorithms` is retained solely for
import compatibility with existing clients.  The represented Chapter 27 main
text ends at Section 27.3; the Strassen recurrences above are a named extension,
not a fabricated Section 27.4.

## Completion boundary

The represented Chapter 27 main-text core is complete: algorithms,
correctness, execution-attached work/span bounds, recurrence analyses, and the
greedy-scheduler theorem are connected at their reader-facing interfaces.
The retained parallel-Strassen recurrences are already isolated behind their
compatibility extension and are not a Chapter 27 proof obligation.
Mutable-array implementations, RAM-level operation and allocation costs,
exercises, and chapter-end problems are outside this sealed pure-functional
boundary.
-/

namespace CLRS
namespace Chapter27

end Chapter27
end CLRS
