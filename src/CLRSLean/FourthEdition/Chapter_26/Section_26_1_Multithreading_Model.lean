import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S1_ComputationDAG
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S2_ReadyExecution
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S3_GreedyAccounting
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S4_ExecutableScheduler
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S5_SpawnTreeAndLoops

/-!
# 26.1. The Basics of Dynamic Multithreading

This reader-facing compatibility module collects the formalization of CLRS
§26.1. Its implementation is organized by foundation, residual execution,
greedy accounting, an executable-scheduler extension point, and spawn-tree
parallel loops. Existing imports of this module continue to expose the full
public API.

## Main results

* `CompDAG.longestTo_le` and `CompDAG.span_le_work` prove T∞ ≤ T₁ for the
  weighted computation DAG.
* `DAGSchedule.time_le_work_div_add_span` realizes the CLRS complete-step /
  incomplete-step argument, giving `Tₚ ≤ T₁ / p + T∞` for an explicit greedy
  DAG execution.
* `SpawnTree.span_le_work` proves the corresponding spawn-tree bound.
* `parallelLoop_work` and `parallelLoop_span` give the exact balanced-loop
  work and span. `parallelLoopDepth_pow` gives the lower logarithmic direction,
  while `parallelLoopDepth_le_log` and `parallelLoop_span_le_log` give
  all-input logarithmic upper bounds for the depth and span.

## Implementation details

* [Computation DAG foundation](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S1_ComputationDAG/)
* [Ready-set execution](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S2_ReadyExecution/)
* [Greedy-schedule accounting](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S3_GreedyAccounting/)
* [Executable-scheduler extension point](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S4_ExecutableScheduler/)
* [Spawn trees and parallel loops](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S5_SpawnTreeAndLoops/)
-/
