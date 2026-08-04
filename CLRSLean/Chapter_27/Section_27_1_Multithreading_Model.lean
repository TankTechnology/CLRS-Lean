import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S1_ComputationDAG
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S2_ReadyExecution
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S3_GreedyAccounting
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S4_ExecutableScheduler
import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model.S5_SpawnTreeAndLoops

/-!
# 27.1. The Basics of Dynamic Multithreading

This reader-facing compatibility module collects the formalization of CLRS
§27.1. Its implementation is organized by foundation, residual execution,
greedy accounting, an executable-scheduler extension point, and spawn-tree
parallel loops. Existing imports of this module continue to expose the full
public API.

## Implementation details

* [Computation DAG foundation](CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S1_ComputationDAG/)
* [Ready-set execution](CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S2_ReadyExecution/)
* [Greedy-schedule accounting](CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S3_GreedyAccounting/)
* [Executable-scheduler extension point](CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S4_ExecutableScheduler/)
* [Spawn trees and parallel loops](CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S5_SpawnTreeAndLoops/)
-/
