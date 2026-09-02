import CLRSLean.Chapter_27
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S1_ComputationDAG
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S2_ReadyExecution
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S3_GreedyAccounting
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S4_ExecutableScheduler
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S5_SpawnTreeAndLoops
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S1_CostModel
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S2_Recurrences
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S3_AllInputBounds
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMergeSort
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelStrassen

/-!
# Chapter 26 — Parallel Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 26.1--26.3 are native fourth-edition sections, imported directly
from
[Section 26.1](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/)
(the fork-join basics: computation DAGs, ready execution, greedy
accounting, the executable scheduler, and spawn trees/parallel loops) and
[Section 26.2--26.3](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/)
(parallel matrix multiplication, parallel merge and merge sort, and the
parallel Strassen recurrences; the `2_4` suffix is a historical legacy
artifact).  Declarations retain the legacy `CLRS.Chapter27` namespace
during the compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_27` and {lit}`CLRSLean.Chapter_27.Section_27_*`
forward to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Computation DAGs](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S1_ComputationDAG/)
* [Ready Execution](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S2_ReadyExecution/)
* [Greedy Accounting](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S3_GreedyAccounting/)
* [Executable Scheduler](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S4_ExecutableScheduler/)
* [Spawn Trees and Parallel Loops](CLRSLean/FourthEdition/Chapter_26/Section_26_1_Multithreading_Model/S5_SpawnTreeAndLoops/)
* [Costed Execution Model](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/S1_CostModel/)
* [Parallel Recurrences](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/S2_Recurrences/)
* [All-Input Bounds](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/S3_AllInputBounds/)
* [Parallel Matrix Algorithms](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMatrix/)
* [Parallel Merge](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMerge/)
* [P-MERGE-SORT](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMergeSort/)
* [Parallel Strassen Recurrences](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelStrassen/)

## Coverage boundary

The native sections supply the represented fourth-edition parallel
sections (§26.1 fork-join basics, §26.2 parallel matrix multiplication,
§26.3 parallel merge sort).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
