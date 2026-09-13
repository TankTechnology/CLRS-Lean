import CLRSLean.Chapter_27
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S1_ComputationDAG
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S2_ReadyExecution
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S3_GreedyAccounting
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S4_ExecutableScheduler
import CLRSLean.FourthEdition.Chapter_26.Section_26_1_Multithreading_Model.S5_SpawnTreeAndLoops
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_Parallel_Matrix_Multiplication
import CLRSLean.FourthEdition.Chapter_26.Section_26_3_Parallel_Merge_Sort
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelStrassen

/-!
# Chapter 26 — Parallel Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 26.1--26.3 are native fourth-edition sections with separate canonical
reader pages for fork-join parallelism, parallel matrix multiplication, and
parallel merge sort. Declarations retain the legacy `CLRS.Chapter27` namespace
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
* [Parallel Strassen Recurrences](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelStrassen/)

## Coverage boundary

The native sections supply the represented fourth-edition parallel
sections (§26.1 fork-join basics, §26.2 parallel matrix multiplication,
§26.3 parallel merge sort). The actual matrix constructors take a depth
{lit}`k` and operate on dimension {lit}`2^k`. Their exact carried work/span
proofs apply to those executions. The all-input asymptotic theorems bound
numerical recurrence extensions at arbitrary {lit}`n`; they do not construct
a padding/unpadding execution for arbitrary matrix dimensions. The completing
greedy scheduler and executed merge/merge-sort work/span results retain their
stated domains.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
