import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms

/-!
# Chapter 27. Multithreaded Algorithms

Chapter 27 marks the beginning of Part VII (Parallel Algorithms) in CLRS.
It develops a formal model for dynamic multithreading and analyzes parallel
algorithms in terms of **work** (total operations) and **span** (critical path length).

## Sections

### 27.1 The Basics of Dynamic Multithreading
Formalizes the computation-DAG model, work/span, speedup, parallelism,
and the greedy-scheduler bound (Theorem 27.1/27.2).
Main declarations:
{lit}`CLRS.Chapter27.Strand`,
{lit}`CLRS.Chapter27.CompDAG`,
{lit}`CLRS.Chapter27.CompDAG.work` (T₁),
{lit}`CLRS.Chapter27.CompDAG.span` (T∞),
{lit}`CLRS.Chapter27.CompDAG.speedup`,
{lit}`CLRS.Chapter27.CompDAG.parallelism`,
{lit}`CLRS.Chapter27.CompDAG.greedy_bound` (Theorem 27.1),
{lit}`CLRS.Chapter27.SpawnTree` (spawn/sync model),
{lit}`CLRS.Chapter27.parallelLoopTree` (parallel-loop pattern).

### 27.2–27.4 Multithreaded Algorithms
Formalizes P-MATMUL, P-MERGE, P-MERGE-SORT, and parallel Strassen with
work/span recurrences and asymptotic bound statements.
Main declarations:
{lit}`CLRS.Chapter27.pMatMulTree`, {lit}`CLRS.Chapter27.pMatMulWork`, {lit}`CLRS.Chapter27.pMatMulSpan`,
{lit}`CLRS.Chapter27.pMergeTree`, {lit}`CLRS.Chapter27.pMergeWork`, {lit}`CLRS.Chapter27.pMergeSpan`,
{lit}`CLRS.Chapter27.pMergeSortTree`, {lit}`CLRS.Chapter27.pMergeSortWork`, {lit}`CLRS.Chapter27.pMergeSortSpan`,
{lit}`CLRS.Chapter27.strassenSpawnTree`, {lit}`CLRS.Chapter27.strassenWork`, {lit}`CLRS.Chapter27.strassenSpan`.

## Current Shape

Section 27.1 defines the core model: `Strand` (atomic work unit), `CompDAG`
(computation DAG with nodes and dependency edges), `work` (T₁), `span` (T∞),
`speedup`, `parallelism`, and states the greedy-scheduler bound (Theorem 27.1).
The `SpawnTree` datatype captures spawn/sync patterns and models parallel loops.

Section 27.2–27.4 provides recurrence definitions for P-MATMUL, P-MERGE,
P-MERGE-SORT, and parallel Strassen, along with work/span theorem statements.
Asymptotic bounds (e.g., work Θ(n³) for P-MATMUL, span Θ(log³ n) for P-MERGE-SORT)
are stated as theorems.

## Deferred Work

* Full proofs of the greedy-scheduler bound (Theorem 27.1/27.2).
* Work/span recurrence solutions using the Chapter 4 Master Theorem.
* Executable implementations of P-MERGE, P-MERGE-SORT, and parallel Strassen.
* DAG topological properties (acyclicity, topological ordering).
* Full spawn/sync execution model with time-step semantics.
-/

namespace CLRS
namespace Chapter27
end Chapter27
end CLRS
