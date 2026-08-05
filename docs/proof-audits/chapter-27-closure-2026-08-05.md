# Chapter 27 Closure Audit

## 1. Date and Status

Date: 2026-08-05

Status: `main-proof-complete`

This audit seals the represented Chapter 27 main text, Sections 27.1--27.3,
at the repository's pure-functional algorithm and execution-cost boundary.  The
historical `Section_27_2_4_Algorithms` import path remains available only for
compatibility.  The retained parallel-Strassen recurrence API is a named
compatibility extension, not a Chapter 27 Section 27.4.

## 2. Acceptance Boundary

The accepted boundary includes:

- the computation-DAG work/span model, ready-set execution, total executable
  greedy scheduler, Brent-style schedule bound, spawn trees, and balanced
  parallel-loop work/span analysis from Section 27.1;
- pure depth-indexed P-ADD and race-free P-MATMUL values, correctness proofs,
  exact execution-cost equalities, and all-input work/span bounds from Section
  27.2; and
- executable binary lower bound, P-MERGE, and P-MERGE-SORT values,
  correctness, exact step costs, universal upper bounds, and explicit
  lower-witness families from Section 27.3.

The seal excludes mutable-array implementations, shared-memory write
semantics, concrete RAM operation/allocation costs, exercises, and chapter-end
problems.  Those are separate implementation or second-track refinements; they
are not silently counted as proved by this audit.

Two model facts are especially important for interpreting the accepted
boundary accurately:

1. Executable P-MERGE uses the real midpoint/binary-search control structure.
   `pMerge_childSize_le_threeQuarters` proves that each actual child is at most
   `totalSize - totalSize / 4`; the proof does not substitute a half-size
   recurrence.
2. Executable P-MATMUL runs eight recursive products in parallel and then calls
   P-ADD sequentially.  Its execution-attached span is therefore
   `Theta(log^2 n)` through `pMatMulExecSpan`.  The older `pMatMulSpan`
   recurrence assumes constant-time combine work and has logarithmic span; it
   is retained as an idealized compatibility model, not claimed as the runtime
   of `pMatMul`.

## 3. Source-Module Responsibilities

| Scope | Source | Responsibility |
| --- | --- | --- |
| 27.1 | `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model.lean` | Stable Section 27.1 aggregator |
| 27.1 | `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S1_ComputationDAG.lean` | Computation DAG, work, longest weighted path, and span |
| 27.1 | `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S2_ReadyExecution.lean` and `S3_GreedyAccounting.lean` | Ready-set execution and complete/incomplete-step schedule accounting |
| 27.1 | `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S4_ExecutableScheduler.lean` | Total greedy scheduler, exhaustion, and end-to-end schedule bound |
| 27.1 | `CLRSLean/Chapter_27/Section_27_1_Multithreading_Model/S5_SpawnTreeAndLoops.lean` | Spawn trees and exact/all-input parallel-loop work/span facts |
| 27.2--27.3 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean` | Historical compatibility aggregator; the main-text responsibility ends at 27.3 |
| 27.2 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S1_CostModel.lean` | Value/work/span carrier and sequential/parallel composition |
| 27.2 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Definitions.lean` and `Correctness.lean` | Executable P-ADD/P-MATMUL and matrix correctness |
| 27.2 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/` | Execution equalities, monotonicity, power bounds, and all-input bounds for executable matrix costs |
| 27.2--27.3 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S2_Recurrences.lean` and `S3_AllInputBounds.lean` | Retained idealized P-MATMUL recurrence plus P-MERGE/P-MERGE-SORT recurrence analysis |
| 27.3 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/` | Duplicate-sensitive executable binary lower bound and logarithmic costs |
| 27.3 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/MergeSplit.lean` and `ParallelMerge/PMerge/` | Real P-MERGE split/control structure and correctness proof |
| 27.3 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/` | Three-quarter child bound, exact steps, linear work, quadratic-log span, and witness lower bound |
| 27.3 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Definitions.lean` and `Correctness/` | Executable P-MERGE-SORT and sorted-permutation correctness |
| 27.3 | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/` | Exact recurrence links, `n log n` work, cubic-log span, and worst-family witness |
| Extension | `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/` | Retained parallel-Strassen recurrence definitions, monotonicity, sandwiches, and all-input bounds |
| Public entry | `CLRSLean/Chapter_27.lean` | Single chapter import and reader-facing completion boundary |
| Closure contract | `Tests/Chapter_27_Closure.lean` | Aggregator-only checks and headline axiom inspection |

## 4. Headline Closure Theorems

- `CompDAG.greedySchedule_final_work_eq_zero` and
  `CompDAG.greedySchedule_time_le_work_div_add_span` show that the total
  executable greedy scheduler consumes all work and satisfies
  `T_p <= T_1 / p + T_infinity`.
- `parallelLoop_span_le_log` gives the all-input logarithmic balanced-loop span
  upper bound.
- `pAdd_correct`, `pAdd_work_eq`, `pAdd_span_eq`,
  `pAddWork_allInput_bigTheta`, and `pAddSpan_allInput_bigTheta` connect
  executable addition to its value and `Theta(n^2)` work / `Theta(log n)` span.
- `pMatMul_correct`, `pMatMul_work_eq`, `pMatMul_span_eq`,
  `pMatMulExecWork_allInput_bigTheta`, and
  `pMatMulExecSpan_allInput_bigTheta` connect the race-free executable value to
  `Theta(n^3)` work and `Theta(log^2 n)` span.
- `pMerge_correct` proves sorted-permutation correctness;
  `pMerge_childSize_le_threeQuarters` proves the real recursive shrink;
  `pMerge_work_lower` and `pMerge_work_upper` give matching linear work; and
  `pMerge_span_upper` plus `pMerge_interleaved_span_lower` give a universal
  quadratic-log upper bound and an explicit matching witness family.
- `pMergeSort_correct` proves sorted-permutation correctness;
  `pMergeSort_work_lower` and `pMergeSort_work_upper` give matching
  `n log n` work; and `pMergeSort_span_upper` plus
  `pMergeSort_worstFamily_span_lower` give a universal cubic-log upper bound
  and an explicit matching witness family.
- `strassenWork_allInput_bigTheta` and `strassenSpan_allInput_bigTheta` preserve
  the legacy Strassen recurrence surface from the separately labeled
  compatibility extension.

## 5. Requirement-to-Evidence Audit

| Requirement | Evidence | Result |
| --- | --- | --- |
| Total executable scheduler and completion | `CompDAG.greedySchedule`, `CompDAG.greedySchedule_final_work_eq_zero` | Complete |
| Greedy scheduler performance theorem | `CompDAG.greedySchedule_time_le_work_div_add_span` | Complete |
| Logarithmic parallel-loop span | `parallelLoop_span_le_log` | Complete |
| P-ADD value and execution-attached costs | `pAdd_correct`, `pAdd_work_eq`, `pAdd_span_eq`, both all-input `bigTheta` theorems | Complete |
| Race-free P-MATMUL value and actual execution costs | `pMatMul_correct`, `pMatMul_work_eq`, `pMatMul_span_eq`, both `pMatMulExec*` all-input `bigTheta` theorems | Complete |
| Binary lower-bound semantics and logarithmic charge | `binaryLowerBound_partition`, `binaryLowerBound_work_le_log`, `binaryLowerBound_span_le_log` | Complete |
| Real P-MERGE correctness and structural shrink | `pMerge_correct`, `pMerge_childSizes_add_one`, `pMerge_childSize_le_threeQuarters` | Complete |
| P-MERGE work and worst-case span | `pMerge_work_lower`, `pMerge_work_upper`, `pMerge_span_upper`, `pMerge_interleaved_span_lower` | Complete |
| P-MERGE-SORT correctness | `pMergeSort_correct`, `pMergeSort_value_sorted`, `pMergeSort_value_perm`, `pMergeSort_value_length` | Complete |
| P-MERGE-SORT work and worst-case span | `pMergeSort_work_lower`, `pMergeSort_work_upper`, `pMergeSort_span_upper`, `pMergeSort_worstFamily_span_lower` | Complete |
| All-input merge recurrence packages | `pMergeWork_allInput_bigTheta`, `pMergeSpan_allInput_bigTheta`, `pMergeSortWork_allInput_bigTheta`, `pMergeSortSpan_allInput_bigTheta` | Complete |
| Main-text/extension boundary and legacy import surface | Chapter guide, historical aggregator, `ParallelStrassen`, and `Tests/Chapter_27_Closure.lean` | Complete |
| No textual proof holes or local axiom declarations | marker scan over Chapter 27 sources and focused tests | Complete for the scanned boundary |

## 6. Verification and Axiom Boundary

The closure audit ran these exact commands from the repository root:

```bash
lake env lean Tests/Chapter_27_Closure.lean
rg -n '\b(sorry|admit|axiom)\b|TODO|FIXME|placeholder' \
  CLRSLean/Chapter_27 Tests/Chapter_27*.lean -g '*.lean'
uv run python scripts/check_repository.py
uv run python scripts/check_site_consistency.py
git diff --check
```

The closure test exits successfully and has exactly one import,
`CLRSLean.Chapter_27`.  It checks at least one public theorem for every sealed
algorithm/cost obligation and checks the two retained Strassen extension
theorems.  Its `#print axioms` results list only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or
project-defined axiom among the inspected headline theorems.

The marker scan produces no matches (raw `rg` exit status 1).  Thus the scanned
Chapter 27 source and focused tests contain no textual `sorry`, `admit`, local
`axiom`, TODO/FIXME, or placeholder marker.  The repository and site
consistency checkers exit successfully, and `git diff --check` is silent.

## 7. Optional Refinements

- Refine the pure matrix and list executions to mutable arrays with explicit
  disjoint-write invariants.
- Connect the carried natural-number charges to a concrete RAM or allocation
  semantics.
- Add lower-level constants, cache effects, or scheduler implementations
  without weakening the current mathematical interface.
- Formalize selected exercises and chapter-end problems as a separate track.
- Add an executable Strassen algorithm if desired; its retained recurrence API
  is already isolated and is not needed to reopen the Chapter 27 main-text
  seal.

These optional refinements may extend Chapter 27 without changing the sealed
`main-proof-complete` status for the accepted pure-functional boundary.
