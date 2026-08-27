# Executable Costed Merge Sort Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Implement a total merge sort that actually calls the verified local `mergeWithCost`, then prove its value and execution-derived work satisfy the Chapter 2 correctness and all-input asymptotic contracts.

**Architecture:** Split definitions, correctness, and cost into three focused modules behind one stable facade.  Refactor the abstract recurrence module's unused Section 2.3 import to prevent a cycle.  Keep Mathlib `List.mergeSort` only as a compatibility result proved equal through sorted-permutation uniqueness.

**Tech Stack:** Lean 4.32, Mathlib `List.Perm`/`SortedLE`, existing Chapter 2 `mergeWithCost`, existing Chapter 2/4 recurrence and asymptotic bridges.

---

### Task 1: Pin the missing public interface

**Files:**
- Modify: `Tests/Chapter_02_Merge_Interface.lean`

- [ ] Add failing `#check`s for `MergeSortExecution`, `mergeSortWithCost`,
  `mergeSortWithCost_perm`, `mergeSortWithCost_sorted`,
  `mergeSortWithCost_eq_mergeSort`, `mergeSortWithCost_work_eq_length`,
  `mergeSortWork_recurrence`, and `mergeSortWork_isBigTheta_nlogn`.
- [ ] Run `lake env lean Tests/Chapter_02_Merge_Interface.lean` and confirm the
  first new declaration is unknown while all existing MERGE checks still pass.

### Task 2: Implement the recursive execution

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort/Definitions.lean`
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms.lean`

- [ ] Define `MergeSortExecution` with value, comparison, output-write, and
  execution-work fields.
- [ ] Define a length-terminating `mergeSortWithCost` with empty, singleton,
  and two-or-more cases.  The recursive case must call `mergeWithCost` on the
  recursively returned values.
- [ ] Expose value and counter projections and import the facade from Section
  2.3.
- [ ] Build only the definitions module and confirm evaluation on a small list
  returns a sorted value with nonzero counters.

### Task 3: Prove semantic correctness

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort/Correctness.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort.lean`

- [ ] Prove both recursive halves are strictly shorter in the non-base case.
- [ ] Prove `mergeSortWithCost_perm` by strong length induction, `merge_perm`,
  and `List.take_append_drop`.
- [ ] Prove `mergeSortWithCost_sorted` by the same induction and
  `merge_sorted`.
- [ ] Bundle `mergeSortWithCost_correct` and prove
  `mergeSortWithCost_eq_mergeSort` through uniqueness of sorted permutations.
- [ ] Re-run the focused interface test; correctness checks should turn green
  while cost checks remain red.

### Task 4: Derive the cost recurrence from the execution

**Files:**
- Modify: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge_Sort_Recurrence.lean`
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort/Cost.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/MergeSort.lean`

- [ ] Remove the recurrence module's unused import of the Section 2.3 facade.
- [ ] Prove the recursive execution equation and rewrite its combine charge
  with `merge_outputWrites_eq`.
- [ ] Define `mergeSortWork` from the actual execution on a canonical list.
- [ ] Prove work depends only on input length, then prove the exact
  floor/ceiling recurrence for its real cast.
- [ ] Prove the required monotonicity from the execution recurrence and apply
  `MergeSortRecurrence.theta_n_log_n_all_inputs`.
- [ ] Re-run the focused interface test and confirm every new check is green.

### Task 5: Add native trust evidence and checkpoint

**Files:**
- Modify: `Tests/Trust/Chapter_02.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_02.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/audits/2026-08-28-whole-book-proof-gap-audit.md`

- [ ] Add `#print axioms`/native axiom checks for the execution correctness,
  recurrence, and asymptotic theorem.
- [ ] Update Chapter 2 prose to remove the now-closed top-level MERGE bridge
  gap without claiming RAM or mutable-array semantics.
- [ ] Run the focused source modules, interface test, and Chapter 2 trust file.
- [ ] Run `python3 scripts/check_repository.py` and `git diff --check`.
- [ ] Commit the independently verifiable Chapter 2 proof batch and close issue
  #335 only after all acceptance targets pass.

