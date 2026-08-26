# Chapter 2 Explicit MERGE Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add an executable, costed CLRS MERGE procedure with kernel-checked sortedness, permutation, and linear-comparison theorems.

**Architecture:** A small `Merge` facade imports separate definition,
correctness, and cost modules. `MergeExecution` keeps the output and comparison
counter in the same recursive computation, so value correctness and runtime
cannot drift apart.

**Tech Stack:** Lean 4, Mathlib lists and `List.Perm`, Lake focused builds,
the repository's native axiom audit and progress tooling.

---

### Task 1: Pin the public interface

**Files:**
- Create: `Tests/Chapter_02_Merge_Interface.lean`

- [ ] **Step 1: Write the failing interface test**

```lean
import CLRSLean.FourthEdition.Chapter_02

#check CLRS.Chapter02.mergeWithCost
#check CLRS.Chapter02.mergeWithCost_value
#check CLRS.Chapter02.merge_perm
#check CLRS.Chapter02.merge_sorted
#check CLRS.Chapter02.merge_comparisons_le
#check CLRS.Chapter02.merge_correct

example : CLRS.Chapter02.merge [1, 4, 7] [2, 3, 9] = [1, 2, 3, 4, 7, 9] := by
  decide
```

- [ ] **Step 2: Verify the expected red state**

Run: `lake env lean Tests/Chapter_02_Merge_Interface.lean`

Expected: elaboration fails because `mergeWithCost` and the public MERGE
theorems do not yet exist.

### Task 2: Define the costed executable MERGE

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge/Definitions.lean`

- [ ] **Step 1: Define one execution record**

```lean
structure MergeExecution where
  value : List Nat
  comparisons : Nat
```

- [ ] **Step 2: Define the two-list recursion**

Define `mergeWithCost` by cases on both lists. Empty branches return the
remaining list and zero comparisons. A nonempty branch compares the two heads,
emits the smaller head, recursively consumes that input, and increments the
recursive comparison count. Use `left.length + right.length` as the termination
measure.

- [ ] **Step 3: Add the value projection**

```lean
def merge (left right : List Nat) : List Nat :=
  (mergeWithCost left right).value
```

- [ ] **Step 4: Build only the definition module**

Run:
`lake build CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Definitions`

Expected: build succeeds.

### Task 3: Prove value correctness

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge/Correctness.lean`

- [ ] **Step 1: Prove the projection equation**

```lean
theorem mergeWithCost_value (left right : List Nat) :
    (mergeWithCost left right).value = merge left right := rfl
```

- [ ] **Step 2: Prove preservation properties**

Prove by the generated two-list recursion principle:

```lean
theorem merge_length (left right : List Nat) :
    (merge left right).length = left.length + right.length

theorem merge_perm (left right : List Nat) :
    (merge left right).Perm (left ++ right)
```

- [ ] **Step 3: Prove sortedness**

```lean
theorem merge_sorted {left right : List Nat}
    (hl : left.SortedLE) (hr : right.SortedLE) :
    (merge left right).SortedLE
```

In each recursive branch, use sorted-head lower bounds from `hl` and `hr` to
show that the emitted head is below every element in the recursive output.

- [ ] **Step 4: Build the correctness module**

Run:
`lake build CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Correctness`

Expected: build succeeds without unfinished proof markers.

### Task 4: Prove the linear comparison bound

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge/Cost.lean`

- [ ] **Step 1: Prove the counter bound**

```lean
theorem merge_comparisons_le (left right : List Nat) :
    (mergeWithCost left right).comparisons ≤ left.length + right.length
```

The recursive branch follows from the induction hypothesis because one input
element is consumed at every comparison; empty branches are immediate.

- [ ] **Step 2: Package the public contract**

```lean
theorem merge_correct {left right : List Nat}
    (hl : left.SortedLE) (hr : right.SortedLE) :
    (merge left right).SortedLE ∧
      (merge left right).Perm (left ++ right) ∧
      (mergeWithCost left right).comparisons ≤ left.length + right.length
```

- [ ] **Step 3: Build the cost module**

Run:
`lake build CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Cost`

Expected: build succeeds.

### Task 5: Wire and audit the theorem surface

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms/Merge.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_02.lean`
- Modify: `CLRSLean/Chapter_02.lean`
- Modify: `Tests/Chapter_02_Interface.lean`
- Modify: `Tests/Trust/Chapter_02.lean`
- Modify: `literate.toml`

- [ ] **Step 1: Import the three modules through a facade**

```lean
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Definitions
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Correctness
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge.Cost
```

- [ ] **Step 2: Export and pin the public declarations**

Import the facade from the Section 2.3 guide, add the six `#check` declarations
to `Tests/Chapter_02_Interface.lean`, and add `merge_correct` to
`Tests/Trust/Chapter_02.lean` with `#assert_axioms`.

- [ ] **Step 3: Verify green**

Run:

```text
lake env lean Tests/Chapter_02_Merge_Interface.lean
lake env lean Tests/Chapter_02_Interface.lean
lake env lean Tests/Trust/Chapter_02.lean
lake build CLRSLean.FourthEdition.Chapter_02
```

Expected: all four commands succeed.

### Task 6: Synchronize the reader contract and close the milestone

**Files:**
- Modify: `CLRSLean/FourthEdition/Chapter_02/Section_02_3_Designing_Algorithms.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_02.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/clrs-fourth-edition-map.csv`
- Modify: `literate.toml`
- Modify: `README.md`

- [ ] **Step 1: Replace the stale MERGE gap text**

Document that the explicit list-level MERGE and its linear comparison bound are
proved, while temporary-array allocation and word-RAM instruction accounting
remain outside the current scope.

- [ ] **Step 2: Update generated progress outputs**

Run:

```text
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/gen_readme_table.py
```

- [ ] **Step 3: Run final verification**

```text
lake env lean Tests/Chapter_02_Merge_Interface.lean
lake env lean Tests/Chapter_02_Interface.lean
uv run python scripts/check_v1_trust_gate.py --chapters 2-2
uv run python scripts/check_repository.py
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/FourthEdition/Chapter_02 Tests/Chapter_02_Merge_Interface.lean
git diff --check
```

Expected: builds and repository checks succeed; the source scan reports no
actual unfinished declaration.

- [ ] **Step 4: Commit the independently verified milestone**

```text
git commit -m "feat(ch02): formalize MERGE correctness and linear cost"
```

Then push the branch, merge it into `main`, push `main`, and update issue #313
with the commit and verification evidence. Keep #310 and #314 open for the next
pseudocode-line cost-model milestone.
