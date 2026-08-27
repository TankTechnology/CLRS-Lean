# Chapter 35 Costed APPROX-SUBSET-SUM Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the unsupported Chapter 35 FPTAS runtime prose with a costed APPROX-SUBSET-SUM execution whose value, approximation guarantee, and polynomial work bound are all kernel checked.

**Architecture:** Keep the existing semantic section unchanged and add four small child modules behind a `Costed` facade.  Local recursive scans produce counters, the outer execution composes those counters, and a final bounds module transports the existing separated-list argument to the actual execution.

**Tech Stack:** Lean 4.32, Mathlib lists/Finsets/real logarithms, existing `CLRS.ApproxSubsetSum` semantics and approximation theorems.

---

### Task 1: Pin the public costed interface in a failing test

**Files:**
- Create: `Tests/Chapter_35_Costed_SubsetSum_Interface.lean`

- [ ] **Step 1: Add the public theorem checks before production code exists**

```lean
import CLRSLean.FourthEdition.Chapter_35

#check CLRS.ApproxSubsetSum.mergeWithCost_value
#check CLRS.ApproxSubsetSum.mergeWithCost_work_le
#check CLRS.ApproxSubsetSum.trimWithCost_value
#check CLRS.ApproxSubsetSum.trimWithCost_work_le
#check CLRS.ApproxSubsetSum.approxListsWithCost_value
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_value
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_work_le
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_fptas
```

- [ ] **Step 2: Run the focused interface and record the intended RED state**

Run:

```text
lake env lean Tests/Chapter_35_Costed_SubsetSum_Interface.lean
```

Expected: the existing Chapter 35 declarations elaborate and each new costed
name is reported as unknown.

### Task 2: Define the local recursive executions

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_35/Section_35_5_The_Subset_Sum_Problem/Costed/Definitions.lean`
- Test: `Tests/Chapter_35_Costed_SubsetSum_Interface.lean`

- [ ] **Step 1: Define result records and the five scans**

The definitions module imports only the original Section 35.5 file and adds:

```lean
structure ListExecution where
  value : List Nat
  work : Nat

structure NatExecution where
  value : Nat
  work : Nat

def mapAddWithCost (x : Nat) : List Nat -> ListExecution
  | [] => ⟨[], 0⟩
  | y :: ys =>
      let rest := mapAddWithCost x ys
      ⟨y + x :: rest.value, rest.work + 1⟩

def mergeWithCost : List Nat -> List Nat -> ListExecution
  | [], ys => ⟨ys, 0⟩
  | xs, [] => ⟨xs, 0⟩
  | x :: xs, y :: ys =>
      if x <= y then
        let rest := mergeWithCost xs (y :: ys)
        ⟨x :: rest.value, rest.work + 1⟩
      else
        let rest := mergeWithCost (x :: xs) ys
        ⟨y :: rest.value, rest.work + 1⟩
termination_by L M => L.length + M.length

def trimAuxWithCost (delta : Real) : Nat -> List Nat -> ListExecution
  | _last, [] => ⟨[], 0⟩
  | last, y :: ys =>
      if (1 + delta) * (last : Real) < (y : Real) then
        let rest := trimAuxWithCost delta y ys
        ⟨y :: rest.value, rest.work + 1⟩
      else
        let rest := trimAuxWithCost delta last ys
        ⟨rest.value, rest.work + 1⟩

def trimWithCost (delta : Real) : List Nat -> ListExecution
  | [] => ⟨[], 0⟩
  | y :: ys =>
      let rest := trimAuxWithCost delta y ys
      ⟨y :: rest.value, rest.work⟩

def filterAtMostWithCost (t : Nat) : List Nat -> ListExecution
  | [] => ⟨[], 0⟩
  | y :: ys =>
      let rest := filterAtMostWithCost t ys
      if y <= t then
        ⟨y :: rest.value, rest.work + 1⟩
      else
        ⟨rest.value, rest.work + 1⟩

def maximumAuxWithCost (best : Nat) : List Nat -> NatExecution
  | [] => ⟨best, 0⟩
  | y :: ys =>
      let rest := maximumAuxWithCost (max best y) ys
      ⟨rest.value, rest.work + 1⟩

def maximumWithCost (xs : List Nat) : NatExecution :=
  maximumAuxWithCost 0 xs
```

`trimAuxWithCost`, filtering, and maximum selection must recurse over the
actual input tail and increment by one exactly where the specified comparison
is made.

- [ ] **Step 2: Elaborate only the definitions module**

Run:

```text
lake env lean CLRSLean/FourthEdition/Chapter_35/Section_35_5_The_Subset_Sum_Problem/Costed/Definitions.lean
```

Expected: success without new linter warnings.

### Task 3: Prove local erasure and linear work

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_35/Section_35_5_The_Subset_Sum_Problem/Costed/LocalCorrectness.lean`

- [ ] **Step 1: Prove the map and merge contracts**

Provide these results by structural or well-founded induction over the same
recursion used by the executions:

```lean
theorem mapAddWithCost_value (x : Nat) (L : List Nat) :
  (mapAddWithCost x L).value = L.map (fun y => y + x)

theorem mapAddWithCost_work (x : Nat) (L : List Nat) :
  (mapAddWithCost x L).work = L.length

theorem mergeWithCost_value (L M : List Nat) :
  (mergeWithCost L M).value = merge L M

theorem mergeWithCost_length (L M : List Nat) :
  (mergeWithCost L M).value.length = L.length + M.length

theorem mergeWithCost_work_le (L M : List Nat) :
  (mergeWithCost L M).work <= L.length + M.length
```

- [ ] **Step 2: Prove the trim, filter, and maximum contracts**

```lean
theorem trimWithCost_value (delta : Real) (L : List Nat) :
  (trimWithCost delta L).value = trim delta L

theorem trimWithCost_work_le (delta : Real) (L : List Nat) :
  (trimWithCost delta L).work <= L.length

theorem trimWithCost_length_le (delta : Real) (L : List Nat) :
  (trimWithCost delta L).value.length <= L.length

theorem filterAtMostWithCost_value (t : Nat) (L : List Nat) :
  (filterAtMostWithCost t L).value = L.filter (fun y => y <= t)

theorem filterAtMostWithCost_work (t : Nat) (L : List Nat) :
  (filterAtMostWithCost t L).work = L.length

theorem maximumWithCost_value (L : List Nat) :
  (maximumWithCost L).value = L.foldl max 0

theorem maximumWithCost_work (L : List Nat) :
  (maximumWithCost L).work = L.length
```

- [ ] **Step 3: Add concrete regression examples and elaborate the module**

The focused test should include examples equivalent to:

```lean
example : (mergeWithCost [1, 3, 5] [2, 4]).value = [1, 2, 3, 4, 5] := by decide
example : (mergeWithCost [1, 3, 5] [2, 4]).work = 4 := by decide
example : (filterAtMostWithCost 3 [0, 2, 5]).work = 3 := by decide
```

Run only `LocalCorrectness.lean` and the focused interface until both are green
for the local declarations.

### Task 4: Compose the costed outer execution

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_35/Section_35_5_The_Subset_Sum_Problem/Costed/Execution.lean`

- [ ] **Step 1: Define the outer list execution from local stages**

```lean
def approxListsWithCost (delta : Real) (t : Nat) : List Nat -> ListExecution
  | [] => ⟨[0], 0⟩
  | x :: xs =>
      let prior := approxListsWithCost delta t xs
      let shifted := mapAddWithCost x prior.value
      let merged := mergeWithCost prior.value shifted.value
      let trimmed := trimWithCost delta merged.value
      let kept := filterAtMostWithCost t trimmed.value
      ⟨kept.value,
        prior.work + shifted.work + merged.work + trimmed.work + kept.work + 1⟩
```

- [ ] **Step 2: Prove outer erasure**

```lean
theorem approxListsWithCost_value (delta : Real) (t : Nat) (xs : List Nat) :
  (approxListsWithCost delta t xs).value = approxLists delta t xs
```

The proof rewrites only through the five local erasure theorems; it must not
re-prove the semantic approximation invariant.

- [ ] **Step 3: Define and identify the returned maximum**

```lean
def approxSubsetSumWithCost (xs : List Nat) (t : Nat) (epsilon : Real) : NatExecution :=
  let lists := approxListsWithCost (epsilon / (2 * (xs.length : Real))) t xs
  let answer := maximumWithCost lists.value
  ⟨answer.value, lists.work + answer.work⟩

theorem approxSubsetSumWithCost_value (xs : List Nat) (t : Nat) (epsilon : Real) :
  (approxSubsetSumWithCost xs t epsilon).value = approxSum xs t epsilon
```

Prove the value theorem by showing the recursive maximum scan is both an upper
bound for every list member and a member when `0` is present, then use the
characterization of `Finset.max'` already used by `approxSum`.

- [ ] **Step 4: Elaborate only `Execution.lean` and rerun the interface**

Expected: all value checks are green; the total-work and bundle checks remain
red because `Bounds.lean` does not exist yet.

### Task 5: Prove intermediate and total work bounds

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_35/Section_35_5_The_Subset_Sum_Problem/Costed/Bounds.lean`

- [ ] **Step 1: Prove the fixed-parameter intermediate-list bound**

For positive original length `n`, prove for every list `ys`:

```lean
theorem approxLists_uniform_length_bound
    (hn : 0 < n) (h_epsilon_pos : 0 < epsilon)
    (h_epsilon_one : epsilon <= 1) (h_target : 1 <= t) (ys : List Nat) :
  ((approxLists (epsilon / (2 * (n : Real))) t ys).length : Real) <=
    4 * (n : Real) * Real.log (t : Real) / epsilon + 2
```

This must instantiate `approxLists_length_bound` at the one `delta` selected
from the original `n`; applying the old `approxSubsetSum_fptas` to `ys` would
silently change `delta` and is not accepted.

- [ ] **Step 2: Prove a generic outer recurrence bound**

Let every semantic intermediate list have real length at most `B`.  Induction
over `xs`, combined with local work and erasure, proves:

```lean
theorem approxListsWithCost_work_le_of_length_bound
    (hB : 0 <= B)
    (hbound : ∀ ys, ((approxLists delta t ys).length : Real) <= B) :
  ((approxListsWithCost delta t xs).work : Real) <=
    (xs.length : Real) * (7 * B + 1)
```

- [ ] **Step 3: Derive the public edge-safe polynomial bound**

Split on `xs = []`; for the nonempty case instantiate the preceding two
lemmas and include the final maximum scan.  Prove:

```lean
theorem approxSubsetSumWithCost_work_le
    (h_epsilon_pos : 0 < epsilon) (h_epsilon_one : epsilon <= 1)
    (h_target : 1 <= t) :
  ((approxSubsetSumWithCost xs t epsilon).work : Real) <=
    48 * ((xs.length : Real) + 1) ^ 2 *
      (Real.log (t : Real) + 1) / epsilon
```

The final arithmetic must use the execution recurrence and the existing
list-size theorem.  Do not replace the left-hand side with a separately defined
closed-form cost.

- [ ] **Step 4: Bundle correctness, approximation, and work**

```lean
theorem approxSubsetSumWithCost_fptas
    (h_epsilon_pos : 0 < epsilon) (h_epsilon_one : epsilon <= 1)
    (h_target : 1 <= t) :
  let run := approxSubsetSumWithCost xs t epsilon
  run.value ∈ subsetSums xs ∧
  run.value <= t ∧
  (optimalSum xs t : Real) <= (1 + epsilon) * (run.value : Real) ∧
  (run.work : Real) <=
    48 * ((xs.length : Real) + 1) ^ 2 *
      (Real.log (t : Real) + 1) / epsilon
```

Use `approxSubsetSumWithCost_value`, `approxSum_mem_subsetSums`,
`approxSum_le_t`, `approxSubsetSum_approx_lt`, and the new work theorem.

- [ ] **Step 5: Elaborate `Bounds.lean` and make the focused interface green**

Run only the new bounds module and
`Tests/Chapter_35_Costed_SubsetSum_Interface.lean` during iteration.

### Task 6: Publish, audit, and checkpoint the closure

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_35/Section_35_5_The_Subset_Sum_Problem/Costed.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_35.lean`
- Modify: `Tests/Trust/Chapter_35.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/audits/2026-08-28-whole-book-proof-gap-audit.md`
- Modify generated progress/readme files through repository scripts.

- [ ] **Step 1: Add the facade and canonical import**

The facade imports `Definitions`, `LocalCorrectness`, `Execution`, and `Bounds`.
The Chapter 35 guide imports the facade after the original Section 35.5 import,
describes the unit-cost boundary, and names
`approxSubsetSumWithCost_fptas` as Theorem 35.8's runtime closure.

- [ ] **Step 2: Add trust evidence**

```lean
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_value
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_work_le
#check CLRS.ApproxSubsetSum.approxSubsetSumWithCost_fptas

#assert_axioms CLRS.ApproxSubsetSum.approxSubsetSumWithCost_value
#assert_axioms CLRS.ApproxSubsetSum.approxSubsetSumWithCost_work_le
#assert_axioms CLRS.ApproxSubsetSum.approxSubsetSumWithCost_fptas
```

- [ ] **Step 3: Update the live ledger and dated audit closure log**

Add three tracked Chapter 35 groups: costed local scans, outer erasure, and the
execution-derived polynomial FPTAS bundle.  Regenerate the dashboard and README
and update the hand-written whole-book snapshot to the resulting total.

- [ ] **Step 4: Run the proportional final gate**

```text
lake env lean <each new source file>
lake build CLRSLean.FourthEdition.Chapter_35
lake env lean Tests/Chapter_35_Costed_SubsetSum_Interface.lean
lake env lean Tests/Trust/Chapter_35.lean
lake build CLRSLean.Audit.Axioms
python3 scripts/check_repository.py
git diff --check
```

Expected: all commands succeed, no new warning is emitted by the costed files,
the ledger reports all selected entries proved, and the public trust surface
uses only the allowed Lean/Mathlib axioms.

- [ ] **Step 5: Commit, push, and close issue #341**

```text
git commit -m "feat(ch35): prove costed subset-sum fptas"
git push origin codex/whole-book-proof-closure
gh issue close 341 --comment "Closed by the costed APPROX-SUBSET-SUM proof batch."
```

Close the issue only after the exact verification output has been recorded.
