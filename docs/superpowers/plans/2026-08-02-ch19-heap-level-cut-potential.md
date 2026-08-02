# Ch19 Heap-Level CUT Potential Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build an executable index-addressed heap-level direct-child CUT and prove its exact change in the Fibonacci-heap potential `t(H) + 2m(H)`.

**Architecture:** Recursive mark accounting belongs to `FHNode`, while the potential consumes a complete `FH`.  A node-level indexed cut removes one child and clears its mark; a heap-level indexed cut replaces the selected parent root and prepends the promoted child.  Strong balance lemmas for list replacement, keys, and marks feed the public invariant and potential theorems.

**Tech Stack:** Lean 4.32, Mathlib, CLRS-Lean `FHNode`/`FH`, Lake, Verso, repository interface and metadata checks.

---

### Task 1: Establish the public interface RED test

**Files:**

- Modify: `Tests/Chapter_19_Interface.lean:1`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Import the executable S1 module**

Add this import beside the current Section 19.1 import:

```lean
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
```

- [ ] **Step 2: Add the wished-for public declarations**

Append these checks after the existing abstract `FibHeap` checks and before the
`FTree` block:

```lean
#check CLRS.Chapter19.FHNode.marks
#check CLRS.Chapter19.FHNode.forestMarks
#check CLRS.Chapter19.FH.cutChildAt
#check CLRS.Chapter19.FH.cutChildAt_keys
#check CLRS.Chapter19.FH.cutChildAt_heapOrdered
#check CLRS.Chapter19.FH.cutChildAt_wellformed
#check CLRS.Chapter19.FH.potential
#check CLRS.Chapter19.FH.potential_makeHeap
#check CLRS.Chapter19.FH.potential_insert
#check CLRS.Chapter19.FH.cutRootChildAt
#check CLRS.Chapter19.FH.cutRootChildAt_keys
#check CLRS.Chapter19.FH.cutRootChildAt_size
#check CLRS.Chapter19.FH.cutRootChildAt_roots_length
#check CLRS.Chapter19.FH.cutRootChildAt_good
#check CLRS.Chapter19.FH.cutRootChildAt_potential_eq
#check CLRS.Chapter19.FH.cutRootChildAt_potential_le
```

- [ ] **Step 3: Run the interface test and verify RED**

Run:

```bash
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: failure on missing `CLRS.Chapter19.FHNode.marks` and the other new
S1 declarations.  Existing interface names must elaborate before the new
missing-name failures.

### Task 2: Repair recursive mark accounting and heap potential

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:74-93`
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:1052-1170`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define recursive node and forest mark counts in `FHNode`**

Place these definitions before `end FHNode`, next to `size` and the forest
summary definitions:

```lean
/-- The number of marked nodes in a subtree, including the root. -/
def marks : FHNode -> Nat
  | node _ marked children =>
      (if marked then 1 else 0) + (children.map marks).sum

/-- The number of marked nodes in a forest. -/
def forestMarks (roots : List FHNode) : Nat :=
  (roots.map marks).sum

@[simp] theorem marks_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).marks =
      (if m then 1 else 0) + (cs.map marks).sum := rfl

@[simp] theorem forestMarks_nil : forestMarks [] = 0 := rfl

@[simp] theorem forestMarks_cons (t : FHNode) (ts : List FHNode) :
    forestMarks (t :: ts) = t.marks + forestMarks ts := by
  simp [forestMarks]
```

- [ ] **Step 2: Replace the root-list draft potential by a heap-level definition**

Remove the duplicate unqualified `forestMarks` draft and use:

```lean
/-- The CLRS Fibonacci-heap potential `t(H) + 2m(H)`. -/
def potential (h : FH) : Int :=
  Int.ofNat h.roots.length +
    2 * Int.ofNat (FHNode.forestMarks h.roots)

theorem potential_nonneg (h : FH) : 0 <= potential h := by
  unfold potential
  positivity

theorem potential_makeHeap : potential makeHeap = 0 := by
  simp [potential, makeHeap]

theorem potential_insert (x : Int) (h : FH) :
    potential (insert x h) = potential h + 1 := by
  simp [potential, insert]
  omega
```

- [ ] **Step 3: Prove the mark-clearing balance equation**

Use addition rather than truncated subtraction as the truth source:

```lean
theorem markFalse_marks_add (t : FHNode) :
    (markFalse t).marks + (if t.marked then 1 else 0) = t.marks := by
  cases t with
  | node k m cs => cases m <;> simp [markFalse]
```

- [ ] **Step 4: Verify the focused source file**

Run:

```bash
lake lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
```

Expected: the namespace/unknown-identifier cascade at lines 1058-1155 is gone;
the interface test still fails only because indexed-cut declarations are absent.

- [ ] **Step 5: Commit the compiler-clean potential foundation**

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
git commit -m "feat(ch19): define executable heap potential"
```

### Task 3: Add the indexed node-level CUT and local invariants

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:930-1052`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define the index-addressed child cut**

Add beside the existing key-directed `cutChild`:

```lean
/-- Remove a direct child by list index and clear the promoted child's mark. -/
def cutChildAt (t : FHNode) (childIndex : Nat) :
    Option (FHNode × FHNode) :=
  match t with
  | FHNode.node k marked children =>
      match children[childIndex]? with
      | none => none
      | some child =>
          some (markFalse child,
            FHNode.node k marked (children.eraseIdx childIndex))
```

- [ ] **Step 2: Prove exact key splitting**

Expose the successful result equation:

```lean
theorem cutChildAt_keys {t cut parent' : FHNode} {i : Nat}
    (hcut : cutChildAt t i = some (cut, parent')) :
    cut.keySet ∪ parent'.keySet = t.keySet
```

Invert `t` and the successful `getElem?` match, obtaining `⟨hi, hchild⟩` from
`List.getElem?_eq_some_iff`.  Rewrite the cut subtree with
`markFalse_keySet`.  Use `List.getElem_cons_eraseIdx_perm hi`, substitute
`hchild`, map the permutation through `FHNode.keysList`, and finish the Finset
membership equality by extensionality.  Do not introduce a key-based lookup.

- [ ] **Step 3: Prove heap order for both returned nodes**

State one bundled theorem:

```lean
theorem cutChildAt_heapOrdered {t cut parent' : FHNode} {i : Nat}
    (hcut : cutChildAt t i = some (cut, parent'))
    (ht : t.HeapOrdered) :
    cut.HeapOrdered ∧ parent'.HeapOrdered
```

Invert `hcut` and the `HeapOrdered.node` constructor.  The selected child's
membership follows from `List.getElem?_eq_some_iff`; apply
`markFalse_heapOrdered` to it.  Build the remaining parent with
`FHNode.HeapOrdered.node`, transporting both child obligations through the
existing `mem_eraseIdx_of_mem` lemma.

- [ ] **Step 4: Prove structural wellformedness for both returned nodes**

State:

```lean
theorem cutChildAt_wellformed {t cut parent' : FHNode} {i : Nat}
    (hcut : cutChildAt t i = some (cut, parent'))
    (ht : t.Wellformed) :
    cut.Wellformed ∧ parent'.Wellformed
```

Invert `FHNode.Wellformed` through `FTree.Wellformed.node`.  Obtain the selected
child's recursive hypothesis from `hall`, transport it through
`markFalse_wellformed`, and reuse `FTree.wellformed_remove_index` plus
`map_eraseIdx` for the remaining parent.  This mirrors the existing
`cutChild_wellformed` proof and adds the missing promoted-child projection.

- [ ] **Step 5: Verify node CUT declarations turn green**

Run:

```bash
lake lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: S1 compiles; the interface advances past all `cutChildAt_*` checks and
fails on the still-missing heap-level CUT declarations.

- [ ] **Step 6: Commit the node-level indexed CUT**

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
git commit -m "feat(ch19): add indexed direct-child cut"
```

### Task 4: Lift CUT to a complete heap state

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:1052`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define the heap-level transition**

```lean
/-- Cut a direct child of an indexed root and promote it into the root list. -/
def cutRootChildAt (h : FH) (rootIndex childIndex : Nat) : Option FH :=
  match h.roots[rootIndex]? with
  | none => none
  | some parent =>
      match cutChildAt parent childIndex with
      | none => none
      | some (cut, parent') =>
          some
            { roots := cut :: h.roots.set rootIndex parent'
            , size := h.size }
```

- [ ] **Step 2: Add list replacement balance helpers**

Prove private/local helpers by induction on `roots` and `rootIndex`, always
using the witness `roots[rootIndex]? = some old`:

```lean
theorem forestKeySet_set_balance {roots : List FHNode} {i : Nat}
    {old new : FHNode} (hget : roots[i]? = some old) :
    FHNode.forestKeySet (roots.set i new) ∪ old.keySet =
      FHNode.forestKeySet roots ∪ new.keySet

theorem forestGood_set {roots : List FHNode} {i : Nat}
    {old new : FHNode} (hget : roots[i]? = some old)
    (hroots : FHNode.ForestGood roots)
    (hnew : new.HeapOrdered ∧ new.Wellformed) :
    FHNode.ForestGood (roots.set i new)
```

The key theorem is a union-balance equation, not an invalid claim that replacing
the parent alone preserves keys.

- [ ] **Step 3: Prove stored size and root-count equations**

```lean
theorem cutRootChildAt_size {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h') :
    h'.size = h.size

theorem cutRootChildAt_roots_length {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h') :
    h'.roots.length = h.roots.length + 1
```

Invert the successful matches.  `List.getElem?_eq_some_iff` gives
`ri < h.roots.length`; simplify with `List.length_set` and the new leading root.

- [ ] **Step 4: Prove key and forest-invariant preservation**

```lean
theorem cutRootChildAt_keys {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h') :
    keys h' = keys h

theorem cutRootChildAt_good {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h')
    (hgood : FHNode.ForestGood h.roots) :
    FHNode.ForestGood h'.roots
```

For keys, combine `cutChildAt_keys` with `forestKeySet_set_balance` and close
finite-set union associativity/commutativity/idempotence by extensionality.  For
`ForestGood`, use `cutChildAt_heapOrdered`, `cutChildAt_wellformed`,
`forestGood_set`, and the leading promoted root.

- [ ] **Step 5: Verify heap-level correctness declarations**

Run:

```bash
lake lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: the interface reaches only the missing potential-equality and
potential-bound declarations.

- [ ] **Step 6: Commit heap-level CUT correctness**

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
git commit -m "feat(ch19): lift direct-child cut to heap state"
```

### Task 5: Prove the exact potential delta

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:1052`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Prove forest mark replacement balance**

```lean
theorem forestMarks_set_add {roots : List FHNode} {i : Nat}
    {old new : FHNode} (hget : roots[i]? = some old) :
    FHNode.forestMarks (roots.set i new) + old.marks =
      FHNode.forestMarks roots + new.marks
```

Prove by induction on `roots` and `i`; each branch reduces with
`FHNode.forestMarks_cons`, while the impossible empty branch contradicts
`hget`.

- [ ] **Step 2: Prove node-cut mark balance**

```lean
theorem cutChildAt_marks_add {parent child cut parent' : FHNode} {i : Nat}
    (hchild : parent.children[i]? = some child)
    (hcut : cutChildAt parent i = some (cut, parent')) :
    cut.marks + parent'.marks + (if child.marked then 1 else 0) =
      parent.marks
```

Invert `parent`, rewrite the successful indexed lookup, use
`markFalse_marks_add`, and prove the erased-list sum balance from
`List.getElem_cons_eraseIdx_perm` after mapping `FHNode.marks`.

- [ ] **Step 3: Prove the heap-level forest mark equation**

First prove the Nat truth source:

```lean
theorem cutRootChildAt_forestMarks_add {h h' : FH}
    {parent child : FHNode} {ri ci : Nat}
    (hparent : h.roots[ri]? = some parent)
    (hchild : parent.children[ci]? = some child)
    (hcut : cutRootChildAt h ri ci = some h') :
    FHNode.forestMarks h'.roots + (if child.marked then 1 else 0) =
      FHNode.forestMarks h.roots
```

Combine `forestMarks_set_add` and `cutChildAt_marks_add`; use `omega` only for
the final Nat reassociation.

- [ ] **Step 4: Prove exact and bounded potential theorems**

```lean
theorem cutRootChildAt_potential_eq {h h' : FH}
    {parent child : FHNode} {ri ci : Nat}
    (hparent : h.roots[ri]? = some parent)
    (hchild : parent.children[ci]? = some child)
    (hcut : cutRootChildAt h ri ci = some h') :
    potential h' = potential h + 1 -
      2 * Int.ofNat (if child.marked then 1 else 0)

theorem cutRootChildAt_potential_le {h h' : FH}
    {parent child : FHNode} {ri ci : Nat}
    (hparent : h.roots[ri]? = some parent)
    (hchild : parent.children[ci]? = some child)
    (hcut : cutRootChildAt h ri ci = some h') :
    potential h' <= potential h + 1
```

Unfold `potential`; rewrite `cutRootChildAt_roots_length` and
`cutRootChildAt_forestMarks_add`; split on `child.marked` and close the two Int
arithmetic branches with `omega`.  Derive the inequality from the exact theorem,
again splitting only the one Boolean mark contribution.

- [ ] **Step 5: Verify the full public interface GREEN**

Run:

```bash
lake lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: both commands exit zero; existing linter warnings may remain.

- [ ] **Step 6: Commit the exact potential theorem**

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean Tests/Chapter_19_Interface.lean
git commit -m "prove(ch19): bound heap-level cut potential"
```

### Task 6: Synchronize the public Chapter 19 boundary

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:1-45`
- Modify: `CLRSLean/Chapter_19.lean:1-159`
- Modify: `CLRSLean/Status.lean:120-124`
- Modify: `docs/proof-map.md:2348-2526`
- Modify: `docs/clrs-proof-progress.csv:20`
- Modify (generated): `CLRSLean/Progress.lean`

- [ ] **Step 1: Correct the S1 and chapter-guide claims**

Change the S1 headline list so it advertises only implemented `FH` operations;
remove the false `FH.extractMin` claim.  Record executable consolidation,
heap-level direct-child CUT, exact one-step potential delta, and the remaining
arbitrary path/cascading-cut and `extractMin` gaps.

- [ ] **Step 2: Update the status and proof map**

Add the public theorem names from Tasks 2-5 and replace statements that say
executable heap forests or consolidation remain entirely absent.  Keep Chapter
19 `partial`; explicitly retain handles, arbitrary paths, cascading cuts,
`extractMin`, global validity, and operation-cost semantics as gaps.

- [ ] **Step 3: Update the progress CSV and regenerate the dashboard**

Update Chapter 19's represented theorem count and summary/gap fields from the
actual declaration list, then run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
```

Expected: CSV validation succeeds and `CLRSLean/Progress.lean` changes only as a
generated consequence of the Chapter 19 row.

- [ ] **Step 4: Run metadata and focused Lean checks**

```bash
uv run python scripts/check_repository.py
lake env lean Tests/Chapter_19_Interface.lean
lake build CLRSLean.Chapter_19
git diff --check
```

Expected: all commands exit zero.

- [ ] **Step 5: Commit synchronized documentation**

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean CLRSLean/Chapter_19.lean CLRSLean/Status.lean docs/proof-map.md docs/clrs-proof-progress.csv CLRSLean/Progress.lean
git commit -m "docs(ch19): record heap-level cut potential proof"
```

### Task 7: Run the full proof and publication gates

**Files:**

- Test: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean`
- Test: `Tests/Chapter_19_Interface.lean`
- Test: repository and Verso gates

- [ ] **Step 1: Check for forbidden proof shortcuts**

```bash
rg -n '\b(sorry|admit|axiom|native_decide)\b' CLRSLean/Chapter_19 Tests/Chapter_19_Interface.lean
```

Expected: no matches in theorem-bearing code.  Matches in explanatory comments
must be inspected rather than counted as proofs.

- [ ] **Step 2: Print axioms of the headline results**

Create a temporary Lean checker outside the repository source tree containing:

```lean
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap

#print axioms CLRS.Chapter19.FH.cutRootChildAt_keys
#print axioms CLRS.Chapter19.FH.cutRootChildAt_good
#print axioms CLRS.Chapter19.FH.cutRootChildAt_potential_eq
#print axioms CLRS.Chapter19.FH.cutRootChildAt_potential_le
```

Run it with `lake env lean`.  Expected: only standard axioms such as
`propext`, `Classical.choice`, and `Quot.sound`; never `sorryAx` or a project
axiom.

- [ ] **Step 3: Run focused, repository, and site builds**

```bash
lake lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
lake env lean Tests/Chapter_19_Interface.lean
uv run python scripts/check_repository.py
lake build CLRSLean
lake build :literateHtml
git diff --check
```

Expected: every command exits zero.  Report linter warnings separately.

- [ ] **Step 4: Review commits and worktree state**

```bash
git status --short --branch
git log --oneline 03abce7..HEAD
```

Expected: clean `codex/ch19-heap-cut`, with the safety draft, design/plan, proof,
interface, and documentation checkpoints visible.
