# Chapter 18 Search and Path Localization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a genuine separator-guided B-tree search and the selected-child localization theorem needed by exact executable deletion semantics.

**Architecture:** Move the reusable child-index and height helpers out of Section 18.2 into a new upstream Section 18.1 search module. Define `searchExec` as a total recursive function that checks the current node and otherwise follows `findChild`; prove soundness without invariants and completeness from `Sorted + ChildBounded`, then bridge it to the existing specification-level `search`.

**Tech Stack:** Lean 4, Mathlib lists and dependent indexing, CLRSLean `BTree`, Lake interface tests.

---

### Task 1: Lock the public search contract with a failing interface test

**Files:**
- Create: `Tests/Chapter_18_Search_Interface.lean`

- [ ] **Step 1: Add the missing-module RED test**

```lean
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Search

namespace CLRS.Chapter18.BTree

#check findChild
#check findChild_localizes_mem
#check searchExec

#check searchExec_sound :
  ∀ {x : Nat} {tr : BTree}, searchExec x tr = true → mem x tr

#check searchExec_complete :
  ∀ {x : Nat} {tr : BTree}, Sorted tr → ChildBounded tr →
    mem x tr → searchExec x tr = true

#check searchExec_true_iff :
  ∀ {x : Nat} {tr : BTree}, Sorted tr → ChildBounded tr →
    (searchExec x tr = true ↔ mem x tr)

#check searchExec_eq_search :
  ∀ {x : Nat} {tr : BTree}, Sorted tr → ChildBounded tr →
    searchExec x tr = search x tr

example : searchExec 10 (node [10] []) = true := by native_decide
example : searchExec 5 (node [10] [node [5] [], node [15] []]) = true := by native_decide
example : searchExec 15 (node [10] [node [5] [], node [15] []]) = true := by native_decide
example : searchExec 7 (node [10] [node [5] [], node [15] []]) = false := by native_decide
example : searchExec 1 (node [1, 1] []) = true := by native_decide

end CLRS.Chapter18.BTree
```

- [ ] **Step 2: Run the test and confirm the expected failure**

Run:

```bash
lake env lean -DwarningAsError=true Tests/Chapter_18_Search_Interface.lean
```

Expected: failure because `CLRSLean.Chapter_18.Section_18_1_B_Tree_Search` does not exist.

- [ ] **Step 3: Commit the RED test**

```bash
git add Tests/Chapter_18_Search_Interface.lean
git commit -m "test(ch18): specify executable B-tree search interface"
```

### Task 2: Extract reusable path and height helpers upstream

**Files:**
- Create: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Search.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`

- [ ] **Step 1: Create the upstream module with the existing child-index operation**

Move the existing definitions and proofs without changing their statements:

```lean
def findChild : List Nat → Nat → Nat
  | [], _ => 0
  | k :: ks, x => if k ≤ x then findChild ks x + 1 else 0

lemma findChild_le (ks : List Nat) (x : Nat) :
    findChild ks x ≤ ks.length := by
  induction ks with
  | nil => simp [findChild]
  | cons k ks ih =>
      unfold findChild
      split
      · simp only [List.length_cons]
        omega
      · omega
```

Also move, unchanged, the existing proofs named:

```lean
foldl_max_ge
mem_le_foldl_max
foldl_max_le'
foldl_max_heightOf_subset
heightOf_mem_lt
heightOf_le_of_children_subset
findChild_take_le
findChild_drop_gt
findChild_x_hi
findChild_x_lo
```

The new module imports only:

```lean
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model
```

- [ ] **Step 2: Make insertion import the new module and remove duplicate declarations**

Replace the Section 18.2 import with:

```lean
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Search
```

Delete the moved declarations from Section 18.2 so every existing downstream reference resolves to the same names from the upstream module.

- [ ] **Step 3: Verify the refactor preserves the existing insertion and deletion surface**

Run:

```bash
lake build CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion
lake build CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion
lake env lean -DwarningAsError=true Tests/Chapter_18_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Deletion_Interface.lean
```

Expected: all commands succeed; the new search interface still fails only because `searchExec` and its theorems have not yet been added.

- [ ] **Step 4: Commit the dependency refactor**

```bash
git add CLRSLean/Chapter_18/Section_18_1_B_Tree_Search.lean \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
git commit -m "refactor(ch18): move B-tree path helpers upstream"
```

### Task 3: Prove selected-child localization and executable search correctness

**Files:**
- Modify: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Search.lean`
- Test: `Tests/Chapter_18_Search_Interface.lean`

- [ ] **Step 1: Add the localization theorem before implementing search**

Use this public statement:

```lean
theorem findChild_localizes_mem
    {ks : List Nat} {cs : List BTree} {x j : Nat} {child : BTree}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hbounded : ChildBounded (node ks cs))
    (hxkeys : x ∉ ks)
    (hchild : cs[j]? = some child)
    (hxchild : x ∈ keysOf child) :
    j = findChild ks x
```

Prove it by comparing `j` with `findChild ks x`.

- If `j < findChild ks x`, obtain `ks[j] ≤ x` from `findChild_take_le` and `x ≤ ks[j]` from the selected child's upper separator bound; equality contradicts `hxkeys`.
- If `findChild ks x < j`, obtain `ks[j - 1] ≤ x` from the child's lower separator bound and `x < ks[j - 1]` from `findChild_drop_gt`; contradiction.
- The remaining case is equality.

- [ ] **Step 2: Define the total executable search**

```lean
def searchExec (x : Nat) : BTree → Bool
  | node ks cs =>
      if x ∈ ks then
        true
      else
        match hc : cs[findChild ks x]? with
        | some child => searchExec x child
        | none => false
termination_by tr => heightOf tr
decreasing_by
  exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨findChild ks x, hc⟩)
```

- [ ] **Step 3: Prove soundness**

```lean
theorem searchExec_sound {x : Nat} {tr : BTree}
    (hsearch : searchExec x tr = true) :
    mem x tr
```

Induct using `searchExec.induct`; a local hit is in the node key prefix, and a recursive hit is in the selected child and therefore in `children.flatMap keysOf`.

- [ ] **Step 4: Prove completeness from the minimal structural contract**

```lean
theorem searchExec_complete {x : Nat} {tr : BTree}
    (hsorted : Sorted tr) (hbounded : ChildBounded tr)
    (hmem : mem x tr) :
    searchExec x tr = true
```

Induct using `searchExec.induct`.

- If `x ∈ ks`, simplify `searchExec`.
- Otherwise decompose `hmem` through `keysOf` and `List.mem_flatMap`, obtaining a child at index `j`.
- Apply `findChild_localizes_mem` to rewrite `j = findChild ks x`.
- Use the recursive `Sorted` and `ChildBounded` projections for that child and invoke the induction hypothesis.

- [ ] **Step 5: Add the truth-source iff and compatibility bridge**

```lean
theorem searchExec_true_iff {x : Nat} {tr : BTree}
    (hsorted : Sorted tr) (hbounded : ChildBounded tr) :
    searchExec x tr = true ↔ mem x tr :=
  ⟨searchExec_sound, searchExec_complete hsorted hbounded⟩

theorem searchExec_eq_search {x : Nat} {tr : BTree}
    (hsorted : Sorted tr) (hbounded : ChildBounded tr) :
    searchExec x tr = search x tr := by
  apply Bool.eq_iff_iff.mpr
  simpa [search_true_iff] using searchExec_true_iff hsorted hbounded
```

If `Bool.eq_iff_iff` is not the available Mathlib lemma, prove Boolean equality by cases on both values and use `searchExec_true_iff` plus `search_true_iff`.

- [ ] **Step 6: Run the focused RED-to-GREEN test and existing regression tests**

Run:

```bash
lake env lean -DwarningAsError=true Tests/Chapter_18_Search_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Deletion_Interface.lean
```

Expected: all pass.

- [ ] **Step 7: Commit executable search**

```bash
git add CLRSLean/Chapter_18/Section_18_1_B_Tree_Search.lean \
  Tests/Chapter_18_Search_Interface.lean
git commit -m "feat(ch18): prove separator-guided B-tree search"
```

### Task 4: Register and expose the new module

**Files:**
- Modify: `CLRSLean/Chapter_18.lean`
- Modify: `literate.toml`
- Modify: `docs/chapters/chapter-18.md`

- [ ] **Step 1: Import the search module from the chapter facade**

Add:

```lean
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Search
```

immediately after the model import.

- [ ] **Step 2: Register the module in `literate.toml`**

Add the module beside the existing Section 18.1 model and Section 18.2 insertion entries, including its module metadata block following the existing Chapter 18 pattern.

- [ ] **Step 3: Correct the chapter status text**

Document that:

- `search` remains the specification oracle for compatibility;
- `searchExec` is the executable separator-guided algorithm;
- `searchExec_true_iff` is the semantic truth source;
- `findChild_localizes_mem` is shared by search and exact deletion semantics.

- [ ] **Step 4: Run the full Chapter 18 verification**

Run:

```bash
lake build CLRSLean.Chapter_18
lake env lean -DwarningAsError=true Tests/Chapter_18_Search_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Deletion_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Root_Occupancy.lean
```

Expected: all commands succeed with no new warnings in the focused interface files.

- [ ] **Step 5: Commit integration**

```bash
git add CLRSLean/Chapter_18.lean literate.toml docs/chapters/chapter-18.md
git commit -m "docs(ch18): register executable B-tree search"
```
