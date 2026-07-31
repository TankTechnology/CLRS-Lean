# Chapter 18 Top-Level B-Tree Insertion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement and prove the real CLRS top-level B-tree insertion that splits a full root before calling the already-proved `insertNonFull`.

**Architecture:** Keep the existing flat `insert` as the specification layer.  Add `splitRoot` as the one-child transient-root application of `splitChild`, prove a dedicated full-root invariant bridge without weakening `Occupancy`, then define `insertRoot` by a full/non-full branch and derive its semantic/query wrappers from one key-permutation theorem.

**Tech Stack:** Lean 4, Mathlib, Lake, CLRS-Lean `BTree` model, chapter-local interface tests.

---

## File Map

- Modify `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
  - owns `splitRoot`, `insertRoot`, the transient full-root bridge, structural
    correctness, exact key-list permutation, height, uniqueness, and query
    wrappers;
  - must not import Chapter 18.3 deletion modules.
- Create `Tests/Chapter_18_Insertion_Interface.lean`
  - freezes the public operation/theorem surface;
  - contains small full-leaf executable regressions.
- Modify `CLRSLean/Chapter_18.lean`
  - lists the new real top-level insertion results and removes top-level
    insertion from the remaining-work sentence.
- Modify `docs/chapters/chapter-18.md`
  - documents the executable/specification boundary and exact assumptions.
- Modify `docs/proof-map.md`
  - records the new public theorem family.
- Modify `docs/clrs-proof-progress.csv`
  - increments represented/proved theorem counts by the exact number of new
    tracked public contracts and leaves the height theorem as the only core
    gap.

## Task 1: Freeze the public insertion contract

**Files:**

- Create: `Tests/Chapter_18_Insertion_Interface.lean`

- [ ] **Step 1: Add the RED interface test**

Create the file with this contract:

```lean
import CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion

namespace CLRS.Chapter18.BTree

#check (splitRoot : Nat → BTree → BTree)
#check (insertRoot : Nat → Nat → BTree → BTree)

#check (splitRoot_keys_perm :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, rootKeyCount tr = 2 * t - 1 →
      (keysOf (splitRoot t tr)).Perm (keysOf tr))

#check (splitRoot_wellFormed :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      rootKeyCount tr = 2 * t - 1 →
      WellFormed t (splitRoot t tr))

#check (splitRoot_height :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      rootKeyCount tr = 2 * t - 1 →
      heightOf (splitRoot t tr) = heightOf tr + 1)

#check (splitRoot_rootKeyCount :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, rootKeyCount tr = 2 * t - 1 →
      rootKeyCount (splitRoot t tr) = 1)

#check (splitRoot_nonFull :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, rootKeyCount tr = 2 * t - 1 →
      rootKeyCount (splitRoot t tr) < 2 * t - 1)

#check (insertRoot_keys_perm :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (keysOf (insertRoot t x tr)).Perm (keysOf tr ++ [x]))

#check (insertRoot_wellFormed :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      WellFormed t (insertRoot t x tr))

#check (insertRoot_height :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      heightOf (insertRoot t x tr) =
        if rootKeyCount tr = 2 * t - 1 then heightOf tr + 1
        else heightOf tr)

#check (insertRoot_mem_iff :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (mem y (insertRoot t x tr) ↔ y = x ∨ mem y tr))

#check (insertRoot_wellFormedUnique :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      ¬ mem x tr →
      WellFormedUnique t (insertRoot t x tr))

#check (insertRoot_mem_iff_insert :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (mem y (insertRoot t x tr) ↔ mem y (insert x tr)))

#check (insertRoot_search_eq_insert :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      search y (insertRoot t x tr) = search y (insert x tr))

#check (insertRoot_searchExec_true_iff :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (searchExec y (insertRoot t x tr) = true ↔ y = x ∨ mem y tr))

#check (insertRoot_correct :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (keysOf (insertRoot t x tr)).Perm (keysOf tr ++ [x]) ∧
      WellFormed t (insertRoot t x tr) ∧
      (heightOf (insertRoot t x tr) = heightOf tr ∨
        heightOf (insertRoot t x tr) = heightOf tr + 1))

example :
    rootKeyCount (splitRoot 2 (node [1, 2, 3] [])) = 1 := by
  native_decide

example :
    heightOf (insertRoot 2 4 (node [1, 2, 3] [])) = 1 := by
  native_decide

example :
    searchExec 4 (insertRoot 2 4 (node [1, 2, 3] [])) = true := by
  native_decide

end CLRS.Chapter18.BTree
```

- [ ] **Step 2: Run the interface and verify RED**

Run:

```bash
lake env lean -DwarningAsError=true Tests/Chapter_18_Insertion_Interface.lean
```

Expected: failure at the first `splitRoot` reference with an unknown-identifier
error.  If it fails earlier for a syntax/import error, fix the test and rerun
until the failure is caused by the missing public operation.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Tests/Chapter_18_Insertion_Interface.lean
git commit -m "test(ch18): specify top-level B-tree insertion"
```

## Task 2: Define the operations and prove exact root-split shape/content

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
- Test: `Tests/Chapter_18_Insertion_Interface.lean`

- [ ] **Step 1: Add the executable definitions after `rootKeyCount`**

Add:

```lean
/-- Split a full B-tree root by wrapping it in a transient empty parent. -/
def splitRoot (t : Nat) (tr : BTree) : BTree :=
  splitChild t (node [] [tr]) 0

/-- CLRS `B-TREE-INSERT`: split a full root, then insert into a non-full root. -/
def insertRoot (t x : Nat) (tr : BTree) : BTree :=
  if rootKeyCount tr = 2 * t - 1 then
    insertNonFull t x (splitRoot t tr)
  else
    insertNonFull t x tr
```

- [ ] **Step 2: Prove the full-root expansion**

For `tr = node ks cs`, prove an internal expansion lemma:

```lean
lemma splitRoot_full_eq
    (t : Nat) (ht : 2 ≤ t) (ks : List Nat) (cs : List BTree)
    (hfull : ks.length = 2 * t - 1) :
    splitRoot t (node ks cs) =
      node [ks[t - 1]'(by omega)]
        [node (ks.take (t - 1)) (cs.take t),
         node (ks.drop t) (cs.drop t)]
```

Unfold `splitRoot` and apply `splitChild_full_eq` with parent keys `[]`,
parent children `[node ks cs]`, and child index `0`.  Discharge the singleton
lookup and length facts with `simp`.

- [ ] **Step 3: Prove key preservation and root-key count**

Add:

```lean
theorem splitRoot_keys_perm
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hfull : rootKeyCount tr = 2 * t - 1) :
    (keysOf (splitRoot t tr)).Perm (keysOf tr)

lemma splitRoot_rootKeyCount
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hfull : rootKeyCount tr = 2 * t - 1) :
    rootKeyCount (splitRoot t tr) = 1

lemma splitRoot_nonFull
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hfull : rootKeyCount tr = 2 * t - 1) :
    rootKeyCount (splitRoot t tr) < 2 * t - 1
```

For `splitRoot_keys_perm`, destruct `tr`, unfold `splitRoot`, invoke
`splitChild_keys_perm` at index `0`, and simplify
`keysOf (node [] [node ks cs])` to `keysOf (node ks cs)`.  Derive the latter
two lemmas from `splitRoot_full_eq` and `2 ≤ t`.

- [ ] **Step 4: Run the narrow source check**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
```

Expected: PASS.  The interface remains RED only for the not-yet-added
structural and top-level theorems.

- [ ] **Step 5: Commit operation/content groundwork**

```bash
git add CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
git commit -m "feat(ch18): add full-root insertion operations"
```

## Task 3: Prove the full-root structural bridge

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
- Test: `Tests/Chapter_18_Insertion_Interface.lean`

- [ ] **Step 1: Prove a full root can become a non-root child**

Add the internal lemma:

```lean
lemma occupancy_false_of_full_root
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hcb : ChildBounded tr)
    (hocc : Occupancy t true tr)
    (hfull : rootKeyCount tr = 2 * t - 1) :
    Occupancy t false tr
```

Destruct `tr`.  Use `child_children_len_of_full_cb` to split the child-list
case into empty or length `2 * t`.  Reuse the recursive occupancy component
from `hocc`; prove the non-root key and child lower bounds by arithmetic.

- [ ] **Step 2: Build transient-wrapper component lemmas**

Prove internal lemmas with these conclusions:

```lean
Sorted tr → Sorted (node [] [tr])
ChildBounded tr → ChildBounded (node [] [tr])
SameDepth tr → SameDepth (node [] [tr])
```

The first two unfold their predicates and simplify the singleton parent.  The
same-depth lemma is `SameDepth.internal [] tr []` with vacuous sibling
hypotheses.

- [ ] **Step 3: Prove split-root occupancy**

Add:

```lean
lemma splitRoot_occupancy
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hcb : ChildBounded tr)
    (hocc : Occupancy t true tr)
    (hfull : rootKeyCount tr = 2 * t - 1) :
    Occupancy t true (splitRoot t tr)
```

Destruct the old root and rewrite with `splitRoot_full_eq`.  Convert the old
root to non-root occupancy using `occupancy_false_of_full_root`, then reuse
`occupancy_left_half` and `occupancy_right_half`.  Construct root occupancy
directly: one key, two children, upper bounds from `2 ≤ t`, and the two
non-root child proofs.

- [ ] **Step 4: Prove `splitRoot_wellFormed`**

For `Sorted`, `ChildBounded`, and `SameDepth`, construct the transient wrapper
component hypotheses and invoke the corresponding existing
`splitChild_preserves_*` theorem at child index `0`.  Derive the full child's
leaf/internal size disjunction from `child_children_len_of_full_cb`.  Combine
those results with `splitRoot_occupancy`.

The public theorem must have exactly this signature:

```lean
theorem splitRoot_wellFormed
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr)
    (hfull : rootKeyCount tr = 2 * t - 1) :
    WellFormed t (splitRoot t tr)
```

- [ ] **Step 5: Prove `splitRoot_height`**

Destruct the old root and rewrite with `splitRoot_full_eq`.  Use
`heightOf_split_parts_eq` to show both split halves have the old root's height,
then reduce the new two-child root with `heightOf_uniform_children`.

```lean
theorem splitRoot_height
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr)
    (hfull : rootKeyCount tr = 2 * t - 1) :
    heightOf (splitRoot t tr) = heightOf tr + 1
```

- [ ] **Step 6: Verify source and the split-root portion of the interface**

Run:

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Insertion_Interface.lean
```

Expected: the source passes.  The interface advances past all `splitRoot`
checks and remains RED at the first missing `insertRoot_*` theorem.

- [ ] **Step 7: Commit the structural bridge**

```bash
git add CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
git commit -m "feat(ch18): prove full-root split invariants"
```

## Task 4: Prove top-level insertion correctness

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
- Test: `Tests/Chapter_18_Insertion_Interface.lean`

- [ ] **Step 1: Prove exact key contents**

Add `insertRoot_keys_perm` with the interface signature from Task 1.
Split on:

```lean
by_cases hfull : rootKeyCount tr = 2 * t - 1
```

In the full branch, rewrite `insertRoot`, apply
`insertNonFull_keys_perm` to `splitRoot`, and compose its permutation with
`splitRoot_keys_perm` appended by `[x]`.  Obtain `ChildBounded (splitRoot t tr)`
from `splitRoot_wellFormed`.  In the non-full branch, apply
`insertNonFull_keys_perm` directly to `hwf.2.1`.

- [ ] **Step 2: Prove structural preservation**

Add `insertRoot_wellFormed` with the interface signature from Task 1.

- Full branch: use `splitRoot_wellFormed`, `splitRoot_nonFull`, and
  `insertNonFull_wellFormed`.
- Non-full branch: obtain strict non-fullness from the `Occupancy` upper bound
  plus `hfull`; then apply `insertNonFull_wellFormed`.

- [ ] **Step 3: Prove the precise height equation**

Add `insertRoot_height` with the interface signature from Task 1.

- Full branch: chain `insertNonFull_height` on the well-formed split root with
  `splitRoot_height`.
- Non-full branch: apply `insertNonFull_height` to the original
  `ChildBounded` and `SameDepth` components.

- [ ] **Step 4: Prove membership and the bundled capstone**

Derive `insertRoot_mem_iff` from `insertRoot_keys_perm.mem_iff`,
`List.mem_append`, and `List.mem_singleton`.

Add `insertRoot_correct` by combining:

```lean
insertRoot_keys_perm
insertRoot_wellFormed
insertRoot_height
```

Split the height equation on the fullness condition to produce the public
same-or-one-higher disjunction.

- [ ] **Step 5: Verify GREEN through the core capstone**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Insertion_Interface.lean
```

Expected: the source passes.  The interface advances through
`insertRoot_mem_iff` and remains RED at
`insertRoot_wellFormedUnique`.

- [ ] **Step 6: Commit the core capstone**

```bash
git add CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
git commit -m "feat(ch18): prove top-level insertion correctness"
```

## Task 5: Add uniqueness and query/specification wrappers

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
- Test: `Tests/Chapter_18_Insertion_Interface.lean`

- [ ] **Step 1: Prove uniqueness preservation**

Add `insertRoot_wellFormedUnique` with the interface signature from Task 1.
Its structural component is `insertRoot_wellFormed`.  For `UniqueKeys`, prove
`(keysOf tr ++ [x]).Nodup` from the old `UniqueKeys` and `¬ mem x tr`, then
transport it through `(insertRoot_keys_perm ...).nodup_iff`.

- [ ] **Step 2: Add the specification membership/search bridge**

Add:

```lean
theorem insertRoot_mem_iff_insert ...
theorem insertRoot_search_eq_insert ...
```

The first is the transitive composition of `insertRoot_mem_iff` and
`insert_mem_iff`.  The second applies `Bool.eq_iff_iff.mpr` and rewrites both
searches with `search_true_iff`.

- [ ] **Step 3: Add executable-search correctness**

Add `insertRoot_searchExec_true_iff` with the interface signature from Task 1.
Obtain output `Sorted` and `ChildBounded` from
`insertRoot_wellFormed`, apply `searchExec_true_iff`, then rewrite membership
with `insertRoot_mem_iff`.

- [ ] **Step 4: Run the complete insertion gate**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Insertion_Interface.lean
lake build CLRSLean.Chapter_18
```

Expected: all commands pass, including the three executable full-leaf
regressions.

- [ ] **Step 5: Commit the ergonomic public surface**

```bash
git add CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
git commit -m "feat(ch18): expose insertion query and uniqueness contracts"
```

## Task 6: Register and document top-level insertion

**Files:**

- Modify: `CLRSLean/Chapter_18.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean`
- Modify: `docs/chapters/chapter-18.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Test: `Tests/Chapter_18_Insertion_Interface.lean`

- [ ] **Step 1: Update reader-facing theorem lists**

Document `splitRoot`, `insertRoot`, their two structural/content capstones,
the exact height equation, membership/spec compatibility,
`WellFormedUnique`, executable search, and `insertRoot_correct`.

State explicitly:

- the old `insert` remains the flat specification operation;
- executable/specification compatibility is extensional, not tree-shape
  equality;
- uniqueness requires `¬ mem x tr`;
- top-level insertion is complete for the functional correctness model;
- the only remaining Chapter 18 core theorem group is the structural key-count
  lower bound and logarithmic height wrapper.

- [ ] **Step 2: Update tracked theorem counts exactly**

Count the newly listed public contracts in the interface and update the Chapter
18 CSV row by that exact number.  Run:

```bash
python3 scripts/check_progress_csv.py
```

Expected: PASS.

- [ ] **Step 3: Run the Chapter 18 completion gate**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
lake env lean -DwarningAsError=true CLRSLean/Chapter_18.lean
lake build CLRSLean.Chapter_18
for f in Tests/Chapter_18*.lean; do
  lake env lean -DwarningAsError=true "$f" || exit 1
done
python3 scripts/check_progress_csv.py
git diff --check
```

Scan theorem-bearing Chapter 18 Lean files with the repository's
comment/string-aware unfinished-marker checker, or run:

```bash
python3 scripts/check_repository.py
```

Do not run `lake build :literateHtml`.

- [ ] **Step 4: Commit insertion integration**

```bash
git add \
  CLRSLean/Chapter_18.lean \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean \
  docs/chapters/chapter-18.md \
  docs/proof-map.md \
  docs/clrs-proof-progress.csv
git commit -m "docs(ch18): register top-level insertion correctness"
```

## Task 7: Review the insertion milestone

**Files:**

- Review every commit from the RED interface through documentation integration.

- [ ] **Step 1: Run specification-compliance review**

Check every requirement in
`docs/superpowers/specs/2026-07-31-ch18-top-level-insertion-design.md` against
the implementation and public interface.  Reject missing assumptions, hidden
shape-equality claims, import cycles, or a transient tree advertised as
`WellFormed`.

- [ ] **Step 2: Run code-quality review**

Inspect theorem dependency direction, duplicated full-root expansions,
unnecessarily strong hypotheses, brittle simp scripts, naming consistency, and
reader-facing documentation.

- [ ] **Step 3: Re-run affected gates after review fixes**

Run the Task 6 Chapter 18 completion gate after every review-driven change.
Commit review fixes separately with a message describing the corrected
contract or proof issue.

- [ ] **Step 4: Hand off to the independent height-bound plan**

Only after all insertion checks and reviews pass, create a separate design and
implementation plan for:

```lean
2 * t ^ heightOf tr ≤ totalKeys tr + 1
heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2)
```

with an explicit legal-empty-root branch.
