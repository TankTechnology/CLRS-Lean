# Chapter 18 Exact Executable Deletion Semantics Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` or `superpowers:executing-plans`
> task by task.  Keep the existing structural deletion proof stable; exact
> key semantics belongs in new modules.

**Goal:** Prove that executable `composedDelete` removes exactly one occurrence
of the requested key, lift that result through root normalization, and recover
the usual set-style deletion contract under an orthogonal `UniqueKeys`
assumption.

**Architecture:** Interpret `keysOf` as a multiset `keyBag`.  Prove primitive
conservation equations for leaf removal, merging, rotations, and parent
reassembly.  A single balance-to-erase lemma then lifts a recursive erase
equation through every parent frame.  The main theorem mirrors the reachable
cases of `composedDelete_packet` but performs only semantic accounting; it does
not re-prove structural preservation.  `UniqueKeys` remains separate from
`WellFormed`, because the current model deliberately permits duplicate keys.

**Tech stack:** Lean 4, Mathlib `Multiset`, list permutation/set/splice lemmas,
generated `composedDelete.induct`, existing `NodeWF` repair facts, and
warning-as-error interface tests.

**Prerequisite baseline:** The executable-search integration and the
support-page move to
`CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.Search` must already be
committed, with `scripts/test_literate_config.py`,
`scripts/check_repository.py`, the Search interface, Chapter 18 build, and
the literate build all GREEN.  Do not begin Task 1 from a worktree that still
contains the old sibling `Section_18_1_B_Tree_Search` path.

**Required import DAG:**

```text
WellFormed
  └─ Exact
       ├─ ExactReassembly
       │    ├─ KeyMultiset
       │    ├─ MergeReassembly
       │    └─ RotationReassembly
       └─ ComposedPreservation

KeyMultiset → base Deletion → Insertion → Model.Search → Model
```

`KeyMultiset` and `Exact` must not import `WellFormed`; `Exact` must import
`ComposedPreservation` explicitly so the structural theorem stack remains
available transitively after `WellFormed` changes its import.

---

## Non-negotiable semantic boundary

The specification operation

```lean
delete x tr
```

filters **all** occurrences of `x`, while executable leaf deletion uses
`sortedRemove` and removes only one occurrence.  The current `Sorted` predicate
uses non-strict ordering and `ChildBounded` uses closed bounds, so duplicates
are valid.  For example, `node [1, 1] []` is well formed at minimum degree two;
executable deletion returns one `1`, while specification deletion returns
none.

Therefore the unconditional truth source must be:

```lean
keyBag (composedDelete t x tr) = (keyBag tr).erase x
```

Complete absence of `x` and compatibility with the set-style specification
must be derived only after assuming `UniqueKeys tr`.

---

### Task 1: Lock uniqueness and selected-path routing with a RED test

**Files:**

- Modify: `Tests/Chapter_18_Search_Interface.lean`

- [ ] **Step 1: Add typed contracts before implementation**

```lean
namespace CLRS.Chapter18.BTree

#check (UniqueKeys : BTree → Prop)
#check (WellFormedUnique : Nat → BTree → Prop)

#check (findChild_pos_and_pred_eq_of_mem :
  ∀ {ks : List Nat} {x : Nat},
    List.Pairwise (· ≤ ·) ks → x ∈ ks →
      0 < findChild ks x ∧
        ks[findChild ks x - 1]? = some x)

#check (findChild_not_mem_child_of_ne :
  ∀ {ks : List Nat} {cs : List BTree} {x j : Nat} {child : BTree},
    List.Pairwise (· ≤ ·) ks →
    ChildBounded (node ks cs) →
    x ∉ ks →
    cs[j]? = some child →
    j ≠ findChild ks x →
    x ∉ keysOf child)

#check (findChild_selected_child_mem :
  ∀ {ks : List Nat} {cs : List BTree} {x : Nat} {child : BTree},
    List.Pairwise (· ≤ ·) ks →
    ChildBounded (node ks cs) →
    x ∉ ks →
    cs[findChild ks x]? = some child →
    x ∈ keysOf (node ks cs) →
    x ∈ keysOf child)

end CLRS.Chapter18.BTree
```

- [ ] **Step 2: Confirm RED**

Run:

```bash
lake env lean -DwarningAsError=true Tests/Chapter_18_Search_Interface.lean
```

Expected: missing `UniqueKeys`, `WellFormedUnique`, and the three routing
helpers.  The already-proved search contracts must continue to elaborate.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Tests/Chapter_18_Search_Interface.lean
git commit -m "test(ch18): specify deletion path-routing interface"
```

---

### Task 2: Add orthogonal uniqueness and selected-path helpers

**Files:**

- Modify: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean`
- Modify: `CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/Search.lean`
- Modify: `Tests/Chapter_18_Search_Interface.lean`

- [ ] **Step 1: Define uniqueness without strengthening `WellFormed`**

Place `UniqueKeys` beside `keysOf`/`mem`:

```lean
/-- No represented key occurs more than once anywhere in the tree. -/
def UniqueKeys (tr : BTree) : Prop :=
  (keysOf tr).Nodup
```

Place the bundle immediately after `WellFormed`:

```lean
/-- Structural B-tree well-formedness plus global key uniqueness. -/
def WellFormedUnique (t : Nat) (tr : BTree) : Prop :=
  WellFormed t tr ∧ UniqueKeys tr
```

Do not change the definition of `WellFormed`.

- [ ] **Step 2: Prove a node hit is the selected predecessor**

```lean
theorem findChild_pos_and_pred_eq_of_mem
    {ks : List Nat} {x : Nat}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hx : x ∈ ks) :
    0 < findChild ks x ∧
      ks[findChild ks x - 1]? = some x
```

Use induction on sorted `ks`.  This theorem must handle duplicate separators:
`findChild` points immediately after the final separator not greater than
`x`, so its predecessor is still `x`.

- [ ] **Step 3: Add direct localization wrappers**

```lean
theorem findChild_not_mem_child_of_ne
    {ks : List Nat} {cs : List BTree} {x j : Nat} {child : BTree}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hbounded : ChildBounded (node ks cs))
    (hxkeys : x ∉ ks)
    (hchild : cs[j]? = some child)
    (hne : j ≠ findChild ks x) :
    x ∉ keysOf child

theorem findChild_selected_child_mem
    {ks : List Nat} {cs : List BTree} {x : Nat} {child : BTree}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hbounded : ChildBounded (node ks cs))
    (hxkeys : x ∉ ks)
    (hchild : cs[findChild ks x]? = some child)
    (hx : x ∈ keysOf (node ks cs)) :
    x ∈ keysOf child
```

Both should be short consequences of `findChild_localizes_mem`.  The second
theorem is the routing fact required by direct, rotation, and merge descent.

- [ ] **Step 4: Verify and turn the interface GREEN**

Run:

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/Search.lean
lake build CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.Search
lake env lean -DwarningAsError=true Tests/Chapter_18_Search_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Interface.lean
```

Do not apply warning-as-error directly to the pre-existing Model source in
this task; it has historical linter warnings outside this change.  Building
`Model.Search` refreshes both Model and Search `.olean` files before the
interface checks.

- [ ] **Step 5: Commit**

```bash
git add CLRSLean/Chapter_18/Section_18_1_B_Tree_Model.lean \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/Search.lean \
  Tests/Chapter_18_Search_Interface.lean
git commit -m "feat(ch18): add unique-key and deletion-routing contracts"
```

---

### Task 3: Prove primitive multiset conservation

**Files:**

- Create:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/KeyMultiset.lean`
- Create: `Tests/Chapter_18_KeyMultiset_Interface.lean`

- [ ] **Step 1: Add and commit a missing-module RED interface**

```lean
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.KeyMultiset

namespace CLRS.Chapter18.BTree

#check (keyBag : BTree → Multiset Nat)

#check (keyBag_erase_of_balance :
  ∀ {after before old new : Multiset Nat} {x : Nat},
    after + old = before + new →
    new = old.erase x →
    (x ∈ before → x ∈ old) →
    after = before.erase x)

#check (sortedRemove_keyBag :
  ∀ (x : Nat) (ks : List Nat),
    (↑(sortedRemove x ks) : Multiset Nat) =
      (↑ks : Multiset Nat).erase x)

#check (mergeNodes_keyBag :
  ∀ (left : BTree) (sep : Nat) (right : BTree),
    keyBag (mergeNodes left sep right) =
      keyBag left + {sep} + keyBag right)

#check (rotateRight_keyBag :
  ∀ (left : BTree) (sep : Nat) (right : BTree),
    keyBag (rotateRight left sep right).1 +
        {(rotateRight left sep right).2.1} +
        keyBag (rotateRight left sep right).2.2 =
      keyBag left + {sep} + keyBag right)

#check (rotateLeft_keyBag :
  ∀ (left : BTree) (sep : Nat) (right : BTree),
    keyBag (rotateLeft left sep right).1 +
        {(rotateLeft left sep right).2.1} +
        keyBag (rotateLeft left sep right).2.2 =
      keyBag left + {sep} + keyBag right)

example :
    (↑(keysOf (composedDelete 2 1 (node [1, 1] []))) : Multiset Nat) =
      ({1} : Multiset Nat) := by native_decide

example :
    keysOf (delete 1 (node [1, 1] [])) = [] := by native_decide

end CLRS.Chapter18.BTree
```

Run the interface and confirm RED because `KeyMultiset` is missing, then:

```bash
git add Tests/Chapter_18_KeyMultiset_Interface.lean
git commit -m "test(ch18): specify deletion multiset foundation"
```

- [ ] **Step 2: Define the semantic key bag**

`KeyMultiset.lean` imports only the base
`CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion` module; it must not import
`Invariant`, `Exact`, or `WellFormed`.

```lean
/-- The represented keys of a B-tree, retaining multiplicity and ignoring order. -/
def keyBag (tr : BTree) : Multiset Nat :=
  ↑(keysOf tr)
```

Add `[simp]` membership and node-decomposition lemmas only when they simplify
predictably.  Avoid a broad simp rule that repeatedly expands recursive
`keysOf`.

- [ ] **Step 3: Prove generic balance-to-erase lifting**

```lean
theorem keyBag_erase_of_balance
    {after before old new : Multiset Nat} {x : Nat}
    (hbalance : after + old = before + new)
    (hnew : new = old.erase x)
    (hroute : x ∈ before → x ∈ old) :
    after = before.erase x
```

The proof should split on `x ∈ before` and use routing in the positive branch.
In the negative branch, first derive `x ∉ old`: otherwise
`Multiset.cons_erase` and `hbalance` imply `x ∈ before`.  Only then use
`Multiset.erase_of_notMem` on `before` and `old`.  Use cancellation rather
than element-count case explosions.

- [ ] **Step 4: Prove list/frame balance utilities**

Add exact multiplicity lemmas for:

1. `List.set` with a `getElem?` witness.
2. `take i ++ drop (i + 1)` removing one witnessed element.
3. `children.set i new` under `flatMap keysOf`.
4. Replacing adjacent children by one splice under `flatMap keysOf`.

Prefer existing permutation lemmas:

```lean
List.set_perm_cons_eraseIdx
List.getElem_cons_eraseIdx_perm
List.eraseIdx_eq_take_drop_succ
List.Perm.flatMap
Multiset.coe_eq_coe.mpr
```

Do not introduce a fictitious `repairChild` abstraction; the implementation
uses `List.set`, `take`, and `drop` directly.

- [ ] **Step 5: Prove primitive deletion equations**

```lean
theorem sortedRemove_keyBag (x : Nat) (ks : List Nat) :
    (↑(sortedRemove x ks) : Multiset Nat) =
      (↑ks : Multiset Nat).erase x

theorem mergeNodes_keyBag (left : BTree) (sep : Nat) (right : BTree) :
    keyBag (mergeNodes left sep right) =
      keyBag left + {sep} + keyBag right

theorem rotateRight_keyBag (left : BTree) (sep : Nat) (right : BTree) :
    keyBag (rotateRight left sep right).1 +
        {(rotateRight left sep right).2.1} +
        keyBag (rotateRight left sep right).2.2 =
      keyBag left + {sep} + keyBag right

theorem rotateLeft_keyBag (left : BTree) (sep : Nat) (right : BTree) :
    keyBag (rotateLeft left sep right).1 +
        {(rotateLeft left sep right).2.1} +
        keyBag (rotateLeft left sep right).2.2 =
      keyBag left + {sep} + keyBag right
```

The merge and rotation equations are unconditional and must include their
identity/fallback branches.

Mathlib details:

- use `← Multiset.cons_coe`; there is no `Multiset.coe_cons`;
- `Multiset.coe_add` is oriented from bag addition to list append;
- create independent equalities with `congrArg` before rewriting dependent
  `take/drop/getLast` expressions;
- use `abel` only after the structural equalities have been rewritten.

- [ ] **Step 6: Turn the foundation test GREEN**

Run:

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/KeyMultiset.lean
lake build CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.KeyMultiset
lake env lean -DwarningAsError=true Tests/Chapter_18_KeyMultiset_Interface.lean
git diff --check
```

- [ ] **Step 7: Commit**

```bash
git add \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/KeyMultiset.lean
git commit -m "feat(ch18): prove primitive deletion key-bag equations"
```

---

### Task 4: Lock and prove exact parent reassembly

**Files:**

- Create: `Tests/Chapter_18_Deletion_Reassembly_Interface.lean`
- Create:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ExactReassembly.lean`

- [ ] **Step 1: Add a RED interface for exact parent reassembly**

```lean
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ExactReassembly

namespace CLRS.Chapter18.BTree

#check replaceChild_keyBag_erase
#check replacePredecessor_keyBag_erase
#check replaceSuccessor_keyBag_erase
#check spliceMerged_keyBag_erase
#check rotateRight_reassembly_keyBag_erase
#check rotateLeft_reassembly_keyBag_erase

end CLRS.Chapter18.BTree
```

Run it and confirm RED because `ExactReassembly` does not exist, then commit:

```bash
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Reassembly_Interface.lean
git add Tests/Chapter_18_Deletion_Reassembly_Interface.lean
git commit -m "test(ch18): specify exact deletion reassembly"
```

- [ ] **Step 2: Prove single-child exact replacement**

In `ExactReassembly.lean`, import exactly `KeyMultiset`,
`MergeReassembly`, and `RotationReassembly`.  Prove:

```lean
theorem replaceChild_keyBag_balance ...

theorem replaceChild_keyBag_erase
    (hold : cs[i]? = some old)
    (hroute : x ∈ keysOf (node ks cs) → x ∈ keysOf old)
    (hrec : keyBag new = (keyBag old).erase x) :
    keyBag (node ks (cs.set i new)) =
      (keyBag (node ks cs)).erase x
```

- [ ] **Step 3: Prove separator replacement**

Prove a generic separator-plus-child balance, then:

```lean
theorem replacePredecessor_keyBag_erase ...
theorem replaceSuccessor_keyBag_erase ...
```

Use `NodeWF.child`, `NodeWF.nonRoot_allKeysPos`, `maxKey_mem`/`minKey_mem`,
and `Multiset.cons_erase`.  These branches erase the old separator while the
recursive predecessor/successor erase is cancelled by inserting its value at
the parent.

- [ ] **Step 4: Prove merge splice exactness**

Prove:

```lean
theorem spliceMerged_keyBag_balance ...

theorem spliceMerged_keyBag_erase
    ...
    (hroute :
      x ∈ keysOf (node ks cs) →
        x ∈ keysOf (mergeNodes left sep right))
    (hrec :
      keyBag newMerged =
        (keyBag (mergeNodes left sep right)).erase x) :
    keyBag out = (keyBag (node ks cs)).erase x
```

One indexed theorem should serve separator-hit merge, left merge, and zero
merge by instantiation.

- [ ] **Step 5: Prove rotation conservation and exact reassembly**

First prove adjacent parent balance and pure rotation conservation.  Add the
two provenance directions needed by routing:

```lean
theorem mem_rotateRight_left_of_mem_left ...
theorem mem_rotateLeft_right_of_mem_right ...
```

Then prove:

```lean
theorem rotateRight_reassembly_keyBag_erase ...
theorem rotateLeft_reassembly_keyBag_erase ...
```

The routing premise is about the original selected child; provenance carries
that member into the repaired recursive target.

- [ ] **Step 6: Verify the module**

The reassembly interface must now be GREEN.

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ExactReassembly.lean
lake build CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ExactReassembly
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Reassembly_Interface.lean
git diff --check
```

- [ ] **Step 7: Commit**

```bash
git add \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/ExactReassembly.lean \
  Tests/Chapter_18_Deletion_Reassembly_Interface.lean
git commit -m "feat(ch18): prove exact deletion reassembly"
```

---

### Task 5: Prove raw `composedDelete` erases exactly one occurrence

**Files:**

- Create:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Exact.lean`
- Create: `Tests/Chapter_18_Deletion_Exact_Interface.lean`

- [ ] **Step 1: Add the raw exact-semantics RED interface**

```lean
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Exact

namespace CLRS.Chapter18.BTree

#check (composedDelete_keyBag :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree} {b : Bool}, NodeWF t b tr →
      keyBag (composedDelete t x tr) = (keyBag tr).erase x)

#check (composedDelete_mem_iff_of_ne :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree} {b : Bool}, NodeWF t b tr →
      y ≠ x →
      (mem y (composedDelete t x tr) ↔ mem y tr))

#check (composedDelete_uniqueKeys :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree} {b : Bool}, NodeWF t b tr →
      UniqueKeys tr → UniqueKeys (composedDelete t x tr))

end CLRS.Chapter18.BTree
```

Confirm RED because `Exact` does not exist, then commit:

```bash
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Exact_Interface.lean
git add Tests/Chapter_18_Deletion_Exact_Interface.lean
git commit -m "test(ch18): specify exact executable deletion semantics"
```

- [ ] **Step 2: State the minimal raw theorem**

`Exact.lean` must import both `ExactReassembly` and
`ComposedPreservation`, and must not import `WellFormed`.

```lean
/--
Executable CLRS deletion removes exactly one occurrence of the requested key.
No uniqueness assumption and no top-level `DeleteReady` premise are needed.
-/
theorem composedDelete_keyBag
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree} {b : Bool}
    (hinv : NodeWF t b tr) :
    keyBag (composedDelete t x tr) =
      (keyBag tr).erase x
```

`NodeWF + 2 ≤ t` is the intended minimal contract.  Do not add `UniqueKeys` or
`DeleteReady`.

- [ ] **Step 3: Mirror the existing reachable-case induction**

Use:

```lean
induction x, tr using composedDelete.induct (t := t)
```

The 12 reachable generated cases, grouped into 11 semantic patterns,
correspond to the existing `composedDelete_packet` skeleton:

| Existing case | Semantic action |
|---|---|
| `case1` | `sortedRemove_keyBag` |
| `case2` | predecessor replacement |
| `case3` | successor replacement |
| `case4` | separator-hit merge |
| `case7` | positive-index direct descent |
| `case8` | borrow from left, recurse right |
| `case10` | borrow from right, recurse left |
| `case12`, `case14` | positive-index merge |
| `case29` | zero-index direct descent |
| `case30` | zero-index borrow right |
| `case32` | zero-index merge right |

For positive miss branches, use
`findChild_pos_and_pred_eq_of_mem` together with the observed unequal
predecessor to prove `x ∉ ks`.  For the zero branch, the same theorem shows
that `findChild ks x = 0` implies `x ∉ ks`.  Then use
`findChild_selected_child_mem` to discharge every frame-routing premise.

For malformed lookup branches, reuse the contradiction closure pattern from
`composedDelete_packet`:

```lean
findChild_predecessor_none_absurd
NodeWF.findChild_leftSibling_none_absurd
NodeWF.findChild_none_absurd
NodeWF.children_rel
NodeWF.two_le_children_of_not_empty
```

- [ ] **Step 4: Add exact raw corollaries**

```lean
theorem composedDelete_mem_iff_of_ne
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree} {b : Bool}
    (hinv : NodeWF t b tr) (hyx : y ≠ x) :
    mem y (composedDelete t x tr) ↔ mem y tr

theorem composedDelete_uniqueKeys
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree} {b : Bool}
    (hinv : NodeWF t b tr) (hunique : UniqueKeys tr) :
    UniqueKeys (composedDelete t x tr)
```

- [ ] **Step 5: Verify**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Exact.lean
lake build CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Exact
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Exact_Interface.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Interface.lean
git diff --check
```

The raw exact interface must now be GREEN.

- [ ] **Step 6: Commit**

```bash
git add \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/Exact.lean
git commit -m "feat(ch18): prove exact raw B-tree deletion semantics"
```

---

### Task 6: Lift through root normalization and recover set semantics

**Files:**

- Modify:
  `CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/WellFormed.lean`
- Create: `Tests/Chapter_18_Deletion_Root_Exact_Interface.lean`

- [ ] **Step 1: Add typed root contracts and confirm missing-name RED**

```lean
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.WellFormed

namespace CLRS.Chapter18.BTree

#check (composedDeleteRoot_keyBag :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      keyBag (composedDeleteRoot t x tr) = (keyBag tr).erase x)

#check (composedDeleteRoot_mem_iff_of_ne :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr → y ≠ x →
      (mem y (composedDeleteRoot t x tr) ↔ mem y tr))

#check (composedDeleteRoot_not_mem :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      ¬ mem x (composedDeleteRoot t x tr))

#check (composedDeleteRoot_mem_iff :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      (mem y (composedDeleteRoot t x tr) ↔ y ≠ x ∧ mem y tr))

#check (composedDeleteRoot_wellFormedUnique :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      WellFormedUnique t (composedDeleteRoot t x tr))

#check (composedDeleteRoot_mem_iff_delete :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      (mem y (composedDeleteRoot t x tr) ↔ mem y (delete x tr)))

#check (composedDeleteRoot_search_eq_delete :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      search y (composedDeleteRoot t x tr) = search y (delete x tr))

#check (composedDeleteRoot_correct :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      keyBag (composedDeleteRoot t x tr) = (keyBag tr).erase x ∧
      WellFormed t (composedDeleteRoot t x tr) ∧
      (heightOf (composedDeleteRoot t x tr) = heightOf tr ∨
        heightOf (composedDeleteRoot t x tr) + 1 = heightOf tr))

end CLRS.Chapter18.BTree
```

Run:

```bash
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Root_Exact_Interface.lean
```

Expected: missing root exactness names.  Then commit the RED interface:

```bash
git add Tests/Chapter_18_Deletion_Root_Exact_Interface.lean
git commit -m "test(ch18): specify exact root deletion semantics"
```

- [ ] **Step 2: Make `WellFormed.lean` import `Exact`**

Replace its direct `ComposedPreservation` import by `Exact`; structural
results remain available transitively.

- [ ] **Step 3: Prove root exactness**

```lean
theorem composedDeleteRoot_keyBag
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    keyBag (composedDeleteRoot t x tr) =
      (keyBag tr).erase x
```

This is `composedDelete_keyBag` plus the existing exact list equality
`keysOf_normalizeRoot`.

- [ ] **Step 4: Expose duplicate-aware membership**

```lean
theorem composedDeleteRoot_mem_iff_of_ne
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) (hyx : y ≠ x) :
    mem y (composedDeleteRoot t x tr) ↔ mem y tr
```

This theorem does not require uniqueness.

- [ ] **Step 5: Add the unique-key layer**

```lean
theorem composedDeleteRoot_not_mem
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    ¬ mem x (composedDeleteRoot t x tr)

theorem composedDeleteRoot_mem_iff
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    mem y (composedDeleteRoot t x tr) ↔
      y ≠ x ∧ mem y tr

theorem composedDeleteRoot_wellFormedUnique
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    WellFormedUnique t (composedDeleteRoot t x tr)
```

Use `Multiset.coe_nodup`, `Multiset.Nodup.erase`,
`Multiset.Nodup.notMem_erase`, and
`Multiset.Nodup.mem_erase_iff`.

- [ ] **Step 6: Bridge to the existing specification under uniqueness**

```lean
theorem composedDeleteRoot_mem_iff_delete
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    mem y (composedDeleteRoot t x tr) ↔
      mem y (delete x tr)

theorem composedDeleteRoot_search_eq_delete
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    search y (composedDeleteRoot t x tr) =
      search y (delete x tr)
```

The bridge is deliberately conditional because specification deletion removes
all duplicates.  Its Boolean theorem concerns the compatibility oracle
`search`, not `searchExec`; no executable-search theorem is being claimed for
the structurally flattened specification result.

- [ ] **Step 7: Bundle structural and semantic correctness**

```lean
theorem composedDeleteRoot_correct
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    keyBag (composedDeleteRoot t x tr) =
        (keyBag tr).erase x ∧
      WellFormed t (composedDeleteRoot t x tr) ∧
      (heightOf (composedDeleteRoot t x tr) = heightOf tr ∨
        heightOf (composedDeleteRoot t x tr) + 1 = heightOf tr)
```

Compose the new exact theorem with existing
`composedDeleteRoot_wellFormed` and `composedDeleteRoot_height`.

- [ ] **Step 8: Turn the root exact interface GREEN**

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/WellFormed.lean
lake build CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.WellFormed
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Root_Exact_Interface.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Exact_Interface.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_KeyMultiset_Interface.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Reassembly_Interface.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Search_Interface.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Deletion_Interface.lean
```

- [ ] **Step 9: Commit**

```bash
git add \
  CLRSLean/Chapter_18/Section_18_3_B_Tree_Deletion/WellFormed.lean \
  Tests/Chapter_18_Deletion_Root_Exact_Interface.lean
git commit -m "feat(ch18): expose exact root deletion semantics"
```

---

### Task 7: Register, document, and run the full Chapter 18 regression

**Files:**

- Modify: `CLRSLean/Chapter_18.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/chapters/chapter-18.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify (generated): `CLRSLean/Progress.lean`

- [ ] **Step 1: Register semantic modules**

Add explicit facade imports for:

```lean
CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.KeyMultiset
CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ExactReassembly
CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Exact
```

Register all three in the deletion child-module list and add metadata titles
in `literate.toml`.  Add their exact source paths to the catalog in
`docs/index.md`.

- [ ] **Step 2: Correct the chapter status**

Document separately:

1. structural preservation;
2. unconditional erase-one multiset semantics;
3. unconditional preservation of different-key membership;
4. full deleted-key absence and specification compatibility under
   `WellFormedUnique`.

Do not claim the existing specification and executable operations have equal
tree shape.  Apply the same status correction and new public API list to
`docs/proof-map.md`, which is the theorem-level status source of truth.

Update the Chapter 18 progress CSV row so exact executable deletion is moved
from “remaining” to “proved”.  Keep the chapter `partial`: the real top-level
insertion/root-split theorem and a structural total-key height lower bound
remain separate core groups.  Regenerate the dashboard rather than editing its
row by hand:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
```

- [ ] **Step 3: Run full verification**

```bash
python3 scripts/test_literate_config.py
python3 scripts/check_site_consistency.py
uv run python scripts/check_progress_csv.py --write-dashboard
python3 scripts/check_repository.py
lake build CLRSLean.Chapter_18
lake env lean -DwarningAsError=true Tests/Chapter_18_Search_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_KeyMultiset_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Deletion_Reassembly_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Deletion_Exact_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Deletion_Root_Exact_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Deletion_Interface.lean
lake env lean -DwarningAsError=true Tests/Chapter_18_Root_Occupancy.lean
lake build :literateHtml
git diff --check
```

- [ ] **Step 4: Commit**

```bash
git add CLRSLean/Chapter_18.lean CLRSLean/Progress.lean literate.toml \
  docs/index.md docs/proof-map.md docs/chapters/chapter-18.md \
  docs/clrs-proof-progress.csv
git commit -m "docs(ch18): register exact deletion semantics"
```

---

## Review gates

Every implementation task must pass, in order:

1. implementer self-review and focused verification;
2. spec-compliance review against this plan and the relevant interface test;
3. Lean proof-quality review;
4. fixes and re-review for any Critical or Important issue.

Before claiming the chapter milestone complete, scan all new files for
`sorry`, `admit`, `axiom`, and `sorryAx`, run the full regression above, and
inspect the exact commit range with `git diff --check`.
