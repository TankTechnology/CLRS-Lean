# Chapter 19 Executable Extract-Min Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement an executable Fibonacci-heap `extractMin` that selects a minimum root, promotes its children, invokes the proved degree-bucket consolidation, removes exactly one minimum occurrence from a multiset key model, and preserves a concrete heap validity invariant.

**Architecture:** Add multiplicity-preserving key bags, real forest size, and a root-mark invariant beside the existing `FHNode` summaries.  A recursive stable `removeMinRoot` supplies a selected root plus a permutation certificate for the remaining roots.  `FH.extractMin` clears promoted-root marks, appends the remaining roots, calls `consolidateList`, and is verified by composing selector, promotion, and strengthened consolidation lemmas.

**Tech Stack:** Lean 4.32, Mathlib `List`/`Multiset`/`Finset`, CLRS-Lean `FHNode`/`FH`/`FTree`, Lake, Verso, repository interface and metadata checks.

---

### Task 1: Establish the executable extract-min public-interface RED test

**Files:**

- Modify: `Tests/Chapter_19_Interface.lean:106-122`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Add the wished-for public declarations**

Append the following checks after the existing executable CUT checks and before
the `FTree` checks:

```lean
#check CLRS.Chapter19.FHNode.keyBag
#check CLRS.Chapter19.FHNode.forestKeyBag
#check CLRS.Chapter19.FHNode.forestSize
#check CLRS.Chapter19.FHNode.RootsUnmarked
#check CLRS.Chapter19.FH.keyBag
#check CLRS.Chapter19.FH.Represents
#check CLRS.Chapter19.FH.Valid
#check CLRS.Chapter19.FH.makeHeap_valid
#check CLRS.Chapter19.FH.insert_valid
#check CLRS.Chapter19.FH.union_valid
#check CLRS.Chapter19.FH.removeMinRoot
#check CLRS.Chapter19.FH.removeMinRoot_none_iff
#check CLRS.Chapter19.FH.removeMinRoot_perm
#check CLRS.Chapter19.FH.removeMinRoot_min
#check CLRS.Chapter19.FHNode.consolidateList_keyBag
#check CLRS.Chapter19.FHNode.consolidateList_forestSize
#check CLRS.Chapter19.FHNode.consolidateList_rootsUnmarked
#check CLRS.Chapter19.FH.extractMin
#check CLRS.Chapter19.FH.extractMin_correct
#check CLRS.Chapter19.FH.extractMin_keyBag
#check CLRS.Chapter19.FH.extractMin_valid
#check CLRS.Chapter19.FH.extractMin_degreeStrict
#check CLRS.Chapter19.FH.extractMin_size
#check CLRS.Chapter19.FH.extractMin_minimum
#check CLRS.Chapter19.FH.extractMin_mem_iff_of_ne
#check CLRS.Chapter19.FH.extractMin_none_iff
#check CLRS.Chapter19.FH.extractMin_none_iff_size_zero
```

- [ ] **Step 2: Run the interface test and verify RED**

Run:

```bash
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: all existing 128 public declarations elaborate, followed by
`unknownIdentifier` failures beginning at `FHNode.keyBag`.  The failure must be
caused by the missing new interface, not by an import or syntax error.

### Task 2: Add exact summaries and the executable heap invariant

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:74-140`
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:626-720`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define node/forest key bags, forest size, and root marks**

Place these definitions beside `keysList`, `forestKeySet`, and `forestMarks`:

```lean
/-- The keys of one subtree with multiplicity. -/
def keyBag (t : FHNode) : Multiset Int :=
  ↑t.keysList

/-- The keys of a root forest with multiplicity. -/
def forestKeyBag (roots : List FHNode) : Multiset Int :=
  ↑(roots.flatMap FHNode.keysList)

/-- The actual number of nodes represented by a root forest. -/
def forestSize (roots : List FHNode) : Nat :=
  (roots.map FHNode.size).sum

/-- Every root has the CLRS root mark `false`. -/
def RootsUnmarked (roots : List FHNode) : Prop :=
  ∀ root ∈ roots, root.marked = false
```

Add exact normalization lemmas:

```lean
theorem keyBag_node (k : Int) (m : Bool) (cs : List FHNode) :
    keyBag (node k m cs) = {k} + forestKeyBag cs

theorem forestKeyBag_nil : forestKeyBag [] = 0

theorem forestKeyBag_cons (t : FHNode) (ts : List FHNode) :
    forestKeyBag (t :: ts) = t.keyBag + forestKeyBag ts

theorem forestKeyBag_append (xs ys : List FHNode) :
    forestKeyBag (xs ++ ys) = forestKeyBag xs + forestKeyBag ys

theorem forestSize_nil : forestSize [] = 0

theorem forestSize_cons (t : FHNode) (ts : List FHNode) :
    forestSize (t :: ts) = t.size + forestSize ts

theorem forestSize_append (xs ys : List FHNode) :
    forestSize (xs ++ ys) = forestSize xs + forestSize ys

theorem size_eq_one_add_forestSize (t : FHNode) :
    t.size = 1 + forestSize t.children
```

Use `Multiset.coe_add`, `List.flatMap_append`, list induction, and `simp` on
`FHNode.size`.  Do not convert the bag theorem through `Finset`, since that
would discard multiplicity.

- [ ] **Step 2: Define the heap abstraction and validity invariant**

Add inside `namespace FH` after `keys`:

```lean
/-- The executable heap's exact key multiset. -/
def keyBag (h : FH) : Multiset Int :=
  FHNode.forestKeyBag h.roots

/-- Exact multiset representation for the executable heap. -/
def Represents (h : FH) (bag : Multiset Int) : Prop :=
  h.keyBag = bag

/-- Structural, root-mark, and stored-size validity. -/
def Valid (h : FH) : Prop :=
  FHNode.ForestGood h.roots ∧
  FHNode.RootsUnmarked h.roots ∧
  h.size = FHNode.forestSize h.roots
```

Add the projection bridge:

```lean
theorem keys_eq_keyBag_toFinset (h : FH) :
    h.keys = h.keyBag.toFinset
```

Prove it by rewriting `forestKeySet_eq_flatMap`, unfolding both heap summaries,
and using `Multiset.mem_toFinset` under extensionality.

- [ ] **Step 3: Make the invariant constructible**

Add these public theorems:

```lean
theorem makeHeap_valid : makeHeap.Valid

theorem insert_valid (x : Int) (h : FH) (hvalid : h.Valid) :
    (insert x h).Valid

theorem union_valid (h₁ h₂ : FH)
    (hvalid₁ : h₁.Valid) (hvalid₂ : h₂.Valid) :
    (union h₁ h₂).Valid
```

For `insert_valid`, use `leaf_heapOrdered`, `leaf_wellformed`, the false mark of
the singleton root, and `forestSize_cons`.  For `union_valid`, split membership
through `List.mem_append` for both `ForestGood` and `RootsUnmarked`, then use
`forestSize_append` and the stored-size equalities.

- [ ] **Step 4: Verify and commit the foundation**

Run:

```bash
lake env lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
lake build CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: the source compiles; interface checks through `FH.union_valid` turn
green and the first remaining failure is `FH.removeMinRoot`.

Commit only the compiler-clean source foundation, leaving the interface RED for
the next task:

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
git commit -m "feat(ch19): define executable heap validity"
```

### Task 3: Implement stable minimum-root removal

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:720`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define the stable recursive selector**

Add beside `minimum` and before the CUT section:

```lean
/-- Remove the leftmost minimum-key root. -/
def removeMinRoot : List FHNode → Option (FHNode × List FHNode)
  | [] => none
  | x :: xs =>
      match removeMinRoot xs with
      | none => some (x, [])
      | some (y, rest) =>
          if x.key ≤ y.key then some (x, xs)
          else some (y, x :: rest)
```

- [ ] **Step 2: Prove totality and permutation truth sources**

Add:

```lean
theorem removeMinRoot_none_iff (roots : List FHNode) :
    removeMinRoot roots = none ↔ roots = []

theorem removeMinRoot_perm {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    (z :: rest).Perm roots
```

Prove both by induction on `roots`, splitting the recursive result and the key
comparison.  In the branch that keeps the head, the permutation is reflexive;
in the branch that selects from the tail, use `List.Perm.cons` followed by a
single swap to move `z` in front of the original head.

- [ ] **Step 3: Derive bag, size, membership, and invariant projections**

From `removeMinRoot_perm`, add:

```lean
theorem removeMinRoot_keyBag {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    FHNode.forestKeyBag roots = z.keyBag + FHNode.forestKeyBag rest

theorem removeMinRoot_forestSize {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    FHNode.forestSize roots = z.size + FHNode.forestSize rest

theorem removeMinRoot_good {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest))
    (hgood : FHNode.ForestGood roots) :
    z.HeapOrdered ∧ z.Wellformed ∧ FHNode.ForestGood rest

theorem removeMinRoot_rootsUnmarked {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest))
    (hunmarked : FHNode.RootsUnmarked roots) :
    z.marked = false ∧ FHNode.RootsUnmarked rest
```

Map the permutation through `FHNode.keysList` for the bag equation, map it
through `FHNode.size` and apply `List.Perm.sum_eq` for size, and transport
pointwise predicates through `removeMinRoot_perm.mem_iff` for the invariant
facts.

- [ ] **Step 4: Prove minimum-root order**

Add the public selector theorem:

```lean
theorem removeMinRoot_min {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    ∀ root ∈ roots, z.key ≤ root.key
```

Use the same structural induction as the definition.  When the head wins, use
the recursive minimum theorem and `x.key ≤ y.key`; when the tail wins, use the
negated comparison to obtain `y.key ≤ x.key` and reuse the recursive theorem
for tail roots.

- [ ] **Step 5: Verify and commit the selector**

Run the narrow source build and interface test.  Expected: selector checks turn
green and the first remaining interface failure is
`FHNode.consolidateList_keyBag`.

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
git commit -m "feat(ch19): select and remove a minimum root"
```

### Task 4: Strengthen LINK and CONSOLIDATE for bag, size, and root marks

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:226-623`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Prove LINK's exact summaries**

Add beside the existing `link_keys` and `link_size` theorems:

```lean
theorem link_keyBag (x y : FHNode) :
    (link x y).keyBag = x.keyBag + y.keyBag

theorem link_marked_false (x y : FHNode)
    (hx : x.marked = false) (hy : y.marked = false) :
    (link x y).marked = false
```

For `link_keyBag`, unfold `link`, split `x.key ≤ y.key`, reduce node bags with
`keyBag_node`, and finish the swapped-parent branch with commutativity and
associativity of multiset addition.  `link_marked_false` is a two-branch
simplification using the mark of whichever root becomes the parent.

- [ ] **Step 2: Lift bag and real size through bucket insertion**

Add:

```lean
theorem insertConsolidated_keyBag (ys : List FHNode) (x : FHNode) :
    forestKeyBag (insertConsolidated ys x) = forestKeyBag ys + x.keyBag

theorem insertConsolidated_forestSize (ys : List FHNode) (x : FHNode) :
    forestSize (insertConsolidated ys x) = forestSize ys + x.size
```

Follow the existing `insertConsolidated_keys` case split.  In the equal-degree
branch use `link_keyBag` or `link_size`; in the ordering branches normalize
with `forestKeyBag_cons` or `forestSize_cons` and close commutative arithmetic
with `abel` or `omega`.

- [ ] **Step 3: Preserve the root-mark invariant through consolidation**

Add:

```lean
theorem insertConsolidated_rootsUnmarked (ys : List FHNode) (x : FHNode)
    (hys : RootsUnmarked ys) (hx : x.marked = false) :
    RootsUnmarked (insertConsolidated ys x)

theorem consolidateList_rootsUnmarked : ∀ roots : List FHNode,
    RootsUnmarked roots → RootsUnmarked (consolidateList roots)
```

Induct through `insertConsolidated`; the only nontrivial branch uses
`link_marked_false`.  Then mirror `consolidateList_good`, projecting the head
and tail root-mark facts before invoking bucket insertion.

- [ ] **Step 4: Publish strengthened consolidation theorems**

Add:

```lean
theorem consolidateList_keyBag : ∀ roots : List FHNode,
    forestKeyBag (consolidateList roots) = forestKeyBag roots

theorem consolidateList_forestSize : ∀ roots : List FHNode,
    forestSize (consolidateList roots) = forestSize roots
```

Both are direct inductions using the matching `insertConsolidated_*` theorem.

- [ ] **Step 5: Verify and commit strengthened consolidation**

Run the source build and interface test.  Expected: all consolidation checks
turn green and the first missing identifier is `FH.extractMin`.

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
git commit -m "prove(ch19): strengthen consolidate accounting"
```

### Task 5: Implement extract-min and prove exact correctness

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:720-960`
- Test: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Prove promotion preservation helpers**

Add reusable facts:

```lean
theorem markFalse_keyBag (t : FHNode) :
    (markFalse t).keyBag = t.keyBag

theorem markFalse_size (t : FHNode) :
    (markFalse t).size = t.size

theorem children_forestGood (t : FHNode)
    (hordered : t.HeapOrdered) (hwellformed : t.Wellformed) :
    FHNode.ForestGood t.children

theorem map_markFalse_forestGood (roots : List FHNode)
    (hgood : FHNode.ForestGood roots) :
    FHNode.ForestGood (roots.map markFalse)

theorem map_markFalse_rootsUnmarked (roots : List FHNode) :
    FHNode.RootsUnmarked (roots.map markFalse)

theorem map_markFalse_forestKeyBag (roots : List FHNode) :
    FHNode.forestKeyBag (roots.map markFalse) =
      FHNode.forestKeyBag roots

theorem map_markFalse_forestSize (roots : List FHNode) :
    FHNode.forestSize (roots.map markFalse) = FHNode.forestSize roots
```

Project child heap order directly from `HeapOrdered.node`.  For child
wellformedness, expose the recursive `FTree.Wellformed.node` hypotheses through
`toFTree`.  The mapped-forest theorems are list inductions using the existing
`markFalse_heapOrdered`, `markFalse_wellformed`, and the new bag/size facts.

- [ ] **Step 2: Lift heap order from a root to every key in its subtree**

Add:

```lean
theorem FHNode.heapOrdered_key_le_of_mem_keyBag {t : FHNode} {y : Int}
    (hordered : t.HeapOrdered) (hy : y ∈ t.keyBag) :
    t.key ≤ y

theorem removeMinRoot_min_key {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest))
    (hgood : FHNode.ForestGood roots) :
    ∀ y ∈ FHNode.forestKeyBag roots, z.key ≤ y
```

The subtree theorem is structural recursion over `HeapOrdered`: split bag
membership between the node singleton and child forest, obtain the containing
child, use the parent-child key inequality, and compose with the recursive
hypothesis.  The forest theorem obtains the containing root from the flattened
bag, applies `removeMinRoot_min`, and then the subtree theorem.

- [ ] **Step 3: Define the executable transition**

Add after `removeMinRoot` and its proof block:

```lean
/-- Executable CLRS `FIB-HEAP-EXTRACT-MIN`. -/
def extractMin (h : FH) : Option (Int × FH) :=
  match removeMinRoot h.roots with
  | none => none
  | some (z, rest) =>
      let promoted := z.children.map markFalse
      let roots' := FHNode.consolidateList (promoted ++ rest)
      some
        (z.key,
          { roots := roots'
          , size := h.size - 1 })
```

- [ ] **Step 4: Prove the bundled correctness theorem**

Add:

```lean
theorem extractMin_correct {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    x ∈ h.keyBag ∧
    (∀ y ∈ h.keyBag, x ≤ y) ∧
    h'.keyBag = h.keyBag.erase x ∧
    h'.Valid ∧
    FHNode.DegreeStrict h'.roots
```

Invert the successful `removeMinRoot` result and substitute `x`/`h'`.

- Membership and minimum order come from `removeMinRoot_keyBag` and
  `removeMinRoot_min_key`.
- For exact deletion, rewrite the selected node bag with `keyBag_node`; show
  `h.keyBag = {x} + h'.keyBag` using promotion, append, and consolidation bag
  preservation; finish with `Multiset.erase_cons_head`.
- For `Valid`, combine selector `ForestGood` projections,
  `children_forestGood`, mapped promotion, append closure, and
  `consolidateList_good`; combine root-mark projection, mapped false marks,
  append closure, and `consolidateList_rootsUnmarked`; combine the additive
  forest-size split, node-size equation, promotion preservation, and
  `consolidateList_forestSize`, closing the final Nat equation with `omega`.
- Degree strictness is exactly `consolidateList_degreeStrict`.

- [ ] **Step 5: Add direct wrappers and minimum compatibility**

Add:

```lean
theorem extractMin_keyBag {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h'.keyBag = h.keyBag.erase x

theorem extractMin_valid {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h'.Valid

theorem extractMin_degreeStrict {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    FHNode.DegreeStrict h'.roots

theorem extractMin_size {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h'.size + 1 = h.size

theorem extractMin_minimum {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h.minimum = some x

theorem extractMin_mem_iff_of_ne {h h' : FH} {x y : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h'))
    (hyx : y ≠ x) :
    y ∈ h'.keys ↔ y ∈ h.keys
```

Prove the first three by projection.  Prove size from the successful transition
plus nonempty valid real size.  For `extractMin_minimum`, transfer membership
and lower bounds from `keyBag` to `keys` with `keys_eq_keyBag_toFinset`, then
identify `Finset.min'`.  For different-key membership, rewrite both Finset
views through bags, use `extractMin_keyBag`, and apply
`Multiset.mem_erase_of_ne hyx`.

- [ ] **Step 6: Prove empty-result specifications**

Add:

```lean
theorem extractMin_none_iff (h : FH) :
    extractMin h = none ↔ h.roots = []

theorem extractMin_none_iff_size_zero (h : FH) (hvalid : h.Valid) :
    extractMin h = none ↔ h.size = 0
```

The first theorem unfolds the transition and uses `removeMinRoot_none_iff`.
For the second, prove by list cases that `forestSize roots = 0 ↔ roots = []`,
using `FHNode.size`'s positive leading `1`, and rewrite with the `Valid` stored
size equation.

- [ ] **Step 7: Verify the complete public interface GREEN and commit**

Run:

```bash
lake env lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
lake build CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
lake env lean Tests/Chapter_19_Interface.lean
git diff --check
```

Expected: all commands exit zero; existing linter warnings may remain.

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean Tests/Chapter_19_Interface.lean
git commit -m "feat(ch19): prove executable extract-min"
```

### Task 6: Synchronize the Chapter 19 public boundary

**Files:**

- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean:1-55`
- Modify: `CLRSLean/Chapter_19.lean:1-180`
- Modify: `CLRSLean/Status.lean:120-135`
- Modify: `docs/proof-map.md:2348-2560`
- Modify: `docs/clrs-proof-progress.csv:20`
- Modify: `CLRSLean/Progress.lean` (generated)

- [ ] **Step 1: Update executable-module and chapter claims**

Record the exact bag representation, `FH.Valid`, minimum-root selector,
consolidation call inside `extractMin`, exact `Multiset.erase`, and invariant
preservation.  Remove `extractMin` from the remaining gap.  Retain cached min
pointer, handles/paths, cascading cuts, executable decrease/delete, duplicate
handle identity, actual cost semantics, and circular pointers as explicit gaps.

- [ ] **Step 2: Add the new public declarations to the proof map and count**

Add exactly the 27 interface checks from Task 1 to the Chapter 19 theorem list.
Update the tracked/proved count from `128/128` to `155/155`; keep the chapter
status `partial` and the remaining core-group count `1`.

- [ ] **Step 3: Regenerate and validate progress metadata**

Run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/check_repository.py
lake build CLRSLean.Chapter_19
git diff --check
```

Expected: the generated dashboard reports 155 Chapter 19 entries and 1552
repository-wide tracked/proved entries, repository checks pass, and the chapter
module builds.

- [ ] **Step 4: Commit synchronized documentation**

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean CLRSLean/Chapter_19.lean CLRSLean/Status.lean docs/proof-map.md docs/clrs-proof-progress.csv CLRSLean/Progress.lean
git commit -m "docs(ch19): record executable extract-min proof"
```

### Task 7: Run full proof and publication gates

**Files:**

- Test: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean`
- Test: `Tests/Chapter_19_Interface.lean`
- Test: repository and Verso gates

- [ ] **Step 1: Check for forbidden proof shortcuts**

```bash
rg -n '\b(sorry|admit|axiom|native_decide)\b' CLRSLean/Chapter_19 Tests/Chapter_19_Interface.lean
```

Expected: no matches in theorem-bearing code.

- [ ] **Step 2: Print headline axioms**

Run:

```bash
lake env lean --stdin <<'EOF'
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
#print axioms CLRS.Chapter19.FH.removeMinRoot_min
#print axioms CLRS.Chapter19.FHNode.consolidateList_keyBag
#print axioms CLRS.Chapter19.FH.extractMin_correct
#print axioms CLRS.Chapter19.FH.extractMin_minimum
EOF
```

Expected: only standard axioms such as `propext`, `Classical.choice`, and
`Quot.sound`; never `sorryAx` or a project axiom.

- [ ] **Step 3: Run final verification**

```bash
lake env lean Tests/Chapter_19_Interface.lean
uv run python scripts/check_repository.py
lake build CLRSLean
lake build :literateHtml
git diff --check
git status --short --branch
```

Expected: both Lean builds, the interface, repository checks, and publication
target exit zero; the feature worktree is clean on
`codex/ch19-heap-cut`.
