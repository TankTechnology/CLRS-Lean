# Chapter 19 Cascading Cuts and Amortized Costs Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the persistent executable Fibonacci heap with arbitrary-node CUT, CASCADING-CUT, decrease-key, delete, cached minimum, and explicit CLRS potential-method cost bounds.

**Architecture:** Strengthen the existing executable `FHNode` invariant with mark-aware degree slack, extend `FH` with a cached minimum-root index, and add an occurrence path plus zipper layer that represents an already-dereferenced CLRS node handle.  Keep structural algorithms in `S2_CascadingCuts.lean`; keep cost instrumentation, degree/root bounds, and trace theorems in `S3_AmortizedCosts.lean`.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib, Lake, `List`/`Multiset` forest semantics, Chapter 17 `PotentialTrace`, Verso documentation.

---

### Task 1: Add the public failure surface for the full executable heap

**Files:**
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Add failing public checks**

Append these declarations after the existing `FH.extractMin_none_iff_size_zero` check:

```lean
#check CLRS.Chapter19.FHNode.LossInvariant
#check CLRS.Chapter19.FHNode.ForestLossInvariant
#check CLRS.Chapter19.FHNode.lossInvariant_wellformed
#check CLRS.Chapter19.FH.MinRootValid
#check CLRS.Chapter19.FH.minimum_cached
#check CLRS.Chapter19.FHPath
#check CLRS.Chapter19.FHFrame
#check CLRS.Chapter19.FHCursor
#check CLRS.Chapter19.FH.openPath
#check CLRS.Chapter19.FH.openPath_close
#check CLRS.Chapter19.FH.cutAtPath
#check CLRS.Chapter19.FH.cutAtPath_correct
#check CLRS.Chapter19.FH.cascadingCut
#check CLRS.Chapter19.FH.cascadingCut_correct
#check CLRS.Chapter19.FH.decreaseKeyAt
#check CLRS.Chapter19.FH.decreaseKeyAt_correct
#check CLRS.Chapter19.FH.deleteAt
#check CLRS.Chapter19.FH.deleteAt_correct
#check CLRS.Chapter19.FH.Costed.consolidate
#check CLRS.Chapter19.FH.Costed.extractMin
#check CLRS.Chapter19.FH.Costed.decreaseKeyAt
#check CLRS.Chapter19.FH.Costed.deleteAt
#check CLRS.Chapter19.FH.Costed.decreaseKey_amortized_le_three
#check CLRS.Chapter19.FH.Costed.extractMin_amortized_le_log
#check CLRS.Chapter19.FH.Costed.delete_amortized_le_log
#check CLRS.Chapter19.FH.Costed.run_totalCost_le
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: failure at the first check with unknown identifier
`CLRS.Chapter19.FHNode.LossInvariant`; all existing checks before it remain
accepted.

- [ ] **Step 3: Commit the red interface**

```bash
git add Tests/Chapter_19_Interface.lean
git commit -m "test(ch19): specify cascading-cut and cost interface"
```

### Task 2: Prove the mark-aware loss invariant

**Files:**
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define the recursive invariant next to `Wellformed`**

```lean
def LossInvariant : FHNode -> Prop
  | node _ _ children =>
      (forall (j : Nat) (hj : j < children.length),
        j - (if children[j].marked then 1 else 0) <= children[j].degree) /\
      forall child ∈ children, child.LossInvariant

def ForestLossInvariant (roots : List FHNode) : Prop :=
  forall root ∈ roots, root.LossInvariant
```

- [ ] **Step 2: Prove projection and local constructors**

Add and prove these exact statements:

```lean
theorem lossInvariant_wellformed (t : FHNode) :
    t.LossInvariant -> t.Wellformed

theorem leaf_lossInvariant (k : Int) :
    (node k false []).LossInvariant

theorem markFalse_lossInvariant (t : FHNode) :
    t.LossInvariant -> (markFalse t).LossInvariant

theorem link_lossInvariant (x y : FHNode)
    (hx : x.LossInvariant) (hy : y.LossInvariant)
    (hxmark : x.marked = false) (hymark : y.marked = false)
    (hdegree : x.degree = y.degree) :
    (link x y).LossInvariant
```

The `lossInvariant_wellformed` proof performs structural recursion.  In the
child-degree goal, split on `child.marked`; the unmarked branch strengthens
`j - 1 <= j`, while the marked branch is the stored bound.

- [ ] **Step 3: Lift through consolidation**

Add and prove:

```lean
theorem insertConsolidated_lossInvariant (roots : List FHNode) (x : FHNode)
    (hroots : ForestLossInvariant roots) (hx : x.LossInvariant)
    (hunmarked : RootsUnmarked roots) (hxmark : x.marked = false) :
    ForestLossInvariant (insertConsolidated roots x)

theorem consolidateList_lossInvariant (roots : List FHNode)
    (hloss : ForestLossInvariant roots)
    (hunmarked : RootsUnmarked roots) :
    ForestLossInvariant (consolidateList roots)
```

Use `link_lossInvariant` in the equal-degree branch and the existing
`insertConsolidated_rootsUnmarked` theorem to retain the root premise across
recursive links.

- [ ] **Step 4: Run focused GREEN checks**

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
lake env lean Tests/Chapter_19_Interface.lean
```

Expected: the three loss-invariant checks pass; the interface now fails first
at `FH.MinRootValid`.

- [ ] **Step 5: Commit**

```bash
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean Tests/Chapter_19_Interface.lean
git commit -m "feat(ch19): add mark-aware Fibonacci loss invariant"
```

### Task 3: Cache the minimum root and strengthen `FH.Valid`

**Files:**
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Extend the heap and define cache validity**

Change the structure and validity spine to:

```lean
structure FH where
  roots : List FHNode
  size : Nat
  minRoot : Option Nat

def MinRootValid (h : FH) : Prop :=
  match h.minRoot with
  | none => h.roots = []
  | some i => exists root,
      h.roots[i]? = some root /\
      forall y ∈ h.keyBag, root.key <= y

def Valid (h : FH) : Prop :=
  FHNode.ForestGood h.roots /\
  FHNode.ForestLossInvariant h.roots /\
  FHNode.RootsUnmarked h.roots /\
  h.size = FHNode.forestSize h.roots /\
  h.MinRootValid
```

- [ ] **Step 2: Add executable minimum-index helpers**

```lean
def minRootIndex : List FHNode -> Option Nat
  | [] => none
  | root :: roots =>
      match minRootIndex roots with
      | none => some 0
      | some i =>
          match roots[i]? with
          | none => some 0
          | some tailMin => if root.key <= tailMin.key then some 0 else some (i + 1)

def minimum (h : FH) : Option Int :=
  h.minRoot.bind fun i => (h.roots[i]?).map FHNode.key
```

Prove `minRootIndex` is `none` exactly on `[]`, selects an in-bounds root, and
selects a root key no larger than every key of a `ForestGood` forest.

- [ ] **Step 3: Update basic operations**

Use these cache updates:

```lean
def makeHeap : FH := { roots := [], size := 0, minRoot := none }

def insert (x : Int) (h : FH) : FH :=
  { roots := FHNode.node x false [] :: h.roots
  , size := h.size + 1
  , minRoot :=
      match h.minimum with
      | none => some 0
      | some m => if x <= m then some 0 else h.minRoot.map Nat.succ }

def union (h1 h2 : FH) : FH :=
  { roots := h1.roots ++ h2.roots
  , size := h1.size + h2.size
  , minRoot :=
      match h1.minimum, h2.minimum with
      | none, none => none
      | some _, none => h1.minRoot
      | none, some _ => h2.minRoot.map (h1.roots.length + .)
      | some x, some y =>
          if x <= y then h1.minRoot else h2.minRoot.map (h1.roots.length + .) }
```

Update `makeHeap_valid`, `insert_valid`, and `union_valid` to prove the new
loss and cache conjuncts.  Retain their existing theorem names and semantic
statements.

- [ ] **Step 4: Refactor extract-min to use the cached root**

Replace the minimum-root scan in `extractMin` with lookup and `eraseIdx` at
`h.minRoot`; after child promotion and consolidation, set
`minRoot := minRootIndex roots'`.  Prove the existing `extractMin_correct`
surface plus the new loss/cache components of validity.  Keep
`removeMinRoot` and its theorems as compatibility lemmas, but do not call it in
the new transition.

- [ ] **Step 5: Prove the cached query theorem**

```lean
theorem minimum_cached (h : FH) :
    h.minimum = h.minRoot.bind fun i => (h.roots[i]?).map FHNode.key := rfl
```

- [ ] **Step 6: Run focused checks and commit**

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
lake env lean Tests/Chapter_19_Interface.lean
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean Tests/Chapter_19_Interface.lean
git commit -m "feat(ch19): cache the executable minimum root"
```

Expected interface failure after compilation: unknown identifier `FHPath`.

### Task 4: Build occurrence paths and a verified zipper

**Files:**
- Create: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean`
- Modify: `CLRSLean/Chapter_19.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Create the module and data types**

```lean
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap

namespace CLRS
namespace Chapter19

structure FHPath where
  root : Nat
  children : List Nat

structure FHFrame where
  key : Int
  marked : Bool
  before : List FHNode
  after : List FHNode

def FHFrame.close (frame : FHFrame) (child : FHNode) : FHNode :=
  FHNode.node frame.key frame.marked (frame.before ++ child :: frame.after)

structure FHCursor where
  focus : FHNode
  parents : List FHFrame
  rootsBefore : List FHNode
  rootsAfter : List FHNode
  size : Nat
  minRoot : Option Nat
```

- [ ] **Step 2: Implement opening and closing**

Define `FHNode.openChildren` by recursion over the child-index list, splitting
with `take` and `drop (i + 1)`.  Define `FH.openPath` by splitting the root list
at `path.root`.  Define `FHCursor.closeNode` by folding the frames from nearest
parent to root and `FHCursor.close` by reinserting that root between
`rootsBefore` and `rootsAfter`.

- [ ] **Step 3: Prove exact reconstruction**

```lean
theorem FH.openPath_close {h : FH} {path : FHPath} {cursor : FHCursor}
    (hopen : h.openPath path = some cursor) :
    cursor.close = h
```

Also prove exact key-bag and size decomposition for a cursor; use
`List.take_append_getElem_drop` and `FHNode.forestKeyBag_append` rather than
Finset extensionality so duplicate occurrences remain visible.

- [ ] **Step 4: Wire and check**

Import the new module from `CLRSLean/Chapter_19.lean`, then run:

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts
lake env lean Tests/Chapter_19_Interface.lean
```

Expected interface failure: unknown identifier `FH.cutAtPath`.

- [ ] **Step 5: Commit**

```bash
git add CLRSLean/Chapter_19.lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean Tests/Chapter_19_Interface.lean
git commit -m "feat(ch19): add duplicate-safe Fibonacci heap cursors"
```

### Task 5: Implement arbitrary CUT and CASCADING-CUT

**Files:**
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define result and recursive transition**

```lean
structure FHCascadeResult where
  heap : FH
  cuts : Nat
  cost : Nat

def FH.cascadingCut : FHCursor -> Option FHCascadeResult
```

The root-focus case returns `none`.  The parent-root case cuts the focus and
returns one cut.  The unmarked nonroot-parent case cuts the focus, marks the
parent, rebuilds the remaining zipper, and stops.  The marked-parent case cuts
the focus and recurses with the parent-without-focus as the next focus; prepend
both promoted roots in the returned forest and increment `cuts` and `cost`.

Define the path wrapper:

```lean
def FH.cutAtPath (h : FH) (path : FHPath) : Option FHCascadeResult :=
  h.openPath path >>= FH.cascadingCut
```

- [ ] **Step 2: Prove local invariant transport**

Prove frame-close lemmas for key bag, size, heap order, and `LossInvariant`.
The first-loss lemma must use an unmarked child's stored bound `j <= degree`
to derive the marked replacement bound `j - 1 <= degree - 1`.  The
marked-parent branch removes that child immediately and uses the existing
`wellformed_remove_index` pattern recursively.

- [ ] **Step 3: Prove the bundled arbitrary-cut theorem**

```lean
theorem FH.cutAtPath_correct {h : FH} {path : FHPath} {result : FHCascadeResult}
    (hvalid : h.Valid)
    (hcut : h.cutAtPath path = some result) :
    result.heap.keyBag = h.keyBag /\
    result.heap.size = h.size /\
    result.heap.Valid /\
    1 <= result.cuts
```

Prove `FH.cascadingCut_correct` at cursor level with the stronger exact
root/mark balance used by the cost theorem.

- [ ] **Step 4: Verify and commit**

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts
lake env lean Tests/Chapter_19_Interface.lean
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean Tests/Chapter_19_Interface.lean
git commit -m "feat(ch19): prove arbitrary cascading cuts"
```

Expected next failure: unknown identifier `FH.decreaseKeyAt`.

### Task 6: Implement decrease-key and exact duplicate semantics

**Files:**
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define update result and transition**

```lean
structure FHUpdateResult where
  oldKey : Int
  heap : FH
  cost : Nat

def FH.decreaseKeyAt (h : FH) (path : FHPath) (newKey : Int) :
    Option FHUpdateResult
```

Reject an invalid path and reject `newKey > oldKey`.  For a root or a
nonviolating parent edge, replace the focus key and close directly.  For a
violating edge, replace the focus key and call `cascadingCut`.  Update the
cached minimum to the decreased root when it is smaller than the old cached
minimum.

- [ ] **Step 2: Prove exact semantics and validity**

```lean
theorem FH.decreaseKeyAt_correct {h : FH} {path : FHPath} {newKey : Int}
    {result : FHUpdateResult}
    (hvalid : h.Valid)
    (hdec : h.decreaseKeyAt path newKey = some result) :
    newKey <= result.oldKey /\
    result.heap.keyBag = h.keyBag.erase result.oldKey + {newKey} /\
    result.heap.size = h.size /\
    result.heap.Valid
```

The multiset equality is occurrence-exact.  In particular, no uniqueness
premise is introduced and another occurrence of `result.oldKey` remains.

- [ ] **Step 3: Verify and commit**

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts
lake env lean Tests/Chapter_19_Interface.lean
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean Tests/Chapter_19_Interface.lean
git commit -m "feat(ch19): prove executable decrease-key by handle"
```

Expected next failure: unknown identifier `FH.deleteAt`.

### Task 7: Implement delete by decrease-key plus extract-min

**Files:**
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define the transition**

```lean
def FH.deleteAt (h : FH) (path : FHPath) : Option FHUpdateResult := do
  let cursor <- h.openPath path
  let minimum <- h.minimum
  let decreased <- h.decreaseKeyAt path (minimum - 1)
  let (_, heap) <- decreased.heap.extractMin
  pure { oldKey := cursor.focus.key, heap := heap, cost := decreased.cost + 1 }
```

The cost field is completed in Task 8 when the costed extract-min result is
available; until then the semantic transition uses the same composition with a
temporary structural unit charge.

- [ ] **Step 2: Prove exact deletion**

```lean
theorem FH.deleteAt_correct {h : FH} {path : FHPath} {result : FHUpdateResult}
    (hvalid : h.Valid)
    (hdelete : h.deleteAt path = some result) :
    result.heap.keyBag = h.keyBag.erase result.oldKey /\
    result.heap.size + 1 = h.size /\
    result.heap.Valid
```

Use `minimum - 1 < minimum`, cached-min correctness, the exact decrease-key bag
replacement, and `extractMin_keyBag`.  The strict sentinel ensures the
extracted occurrence is the addressed node even when its old key is duplicated.

- [ ] **Step 3: Verify and commit**

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts
lake env lean Tests/Chapter_19_Interface.lean
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S2_CascadingCuts.lean Tests/Chapter_19_Interface.lean
git commit -m "feat(ch19): prove handle-directed Fibonacci heap delete"
```

Expected next failure: unknown identifier `FH.Costed.consolidate`.

### Task 8: Instrument consolidation and prove logarithmic extract-min

**Files:**
- Create: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S3_AmortizedCosts.lean`
- Modify: `CLRSLean/Chapter_19.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Define costed results and consolidation**

```lean
namespace FH.Costed

structure Result (alpha : Type) where
  value : alpha
  cost : Nat

def consolidate (roots : List FHNode) : Result (List FHNode)
```

Instrument the same degree-bucket branches as `insertConsolidated` and
`consolidateList`: charge one for each input root, one for each equal-degree
link, and one per final bucket inspected for the cached minimum.  Prove
`consolidate roots |>.value = FHNode.consolidateList roots` and prove the link
count identity from input and output root lengths.

- [ ] **Step 2: Prove the post-consolidation root bound**

```lean
theorem degreeStrict_length_le {h : FH}
    (hvalid : h.Valid) (hstrict : FHNode.DegreeStrict h.roots) :
    h.roots.length <= 2 * Nat.log 2 h.size + 2
```

Map roots to degrees, use pairwise strictness, bound each root degree through
`FHNode.wellformed_degree_le_twice_log_two`, and prove that a strictly
increasing bounded natural list has length at most bound plus one.

- [ ] **Step 3: Define and relate costed extract-min**

```lean
def extractMin (h : FH) : Option (Result (Int × FH))

theorem extractMin_erases (h : FH) :
    (extractMin h).map (fun result => result.value) = h.extractMin
```

The cost is root removal plus promoted-child traversal plus costed
consolidation plus the final minimum-bucket scan.

- [ ] **Step 4: Prove the logarithmic amortized bound**

```lean
theorem extractMin_amortized_le_log {h : FH} {result : Result (Int × FH)}
    (hvalid : h.Valid) (hextract : extractMin h = some result) :
    Int.ofNat result.cost + FH.potential result.value.2 - FH.potential h <=
      12 * Int.ofNat (Nat.log 2 h.size + 1) + 8
```

Use the exact input/output root-count equation, mark clearing, link count, and
`degreeStrict_length_le`.  Keep all Nat subtraction facts as additive balance
lemmas before casting to `Int`.

- [ ] **Step 5: Wire and commit**

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts
lake env lean Tests/Chapter_19_Interface.lean
git add CLRSLean/Chapter_19.lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S3_AmortizedCosts.lean Tests/Chapter_19_Interface.lean
git commit -m "prove(ch19): bound extract-min amortized cost"
```

### Task 9: Complete decrease/delete costs and operation traces

**Files:**
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S3_AmortizedCosts.lean`
- Modify: `Tests/Chapter_19_Interface.lean`

- [ ] **Step 1: Add costed wrappers**

```lean
def decreaseKeyAt (h : FH) (path : FHPath) (newKey : Int) :
    Option (Result FHUpdateResult)

def deleteAt (h : FH) (path : FHPath) :
    Option (Result FHUpdateResult)
```

Their erasure theorems identify the values with `FH.decreaseKeyAt` and
`FH.deleteAt`; costs are the branch counts already returned by cascading cut
and the costed extract-min composition.

- [ ] **Step 2: Prove the one-operation bounds**

```lean
theorem decreaseKey_amortized_le_three {h : FH} {path : FHPath}
    {newKey : Int} {result : Result FHUpdateResult}
    (hvalid : h.Valid)
    (hdec : decreaseKeyAt h path newKey = some result) :
    Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h <= 3

theorem delete_amortized_le_log {h : FH} {path : FHPath}
    {result : Result FHUpdateResult}
    (hvalid : h.Valid)
    (hdelete : deleteAt h path = some result) :
    Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h <=
      12 * Int.ofNat (Nat.log 2 h.size + 1) + 11
```

Also add exact constant bounds for make-heap, cached minimum, insert, and union.

- [ ] **Step 3: Add a trace machine and telescope**

Define an operation inductive containing insert, union-with, minimum,
extract-min, decrease-key, and delete; define a costed step and list fold.
Instantiate `CLRS.Chapter17.PotentialTrace` with the actual step costs and
`FH.potential`.  Prove:

```lean
theorem run_totalCost_le (initial : FH) (operations : List Operation)
    (hvalid : initial.Valid) :
    Int.ofNat (run initial operations).cost <=
      (run initial operations).amortizedBound + FH.potential initial
```

- [ ] **Step 4: Verify and commit**

```bash
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts
lake env lean Tests/Chapter_19_Interface.lean
git add CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S3_AmortizedCosts.lean Tests/Chapter_19_Interface.lean
git commit -m "prove(ch19): close Fibonacci heap amortized costs"
```

Expected: every new interface check passes.

### Task 10: Synchronize Chapter 19 status and verify closure

**Files:**
- Modify: `CLRSLean/Chapter_19.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Progress.lean` through the generator
- Modify: `docs/proof-map.md`
- Modify: `docs/index.md`
- Modify: `literate.toml`
- Modify: `CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean`
- Modify: `CLRSLean/Chapter_19/Section_19_4_Bounding_Maximum_Degree.lean`

- [ ] **Step 1: Wire S2 and S3 into navigation**

Add both modules under the existing Section 19.1 child list in
`literate.toml`, with titles `19.1 S2. Cascading Cuts` and
`19.1 S3. Amortized Costs`, and add both source paths to `docs/index.md`.

- [ ] **Step 2: Make status claims match the proved boundary**

List the new public theorems in the chapter guide and proof map.  Change
Chapter 19 from `partial` only if arbitrary cuts, cascading cuts,
decrease/delete, cached minimum, and every stated operation-cost theorem are
all imported and kernel-checked.  Keep circular pointer mutation and Lean
evaluator allocation cost explicitly marked as lower-level refinements.

- [ ] **Step 3: Regenerate progress**

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
```

- [ ] **Step 4: Run final gates**

```bash
lake build +CLRSLean.Chapter_19
lake env lean Tests/Chapter_19_Interface.lean
rg -n '\b(sorry|admit|axiom|native_decide)\b' CLRSLean/Chapter_19 Tests/Chapter_19_Interface.lean
uv run python scripts/check_repository.py
lake build CLRSLean
git diff --check
```

Expected: all commands exit zero; the forbidden-proof scan prints no matches.
Do not run full `literateHtml` as a routine proof gate.  Run it only if the
navigation checker cannot validate the two new module entries or before a site
release.

- [ ] **Step 5: Audit headline axioms**

Run `#print axioms` for:

```lean
CLRS.Chapter19.FH.cascadingCut_correct
CLRS.Chapter19.FH.decreaseKeyAt_correct
CLRS.Chapter19.FH.deleteAt_correct
CLRS.Chapter19.FH.Costed.decreaseKey_amortized_le_three
CLRS.Chapter19.FH.Costed.extractMin_amortized_le_log
CLRS.Chapter19.FH.Costed.delete_amortized_le_log
CLRS.Chapter19.FH.Costed.run_totalCost_le
```

Expected dependencies: only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 6: Commit the synchronized closure**

```bash
git add CLRSLean/Chapter_19.lean CLRSLean/Status.lean CLRSLean/Progress.lean CLRSLean/Chapter_19 docs/clrs-proof-progress.csv docs/proof-map.md docs/index.md literate.toml Tests/Chapter_19_Interface.lean
git commit -m "docs(ch19): record cascading-cut and amortized closure"
```
