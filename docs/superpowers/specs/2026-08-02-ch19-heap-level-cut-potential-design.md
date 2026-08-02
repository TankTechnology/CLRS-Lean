# Ch19 Heap-Level CUT Potential Design

## Goal

Replace the uncompiled local potential draft with an executable heap-level
direct-child `CUT` transition and prove its exact change in the CLRS potential
`t(H) + 2m(H)`.  This milestone must preserve all previously proved
`FHNode.cutChild` results and leave the branch compiler-clean for the next
`extractMin` milestone.

## Starting point and preservation

The five compiler-clean Chapter 19 checkpoints end at `03abce7`.  The 115-line
amortized-analysis draft is preserved separately by commit `719c92c` on
`codex/ch19-amortized-draft-backup` and by the equivalent cherry-picked commit
`0b2d239` in the implementation worktree.  That draft is evidence and lemma
scaffolding, not an interface constraint: definitions and theorem statements
may be replaced when they describe the wrong state transition.

Development takes place on `codex/ch19-heap-cut` in the isolated worktree
`/home/ubuntu/clrs-lean-worktrees/codex/ch19-heap-cut`.  The original `main`
worktree remains clean and is not rebased or pushed during this milestone.

## Scope

This pass covers:

- recursive marked-node counting on `FHNode` and forests;
- the heap-level potential `FH.potential`;
- zero-potential and insertion-potential equations;
- an index-addressed direct-child cut on one node;
- an index-addressed heap transition that replaces the parent root and promotes
  the cleared child into the root list;
- key-set, stored-size, root-count, heap-order, structural-wellformedness, and
  potential-change theorems for a successful heap-level cut;
- public interface checks and truthful Chapter 19 status documentation.

This pass does not implement arbitrary descendant paths, stable external
handles, cascading cuts, `decreaseKey`, `delete`, or `extractMin`.  It also does
not yet define the final `FH.Valid`/`FH.Represents` predicate tying the stored
`size` field to the recursive node count.  Those are separate milestones; the
next one is the executable `extractMin` that invokes `consolidateList`.

## Mark count and potential

Marked nodes are counted recursively, not only at the roots:

```lean
def FHNode.marks : FHNode -> Nat
  | .node _ marked children =>
      (if marked then 1 else 0) + (children.map marks).sum

def FHNode.forestMarks (roots : List FHNode) : Nat :=
  (roots.map FHNode.marks).sum

def FH.potential (h : FH) : Int :=
  Int.ofNat h.roots.length + 2 * Int.ofNat (FHNode.forestMarks h.roots)
```

Putting both recursive counters in `namespace FHNode` fixes the namespace error
in the draft and makes the counting lemmas reusable by `extractMin` and
cascading cuts.  `FH.potential` consumes a full heap, so a theorem cannot
silently omit unrelated roots or the parent root.

The initial public equations are:

```lean
theorem potential_makeHeap : potential makeHeap = 0

theorem potential_insert (x : Int) (h : FH) :
    potential (insert x h) = potential h + 1
```

## Index-addressed CUT operations

Keys are not handles: the current representation collapses duplicates in its
`Finset` view, and selecting a node by key would make the operational meaning
ambiguous.  This milestone therefore addresses the parent root and direct child
by list indices.

The node-level operation has the shape:

```lean
def cutChildAt (t : FHNode) (childIndex : Nat) :
    Option (FHNode * FHNode)
```

On success it returns the selected child with its mark cleared and the parent
with that child removed.  The existing key-directed `cutChild` remains
available; the new indexed operation supplies the unambiguous executable spine
for the heap transition.

The heap-level operation has the shape:

```lean
def cutRootChildAt (h : FH) (rootIndex childIndex : Nat) : Option FH
```

It fails if either index is out of bounds.  On success it:

1. selects `parent = h.roots[rootIndex]`;
2. runs `cutChildAt parent childIndex` to obtain `(cut, parent')`;
3. replaces the selected root by `parent'`;
4. prepends `cut` to the root list; and
5. preserves `h.size`.

Prepending gives a simple executable realization of inserting the cut node into
the circular root list; root order has no semantic role before consolidation.

## Correctness interface

Successful node-level cuts expose both halves of the existing invariant:

```lean
theorem cutChildAt_keys ... :
    cut.keySet union parent'.keySet = parent.keySet

theorem cutChildAt_heapOrdered ... :
    cut.HeapOrdered /\ parent'.HeapOrdered

theorem cutChildAt_wellformed ... :
    cut.Wellformed /\ parent'.Wellformed
```

The heap-level public surface then proves:

```lean
theorem cutRootChildAt_keys ... : FH.keys h' = FH.keys h

theorem cutRootChildAt_size ... : h'.size = h.size

theorem cutRootChildAt_roots_length ... :
    h'.roots.length = h.roots.length + 1

theorem cutRootChildAt_good ... :
    FHNode.ForestGood h.roots -> FHNode.ForestGood h'.roots
```

Here `...` includes the successful result equation
`cutRootChildAt h rootIndex childIndex = some h'` and, where needed, the input
forest invariant.  Key preservation is stated as equality of the existing
`Finset` semantics; no duplicate-key claim is added.

## Exact potential theorem

Let `child` be the original child selected by the two indices.  A successful
cut adds one root and removes exactly the original child's own mark; marks in
its descendants and every unrelated root are unchanged.  The strongest theorem
therefore states:

```lean
theorem cutRootChildAt_potential_eq ... :
    potential h' = potential h + 1 -
      2 * Int.ofNat (if child.marked then 1 else 0)
```

The public amortized-bound corollary is:

```lean
theorem cutRootChildAt_potential_le ... :
    potential h' <= potential h + 1
```

The exact equality is the reusable result.  The inequality alone would hide
the two-unit credit released when a marked node becomes a root, which is needed
by the later cascading-cut proof.

## Test and documentation surface

`Tests/Chapter_19_Interface.lean` will import the executable S1 module and
`#check` the mark-count definitions, heap potential equations, both indexed cut
operations, the heap invariant theorems, and both potential theorems.  The test
is added before the declarations and must first fail because the names are
missing.

The S1 module header, `CLRSLean/Chapter_19.lean`, `CLRSLean/Status.lean`,
`docs/proof-map.md`, and `docs/clrs-proof-progress.csv` will distinguish:

- completed executable `consolidateList`;
- completed heap-level direct-child cut and its one-step potential theorem; and
- remaining arbitrary-path/cascading cut, executable `extractMin`, handles,
  global representation validity, and operation-cost semantics.

`CLRSLean/Progress.lean` is regenerated from the CSV and is never edited by
hand.  The S1 header must stop claiming that `FH.extractMin` already exists.

## Verification

The development loop uses the focused interface test and the S1 source file.
Completion requires fresh successful runs of:

```text
lake env lean Tests/Chapter_19_Interface.lean
lake lean CLRSLean/Chapter_19/Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean
rg -n '\b(sorry|admit|axiom|native_decide)\b' CLRSLean/Chapter_19 Tests/Chapter_19_Interface.lean
uv run python scripts/check_repository.py
lake build CLRSLean
lake build :literateHtml
git diff --check
```

`#print axioms` for `FH.cutRootChildAt_potential_eq`,
`FH.cutRootChildAt_potential_le`, `FH.cutRootChildAt_keys`, and
`FH.cutRootChildAt_good` must contain no `sorryAx` or project axiom.  Existing
linter warnings are reported but are not treated as proof failures.
