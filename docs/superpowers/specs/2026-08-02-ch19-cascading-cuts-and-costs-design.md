# Chapter 19 Cascading Cuts and Amortized Costs Design

## Goal

Close the remaining main Chapter 19 algorithmic layer on top of the executable
`FHNode`/`FH` forest: address an arbitrary node occurrence, perform CLRS `CUT`
and `CASCADING-CUT`, implement executable `decreaseKey` and `delete`, and prove
operation-level costs under the standard potential
`Phi(H) = t(H) + 2 m(H)`.

The completion boundary is the persistent executable model.  Circular sibling
lists and machine-address mutation remain a representation refinement, but the
cost model must count the same root-list, link, mark, cut, and bucket operations
as the CLRS pseudocode and must be connected to the executable transitions.

## Current model and the missing invariant

`FHNode.Wellformed` records the CLRS Lemma 19.1 lower bound
`j - 1 <= degree(child[j])`.  That predicate is sufficient for the degree
theorem and for removing a direct child of a root.  It is not strong enough to
justify leaving a nonroot parent in place after its first child loss: Lean needs
to know that an unmarked child at position `j` still has degree at least `j`, so
that losing one child and becoming marked leaves degree at least `j - 1`.

Add a recursive mark-aware invariant:

```lean
def FHNode.LossInvariant : FHNode -> Prop
  | .node _ _ children =>
      (forall j, (hj : j < children.length) ->
        j - (if children[j].marked then 1 else 0) <= children[j].degree) /\
      forall child, child ∈ children -> child.LossInvariant
```

It implies the existing `Wellformed`.  Equal-degree `LINK` of unmarked roots
preserves it, as do insertion, union, promotion, consolidation, and the CLRS
mark/cut cases.  The full heap invariant is strengthened to include it; the old
`ForestGood` projections remain available for existing proofs.

## Occurrence handles and zipper

Keys cannot identify nodes because `keyBag` intentionally permits duplicates.
The persistent model therefore uses an occurrence path:

```lean
structure FHPath where
  root : Nat
  children : List Nat

structure FHFrame where
  key : Int
  marked : Bool
  before : List FHNode
  after : List FHNode

structure FHCursor where
  focus : FHNode
  parents : List FHFrame
  rootsBefore : List FHNode
  rootsAfter : List FHNode
  size : Nat
  minRoot : Option Nat
```

`FH.openPath` follows a path and splits each child list into a zipper frame.
`FHCursor.close` reconstructs the exact heap.  Theorems prove successful open
followed by close is the original heap, the focus is one exact multiset
occurrence, and reconstruction preserves all unrelated occurrences.

The executable path lookup is useful for tests and functional clients.  The
costed CLRS operation starts from a verified cursor: a cursor is the persistent
analogue of an already dereferenced node pointer, so handle lookup is not
silently charged as a tree traversal.  This makes the cost boundary explicit
instead of pretending `List` path lookup is constant time.

## Arbitrary CUT and CASCADING-CUT

`FHCursor.cut` removes a nonroot focus from its immediate frame, clears the
focus mark, and promotes it to the root forest.  `FHCursor.cascadingCut`
continues upward exactly as CLRS specifies:

1. if the parent is a root, stop;
2. if the nonroot parent is unmarked, mark it and stop;
3. if the nonroot parent is marked, remove it, clear its mark, promote it, and
   continue at its parent.

The result records the number of cut nodes:

```lean
structure FHCascadeResult where
  heap : FH
  cuts : Nat
  cost : Nat
```

Successful arbitrary cuts prove exact `keyBag` preservation, stored and real
size preservation, root marks, heap order, `LossInvariant`, and an exact
root/mark balance.  The cost is one unit per inspected stop case plus one unit
per cut.  The central inequality is stated directly in potential form:

```lean
theorem cascadingCut_amortized_le_three ... :
  Int.ofNat result.cost + FH.potential result.heap - FH.potential before <= 3
```

The exact accounting theorem remains the truth source; the constant bound is a
corollary.

## Cached minimum root

The current `FH.minimum` scans a `Finset`, and `extractMin` scans the root list.
That cannot support the CLRS constant-time minimum interface.  Add a cached
root index to `FH` and a `MinRootValid` component to `FH.Valid`:

```lean
structure FH where
  roots : List FHNode
  size : Nat
  minRoot : Option Nat
```

`MinRootValid` states that `none` is equivalent to an empty forest and that a
cached index selects a root whose key is no greater than every represented key.
Insertion and union update the index arithmetically.  CUT/decrease update it
from the old cached root and the promoted/decreased node.  Extraction removes
the cached root and computes the next cached root while traversing the
consolidated degree buckets.  `minimum` becomes a cached lookup.

## Decrease-key and delete

`FH.decreaseKeyAt` accepts a verified cursor and a new key with
`newKey <= cursor.focus.key`.  It changes exactly the selected occurrence.  If
heap order against the parent remains true, it closes the cursor directly;
otherwise it performs the initial cut and cascading cut.  Its bundled theorem
proves:

- exact replacement of one old-key occurrence by one new-key occurrence;
- preservation of every other occurrence, including duplicate keys;
- full validity and unchanged size;
- the new key is reflected by the cached minimum; and
- amortized cost at most a fixed constant.

`FH.deleteAt` follows the CLRS composition.  For a nonempty valid heap it
chooses `minimum - 1`, decreases the selected occurrence to that fresh strict
minimum, and invokes cached-root `extractMin`.  Since `Int` is unbounded, the
sentinel is always available and cannot collide with an old minimum.  The
result removes exactly the selected occurrence even when several nodes carry
the same original key.  Its amortized bound is the decrease-key constant plus
the extract-min logarithmic bound.

## Costed execution and asymptotic boundary

The cost layer lives in `S3_AmortizedCosts.lean` and instruments the executable
branches rather than assigning unrelated post-hoc constants.  It records:

- root splice, mark, and cut steps for cascading cuts;
- roots processed and equal-degree links for consolidation;
- promoted children and final cached-min bucket scan for extract-min; and
- composition costs for decrease-key and delete.

The consolidation link count is tied to the executable output root count.  A
degree-strict valid post-consolidation forest has at most
`2 * Nat.log 2 n + 2` roots, using the already proved Lemma 19.5 bound.  Combining
that fact with the exact potential change yields explicit bounds:

```lean
makeHeapAmortizedCost <= 1
minimumCost <= 1
insertAmortizedCost <= 2
unionAmortizedCost <= 2
decreaseKeyAmortizedCost <= 3
extractMinAmortizedCost <= 12 * (Nat.log 2 n + 1) + 8
deleteAmortizedCost <= 12 * (Nat.log 2 n + 1) + 11
```

These fixed conservative constants leave room for root removal, child
promotion, links, and the final cached-min scan; the results are not weakened
to an existential big-O statement.  Trace-level total-cost theorems instantiate
the Chapter 17 potential telescoping framework.

The metric is the CLRS pointer/bucket primitive model.  It does not claim Lean
evaluator time for persistent `List.append`, nor hardware allocation cost.

## Module and public interface layout

- Modify `S1_ExecutableFibHeap.lean` only for the cached minimum field, the
  strengthened validity spine, and preservation lemmas needed by old operations.
- Add `S2_CascadingCuts.lean` for `LossInvariant`, paths, zippers, arbitrary
  cuts, cascading cuts, decrease-key, and delete semantics.
- Add `S3_AmortizedCosts.lean` for instrumented consolidation/operations,
  logarithmic root bounds, one-step amortized inequalities, and trace theorems.
- Extend `Tests/Chapter_19_Interface.lean` before each public implementation and
  observe the expected missing-identifier failure.
- Update the chapter guide, status ledger, proof map, progress CSV, dashboard,
  `docs/index.md`, and `literate.toml` only after the corresponding Lean surface
  compiles.

## Rejected alternatives

Adding a numeric ID directly to every existing `FHNode` would force a rewrite
of the complete consolidation/extract-min proof stack, and independently
constructed heaps make ID-preserving union require a global name supply or
handle-renaming map.  A parallel second heap implementation would avoid that
rewrite but would duplicate all existing proofs and leave `FH` as permanent
scaffolding.  State-relative paths plus a verified zipper preserve duplicate
occurrence semantics, reuse the existing forest, and expose exactly the local
context that cascading cuts need.

## Verification

Development uses focused checks:

```text
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts
lake build +CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts
lake env lean Tests/Chapter_19_Interface.lean
```

Completion additionally requires the forbidden-proof scan, headline
`#print axioms`, repository checks, and `lake build CLRSLean`.  Full
`literateHtml` is a release/site-navigation check rather than a per-proof
development gate.
