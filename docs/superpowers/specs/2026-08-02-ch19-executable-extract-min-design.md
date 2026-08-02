# Chapter 19 Executable Extract-Min Design

## Goal

Implement a persistent executable `FH.extractMin` that removes one minimum
node, promotes its children, invokes the existing proved `consolidateList`, and
preserves a concrete heap validity invariant.  Its semantic truth source is a
`Multiset Int`, so duplicate keys are represented exactly and one successful
extraction removes exactly one minimum-key occurrence.

## Scope

This milestone closes the executable structural and semantic core of CLRS
`FIB-HEAP-EXTRACT-MIN` for the current root-list model:

- select and remove a minimum root;
- promote that root's direct children and clear their root marks;
- consolidate the resulting forest by the existing degree-bucket algorithm;
- decrement the stored node count;
- prove minimum correctness, exact multiset deletion, structural validity, and
  degree uniqueness.

It does not introduce pointer handles, circular sibling lists, a cached minimum
pointer, arbitrary-path mutation, cascading cuts, or an actual-operation cost
model.  It also does not claim the amortized `O(log n)` bound in this milestone.

## Representation Layer

The existing `FH.keys : Finset Int` remains the duplicate-collapsing query
view.  The executable layer gains the following exact summaries:

```lean
def FHNode.keyBag (t : FHNode) : Multiset Int := t.keysList

def FHNode.forestKeyBag (roots : List FHNode) : Multiset Int :=
  roots.flatMap FHNode.keysList

def FHNode.forestSize (roots : List FHNode) : Nat :=
  (roots.map FHNode.size).sum

def FHNode.RootsUnmarked (roots : List FHNode) : Prop :=
  ∀ root ∈ roots, root.marked = false
```

The heap-level abstraction and invariant are:

```lean
def FH.keyBag (h : FH) : Multiset Int := FHNode.forestKeyBag h.roots

def FH.Represents (h : FH) (bag : Multiset Int) : Prop :=
  h.keyBag = bag

def FH.Valid (h : FH) : Prop :=
  FHNode.ForestGood h.roots ∧
  FHNode.RootsUnmarked h.roots ∧
  h.size = FHNode.forestSize h.roots
```

`Valid` deliberately contains only facts required by the persistent executable
model: heap order and the Section 19.4 structural invariant, the CLRS root-mark
rule, and agreement between stored and real node counts.  Handle identity and
pointer ownership remain outside this representation.

## Minimum-Root Selection

`removeMinRoot` is a recursive stable minimum selection over the root list:

```lean
def removeMinRoot : List FHNode → Option (FHNode × List FHNode)
  | [] => none
  | x :: xs =>
      match removeMinRoot xs with
      | none => some (x, [])
      | some (y, rest) =>
          if x.key ≤ y.key then some (x, xs)
          else some (y, x :: rest)
```

Ties choose the leftmost minimum root.  The selector must prove:

- `none` exactly for an empty root list;
- the original key bag is the selected root's bag plus the remaining forest;
- the original forest size is the selected root's size plus the remaining
  forest size;
- every remaining root came from the original list;
- the selected root key is no greater than every original root key;
- `ForestGood` and `RootsUnmarked` project to the selected root and the
  remaining forest.

The operation selects roots directly instead of computing the minimum over all
subtree keys and searching by value.  Heap order is then used once, in the
correctness proof, to lift minimum-root order to minimum-key order over every
node in every subtree.

## Strengthening CONSOLIDATE

The current `consolidateList` proofs cover `Finset` keys, `ForestGood`, and
degree strictness.  Extract-min additionally needs the following preservation
facts:

- `link` preserves `keyBag` and total node size;
- linking two unmarked roots produces an unmarked root;
- `insertConsolidated` preserves `forestKeyBag`, `forestSize`, and
  `RootsUnmarked`;
- `consolidateList` preserves those same three summaries.

These are genuine executable invariants rather than restatements of the
existing `Finset` theorem.  In particular, `forestKeyBag` preservation retains
duplicate multiplicities.

## Extract-Min Transition

The operation is:

```lean
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

Clearing each promoted child's root mark matches the root-mark invariant and is
compatible with the existing CUT transition.  It does not alter keys, subtree
sizes, heap order, or Section 19.4 wellformedness.  Consolidation is mandatory
in the transition rather than merely mentioned in its specification.

## Public Correctness Surface

The bundled truth source has this shape:

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

Direct public projections are added only where they remove downstream proof
friction:

- `extractMin_keyBag` for exact one-occurrence deletion;
- `extractMin_valid` for invariant preservation;
- `extractMin_degreeStrict` for the post-consolidation root property;
- `extractMin_size` for stored-size decrement under validity;
- `extractMin_minimum` connecting the returned key to existing `FH.minimum`;
- `extractMin_none_iff` for the unconditional empty-root-table behavior;
- `extractMin_none_iff_size_zero` under `FH.Valid`.

The `Finset` projection will state preservation of every key different from the
returned key.  It will not falsely state `h'.keys = h.keys.erase x` without a
uniqueness premise, because another occurrence of `x` may remain.

## Proof Decomposition

Proofs proceed in four independent layers:

1. Multiset and size summaries for nodes, forests, `markFalse`, and `link`.
2. `removeMinRoot` split, minimum, and invariant projection lemmas.
3. `insertConsolidated`/`consolidateList` preservation for bag, size, and
   root marks.
4. Heap-order lifting from a minimum root to every subtree key, followed by the
   bundled `extractMin_correct` theorem and its wrappers.

Nat equations use additive balance statements before subtraction.  Multiset
deletion is discharged only after proving the selected root-key singleton plus
promoted-child bag decomposition.  The final `size - 1` equality uses `Valid`
to establish nonemptiness and the exact real-node count.

## Testing and Commit Discipline

The public interface test is extended first with `#check` declarations for the
new summaries, invariant, selector, transition, bundled theorem, and direct
wrappers.  The test must fail on the missing names before production code is
written.

Implementation proceeds with compiler-clean commits at these boundaries:

1. exact bag/size summaries and `FH.Valid`;
2. minimum-root selector and its local theorems;
3. strengthened consolidation preservation;
4. executable `extractMin` and correctness surface;
5. synchronized Chapter 19 documentation and progress metadata.

Final gates are the focused S1 build, Chapter 19 interface test, forbidden-proof
scan, headline axiom print, repository checks, full `CLRSLean` build, and
literate HTML build.  Existing linter warnings may remain, but compilation or
publication errors may not.
