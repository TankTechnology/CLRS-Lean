# Chapter 18 Top-Level B-Tree Insertion Design

## Goal

Complete the real CLRS `B-TREE-INSERT` layer above the already-proved
`insertNonFull` algorithm.  The new operation must split a full root before
descent, preserve the structural `WellFormed` invariant, add exactly one key,
and expose height, membership, search, specification-compatibility, and
uniqueness wrappers.

This design deliberately leaves the early flat `insert` operation in place as
the specification layer.  The executable operation is named `insertRoot` and
is related to `insert` extensionally through key membership rather than tree
shape equality.

## Existing Foundation

The implementation reuses the following proved surfaces:

- `splitChild` and its exact `List.Perm` key-preservation theorem;
- preservation of `Sorted`, `ChildBounded`, `Occupancy`, and `SameDepth` by an
  ordinary non-full-parent child split;
- the real recursive `insertNonFull`;
- `insertNonFull_keys_perm`, `insertNonFull_wellFormed`, and
  `insertNonFull_height`;
- `searchExec_true_iff` for structurally well-formed output trees;
- `UniqueKeys` and `WellFormedUnique`.

The missing layer is not another recursive insertion proof.  It is the
full-root transition that makes the precondition of `insertNonFull` true.

## Approaches Considered

### A. Wrap the old root and reuse `splitChild` — selected

Define:

```lean
def splitRoot (t : Nat) (tr : BTree) : BTree :=
  splitChild t (node [] [tr]) 0
```

Then define `insertRoot` by testing whether the old root is full.  In the full
branch, split the wrapped root and call `insertNonFull`; in the non-full branch,
call `insertNonFull` directly.

This keeps one executable split implementation and reuses the existing split
contents, ordering, child-bound, and same-depth proofs.  It requires a dedicated
root-occupancy bridge because `node [] [tr]` is intentionally only a transient
state.

### B. Implement a separate explicit root splitter

Pattern-match on the old root and construct the promoted median and two halves
directly.  This makes the final root occupancy proof syntactically local, but
duplicates `splitChild`, creates a second executable split definition, and
would require a separate equivalence or duplicated preservation surface.

### C. Relax `Occupancy` to admit the transient one-child empty root

This would allow the generic `splitChild_preserves_wellFormed` theorem to apply,
but it would weaken every normal root theorem and reintroduce exactly the
malformed state that deletion root normalization was designed to exclude.

Approach A is selected.  The transient wrapper is never advertised as
`WellFormed`; only its split result is.

## Executable Interface

```lean
def splitRoot (t : Nat) (tr : BTree) : BTree :=
  splitChild t (node [] [tr]) 0

def insertRoot (t x : Nat) (tr : BTree) : BTree :=
  if rootKeyCount tr = 2 * t - 1 then
    insertNonFull t x (splitRoot t tr)
  else
    insertNonFull t x tr
```

The full-root test is equality, not `≥`, because `WellFormed` already supplies
the upper bound.  The theorem surface always assumes `2 ≤ t` and
`WellFormed t tr`, so malformed overfull input is outside the correctness
contract.

## Proof Architecture

### Full-root transition

First prove small bridge lemmas:

1. a full well-formed old root satisfies `Occupancy t false` when viewed as a
   child of the new root;
2. `node [] [tr]` satisfies the `Sorted`, `ChildBounded`, and `SameDepth`
   hypotheses needed by the existing split theorems;
3. unfolding `splitRoot` on a full root produces one promoted root key and two
   children;
4. the two split halves satisfy non-root occupancy;
5. the final one-key/two-child root satisfies root occupancy.

These combine into:

```lean
theorem splitRoot_wellFormed
    (ht : 2 ≤ t) (hwf : WellFormed t tr)
    (hfull : rootKeyCount tr = 2 * t - 1) :
    WellFormed t (splitRoot t tr)
```

Companion theorems state:

- `splitRoot_keys_perm`;
- `rootKeyCount (splitRoot t tr) = 1`;
- `heightOf (splitRoot t tr) = heightOf tr + 1`;
- `rootKeyCount (splitRoot t tr) < 2 * t - 1`.

The last theorem is the exact precondition needed by
`insertNonFull_wellFormed`.

### Top-level insertion

Split on the same fullness condition used by `insertRoot`.

- Non-full branch: apply the existing `insertNonFull` theorems directly.
- Full branch: use the `splitRoot` bridge, then apply the existing
  `insertNonFull` theorems.

The core public surface is:

```lean
theorem insertRoot_wellFormed ...
theorem insertRoot_keys_perm ...
theorem insertRoot_mem_iff ...
theorem insertRoot_height ...
theorem insertRoot_correct ...
```

`insertRoot_height` gives the precise conditional result: the height is
unchanged when the old root is non-full and increases by one when it is full.
The bundled `insertRoot_correct` includes exact key contents, `WellFormed`, and
the same-or-one-higher height result.

### Uniqueness and query wrappers

`insertRoot_keys_perm` adds exactly `[x]`, so uniqueness is preserved only under
the necessary premise `¬ mem x tr`.  The result is exposed as
`insertRoot_wellFormedUnique`.

Membership and query wrappers are derived rather than reproved recursively:

- membership from `List.Perm`;
- specification compatibility from `insert_mem_iff`;
- membership-oracle `search` from membership;
- executable `searchExec` from output `Sorted` and `ChildBounded`.

No insertion module theorem depends on the deletion module's `keyBag`; this
preserves the current import direction.

## Test Design

Create `Tests/Chapter_18_Insertion_Interface.lean`.

The first commit contains RED `#check` contracts for the selected public API.
Subsequent commits turn them green in dependency order:

1. `splitRoot` definitions and full-root bridge;
2. `insertRoot` structural/content/height capstones;
3. uniqueness, search, and specification wrappers.

Every implementation commit must pass:

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_2_B_Tree_Insertion.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Insertion_Interface.lean
lake build CLRSLean.Chapter_18
```

At the insertion milestone, run every `Tests/Chapter_18*.lean` file with
`-DwarningAsError=true`, scan the Chapter 18 Lean sources for unfinished proof
markers, and run `git diff --check`.

Full-site `lake build :literateHtml` is explicitly outside the single-chapter
completion gate.  Fast site/config consistency checks are needed only if the
module registry or navigation changes.

## Commit Boundaries

Use small, reviewable commits:

1. design and implementation plan;
2. RED insertion interface;
3. full-root split bridge;
4. top-level insertion capstones;
5. query/uniqueness ergonomics and Chapter 18 documentation.

Do not combine the independent key-count/height theorem group with these
commits.  It receives its own design, interface test, and proof series after
top-level insertion is green.

## Non-Goals

- changing the existing specification-level `insert` tree shape;
- admitting transient roots into `WellFormed`;
- pointer mutation, disk pages, buffer caches, or I/O cost semantics;
- equality between executable and specification tree shapes;
- full-site HTML generation during Chapter 18 proof development.
