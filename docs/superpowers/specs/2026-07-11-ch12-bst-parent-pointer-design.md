# Design: Ch12.1 BST Parent-Pointer Refinement via Zipper

Date: 2026-07-11
Issue: [#6](https://github.com/TankTechnology/CLRS-Lean/issues/6)
Branch: `ch12-bst-parent-pointer`

## Summary

Add a Zipper layer over the existing inductive `BSTree` to encode parent-pointer
navigation. The zipper does NOT touch the existing type or its 30+ proved
theorems. It adds iterative search, functional subtree replacement, deletion
expressed through that replacement interface, and parent-ascent navigation,
each connected to the existing functional operations.

## Design Decision: Append to existing file, not a new file

This repo uses "one section file = one Verso web page" (CLAUDE.md). The zipper
is genuinely part of §12.1, not a separate section. Keeping it in
`Section_12_1_Binary_Search_Trees.lean` avoids fragmenting the page and
adding `literate.toml` registration noise. The file will grow from ~1200 to
~1700 lines.

## Core Types

```lean
inductive Frame where
  | fromLeft  (parentKey : Nat) (rightSibling : BSTree)
  | fromRight (parentKey : Nat) (leftSibling  : BSTree)

structure Zipper where
  focus : BSTree
  ctx   : List Frame
```

**Interpretation:**

- `focus` — the current subtree under the cursor (CLRS "x")
- `ctx` — path from the cursor back to the root (stack top = immediate parent)
- The path reads top-down: `ctx.reverse` gives root-to-focus order
- Each `Frame` encodes: "I descended left/right through `parentKey`, and
  `rightSibling`/`leftSibling` is the other branch I did not take"
- Parent pointer: in CLRS terms, `x.p = node(focus' parent key, ...)` where
  `focus'` is the parent of `focus`. This is encoded by `ctx.head?`

## Key Operations

### 1. `Frame.plug` and `Zipper.toTree`

```lean
def Frame.plug (fr : Frame) (t : BSTree) : BSTree
def Zipper.toTree (z : Zipper) : BSTree
```

`toTree` reconstructs the full tree from a zipper by folding `plug` over
the context path, bottom-up. This is the bridge lemma: every correctness
theorem works by `toTree`ing back to a `BSTree` and reusing the proved
functional theorems.

### 2. `searchZipper`

```lean
def searchZipper (x : Nat) (t : BSTree) : Zipper
```

Iterative search following BST decisions, recording each descent frame.
When `x` is found (or bottom reached), returns the zipper with `focus`
at the target node (or `empty`).

**Key invariant:** `searchZipper x t |>.toTree = t` (zipper is a view, not
a mutation).

### 3. `TRANSPLANT`

```lean
def transplant (z : Zipper) (newFocus : BSTree) : BSTree
```

Replaces `z.focus` with `newFocus` and reconstructs the full tree by folding all
context frames around the replacement.
Special case: if `z.ctx = []` (zipper at root), `transplant` returns `newFocus`.

This matches CLRS `TRANSPLANT(T, u, v)`:
- `u` is identified by `z.focus`
- `v` is `newFocus`

### 4. Iterative search and predecessors/successors

```lean
def searchIter (x : Nat) (t : BSTree) : Bool
theorem searchIter_eq_search (x : Nat) (t : BSTree) : searchIter x t = search x t

def successorZipper (x : Nat) (t : BSTree) : Option Nat
theorem successorZipper_eq_successor? (x : Nat) (t : BSTree)
    (ht : Ordered t) (hx : InTree x t) :
    successorZipper x t = successor? x t

def predecessorZipper (x : Nat) (t : BSTree) : Option Nat
theorem predecessorZipper_eq_predecessor? (x : Nat) (t : BSTree)
    (ht : Ordered t) (hx : InTree x t) :
    predecessorZipper x t = predecessor? x t
```

### 5. `deleteViaTransplant`

```lean
def deleteViaTransplant (x : Nat) : BSTree -> List Frame -> BSTree
```

The context carries the parent path while the function searches for `x`.  At
the matching node it uses the same successor-replacement shape as the existing
functional `deleteRoot`:

1. If the right child is empty, transplant the left child into the context.
2. Otherwise, transplant `node left (minKey right) (deleteMin right)` into the
   context.

**Correspondence:** The existing `delete` uses `deleteRoot` which replaces
the root with `minKey right`. `deleteViaTransplant` mirrors that replacement and
uses `transplant` to rebuild the parent context.  This is a functional
refinement boundary, not yet a line-by-line mutable implementation of the three
CLRS pointer cases.  Structural equivalence is unconditional:

```lean
theorem deleteViaTransplant_eq_delete (x : Nat) (t : BSTree) :
    deleteViaTransplant x t [] = delete x t
```

## Invariants

### `Zipper.Valid`

```lean
def Zipper.Valid (z : Zipper) : Prop
```

A zipper satisfies this local helper when:

1. `z.toTree` is `Ordered`
2. If the immediate frame contributes an upper bound, every focus key is below it
3. If the immediate frame contributes a lower bound, every focus key is above it

The stronger full-context replacement theorem does not rely on a claimed
`searchZipper` preservation lemma.  It takes reconstructed-tree ordering and
range-preservation hypotheses explicitly and proves them inductively over the
whole context.

## Correctness Theorems (Acceptance Criteria)

| # | Theorem | Meaning |
|---|---------|---------|
| AC-1 | `searchZipper_toTree` | `(searchZipper x t).toTree = t` |
| AC-2 | `searchIter_eq_search` | Iterative search = functional search |
| AC-3 | `transplant_preserves_ordered` | TRANSPLANT preserves BST ordering when the replacement is ordered and preserves every old focus range bound |
| AC-4 | `deleteViaTransplant_eq_delete` | Deletion expressed through transplant = existing functional `delete` |
| AC-5 | `successorZipper_eq_successor?` / `predecessorZipper_eq_predecessor?` | Parent-ascent navigation = functional query on ordered trees for present keys |

**AC-4 fallback:** structural equality `deleteViaTransplant x t = delete x t` is
the target (the two should coincide because the existing `deleteRoot` already
replaces the root with `minKey right`, i.e. the successor). If the structural
proof proves intractable, the accepted fallback is the pair
`inTree_deleteViaTransplant_iff` (matching `inTree_delete_iff`) +
`deleteViaTransplant_ordered` — i.e. same membership result and ordering
preservation, which is what "equivalence" means observationally.

## File Layout

All additions go into `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean`
inside `namespace CLRS.Chapter12.BSTree`, before its final `end BSTree`.
Structure:

```
/-! ## Parent-pointer refinement via Zipper -/
- Frame, Zipper types
- Frame.plug, Zipper.toTree
- Zipper.Valid
- searchZipper, searchIter
- transplant
- successorZipper, predecessorZipper
- deleteViaTransplant
- All correctness theorems
```

The new code is in the same `namespace CLRS.Chapter12.BSTree`.

## Proof Strategy

All correctness relies on `toTree` as the bridge: we never prove ordering
or membership directly against the zipper, we always `toTree` back to
`BSTree` and reuse the existing 30+ theorems.

For `transplant_preserves_ordered`: `toTree_ordered_of_subrange` inducts over
the full context and proves that replacing an ordered focus by an ordered
subtree preserving all inherited range bounds produces an `Ordered` tree.

For `deleteViaTransplant_eq_delete`: structural induction follows the search
path and reduces the replacement branch to the existing `deleteRoot`
definition via `toTree`.

## Out of Scope

- Imperative in-place mutation (RAM semantics)
- A line-by-line refinement of all three mutable CLRS `TREE-DELETE` cases
- `inorderTreeWalk` (trivial in functional setting)
- Connection to red-black tree rotations (→ #8, Ch14)
- Executable cost model
