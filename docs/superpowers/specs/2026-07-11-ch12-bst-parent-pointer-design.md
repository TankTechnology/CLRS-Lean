# Design: Ch12.1 BST Parent-Pointer Refinement via Zipper

Date: 2026-07-11
Issue: [#6](https://github.com/TankTechnology/CLRS-Lean/issues/6)
Branch: `ch12-bst-parent-pointer`

## Summary

Add a Zipper layer over the existing inductive `BSTree` to encode parent-pointer
navigation. The zipper does NOT touch the existing type or its 30+ proved
theorems. It adds iterative search, `TRANSPLANT`, and `TREE-DELETE` using
transplant, each proved equivalent to the existing functional operations.

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

Replaces `z.focus` with `newFocus` in the full tree. Defined as:
`z.toTree` with the top frame plugged with `newFocus` instead of `z.focus`.
Special case: if `z.ctx = []` (zipper at root), `transplant` returns `newFocus`.

This matches CLRS `TRANSPLANT(T, u, v)`:
- `u` is identified by `z.focus`
- `v` is `newFocus`

### 4. Iterative search and predecessors/successors

```lean
def searchIter (x : Nat) (t : BSTree) : Bool
theorem searchIter_eq_search (x : Nat) (t : BSTree) : searchIter x t = search x t

def successorZipper (x : Nat) (t : BSTree) : Option Nat
theorem successorZipper_eq_successor? (x : Nat) (t : BSTree) (ht : Ordered t) :
    successorZipper x t = successor? x t

def predecessorZipper (x : Nat) (t : BSTree) : Option Nat
theorem predecessorZipper_eq_predecessor? (x : Nat) (t : BSTree) (ht : Ordered t) :
    predecessorZipper x t = predecessor? x t
```

### 5. `deleteViaTransplant`

```lean
def deleteViaTransplant (x : Nat) (t : BSTree) : BSTree
```

CLRS `TREE-DELETE` using `transplant` for all three cases:

1. `z.left = NIL` → transplant z with z.right
2. `z.right = NIL` → transplant z with z.left
3. Both children present → find successor y, if y is not z's right child
   then transplant y with y.right then wire y as z's replacement, finally
   transplant z with y

**Correspondence:** The existing `delete` uses `deleteRoot` which replaces
root with `minKey right`. `deleteViaTransplant` does the same via
transplant operations. Proved equivalent:

```lean
theorem deleteViaTransplant_eq_delete (x : Nat) (t : BSTree) (ht : Ordered t) :
    deleteViaTransplant x t = delete x t
```

## Invariants

### `Zipper.Valid`

```lean
def Zipper.Valid (z : Zipper) : Prop
```

A zipper is valid when:

1. `z.toTree` is `Ordered`
2. For each `fromLeft pk rs` frame: all keys in `z.focus` are `< pk`, and
   `pk` is less than all keys in `rs`
3. For each `fromRight pk ls` frame: all keys in `ls` are `< pk`, and
   `pk` is less than all keys in `z.focus`

This is preserved by `searchZipper` when starting from an `Ordered` tree.

## Correctness Theorems (Acceptance Criteria)

| # | Theorem | Meaning |
|---|---------|---------|
| AC-1 | `searchZipper_toTree` | `(searchZipper x t).toTree = t` |
| AC-2 | `searchIter_eq_search` | Iterative search = functional search |
| AC-3 | `transplant_preserves_ordered` | TRANSPLANT preserves BST ordering (given `Valid` zipper and `newFocus` within key bounds of the zipper's parent) |
| AC-4 | `deleteViaTransplant_eq_delete` | TREE-DELETE using transplant = existing functional `delete` on ordered trees |
| AC-5 | `successorZipper_eq_successor?` | Parent-pointer successor = functional successor on ordered trees |

**AC-4 fallback:** structural equality `deleteViaTransplant x t = delete x t` is
the target (the two should coincide because the existing `deleteRoot` already
replaces the root with `minKey right`, i.e. the successor). If the structural
proof proves intractable, the accepted fallback is the pair
`inTree_deleteViaTransplant_iff` (matching `inTree_delete_iff`) +
`deleteViaTransplant_ordered` — i.e. same membership result and ordering
preservation, which is what "equivalence" means observationally.

## File Layout

All additions go into `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean`
after the existing `end BSTree` line, before `end Chapter12` / `end CLRS`.
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

For `transplant_preserves_ordered`: we prove that `searchZipper` preserves
`Zipper.Valid`, and that `transplant` on a `Valid` zipper with a well-bounded
`newFocus` produces an `Ordered` tree.

For `deleteViaTransplant_eq_delete`: case analysis on the three CLRS
deletion cases, each reducing to the existing `delete`/`deleteRoot` theorems
via `toTree`.

## Out of Scope

- Imperative in-place mutation (RAM semantics)
- `inorderTreeWalk` (trivial in functional setting)
- Connection to red-black tree rotations (→ #8, Ch14)
- Executable cost model
