# Chapter 18 Structural Height Bound Design

## Goal

Close Chapter 18's final core theorem group by connecting the existing B-tree
shape invariants to the CLRS minimum-key and logarithmic-height bounds.

For a well-formed B-tree of minimum degree `t`, the proof must establish:

- every non-root subtree contains enough keys for its height;
- a root is either the legal empty tree or contains at least
  `2 * t ^ height - 1` keys;
- every nonempty well-formed tree satisfies the existing `minKeys` expression;
- every well-formed tree, including the empty root, satisfies the CLRS
  logarithmic height bound.

The legal empty tree is not excluded or hidden behind a strengthened
`WellFormed` definition.

## Existing Foundation and the Actual Gap

`Section_18_1_B_Tree_Model.lean` already defines:

- `keysOf`, which recursively flattens all represented key slots;
- `minKeys t h := 2 * t ^ h - 1`;
- `ChildBounded`, which connects key count and child count;
- `Occupancy`, which gives non-root branching at least `t` and internal-root
  branching at least two;
- `SameDepth`, which makes all children of an internal node have one common
  height;
- `heightOf` and `WellFormed`.

The current theorem named `minKeys_lower_bound` only unfolds the definition of
`minKeys`; it has no tree argument and is not a structural lower bound.

An unconditional theorem

```lean
minKeys t (heightOf tr) ≤ (keysOf tr).length
```

is false for the legal empty root: its height and key count are both zero,
while `minKeys t 0 = 1`.  The new theorem family must preserve that boundary.

## Approaches Considered

### A. Augmented counts with an explicit empty-root disjunction — selected

Define:

```lean
def totalKeys (tr : BTree) : Nat := (keysOf tr).length
```

Prove lower bounds in the subtraction-free form `power ≤ totalKeys + 1`.
For non-root subtrees:

```lean
t ^ (heightOf tr + 1) ≤ totalKeys tr + 1
```

For roots:

```lean
tr = node [] [] ∨
  2 * t ^ heightOf tr ≤ totalKeys tr + 1
```

The second inequality immediately yields the usual nonempty minimum-key
bound, while the first branch describes the one legal exception exactly.

This formulation matches the recursive branching proof and avoids repeated
natural-number subtraction.

### B. Prove `minKeys ≤ totalKeys` directly by recursion

This follows the textbook surface more literally, but every induction step
must normalize truncated subtraction.  It also encourages accidentally
stating a false theorem for the empty root.

### C. Require a nonempty root in `WellFormed`

This would make the textbook inequality unconditional, but would break the
existing empty-tree theorem and the insertion/deletion API.  The model already
correctly admits an empty root, so the theorem must adapt to the model rather
than weaken it.

Approach A is selected.

## Module Boundary

Create:

```text
CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
```

The new file imports the base model and owns the counting induction and public
height wrappers.  The base model remains focused on the data type, invariants,
and split preservation.  `CLRSLean/Chapter_18.lean` imports the new child
module, and `literate.toml` registers it below Section 18.1.

No insertion or deletion module is imported by the height proof.

## Public Contract

The focused public surface is:

```lean
def totalKeys (tr : BTree) : Nat

theorem totalKeys_node (ks : List Nat) (cs : List BTree) :
    totalKeys (node ks cs) =
      ks.length + (cs.map totalKeys).sum

theorem nonRoot_totalKeys_add_one_lower_bound
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hcb : ChildBounded tr)
    (hocc : Occupancy t false tr)
    (hsd : SameDepth tr) :
    t ^ (heightOf tr + 1) ≤ totalKeys tr + 1

theorem wellFormed_empty_or_totalKeys_add_one_lower_bound
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    tr = node [] [] ∨
      2 * t ^ heightOf tr ≤ totalKeys tr + 1

theorem wellFormed_empty_or_minKeys_le_totalKeys
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    tr = node [] [] ∨ minKeys t (heightOf tr) ≤ totalKeys tr

theorem wellFormed_minKeys_le_totalKeys
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr)
    (hne : tr ≠ node [] []) :
    minKeys t (heightOf tr) ≤ totalKeys tr

theorem wellFormed_height_log_bound
    (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2)
```

The contract has seven new tracked entries: one definition and six theorems.

## Counting Architecture

### Exact node accounting

Because `keysOf (node ks cs)` is `ks ++ cs.flatMap keysOf`,
`List.length_flatMap` gives:

```lean
totalKeys (node ks cs) =
  ks.length + (cs.map totalKeys).sum
```

For a nonempty child list, `ChildBounded` gives
`cs.length = ks.length + 1`.  Therefore:

```lean
totalKeys (node ks cs) + 1 =
  (cs.map (fun child => totalKeys child + 1)).sum
```

The augmented identity is the central recurrence: it counts every child
subtree and absorbs the parent separator keys into one `+1` per child.

### Non-root induction

Use structural induction through the `SameDepth` witness.

- Leaf: non-root occupancy gives at least `t - 1` keys, hence
  `t ≤ totalKeys + 1`.
- Internal node: each child inherits `ChildBounded`, non-root `Occupancy`, and
  `SameDepth`.  The induction hypothesis gives the same lower bound for every
  child because `SameDepth` equates their heights.  `List.sum_le_sum` lifts
  the per-child bounds to the augmented node count, and non-root occupancy
  supplies at least `t` children.

The proof counts list positions, not a `Finset`, so it remains valid without a
key-uniqueness assumption.

### Root theorem

Destruct the root.

- Empty children and empty keys: return the exact `node [] []` branch.
- Empty children and nonempty keys: root occupancy gives at least one key, so
  `2 * t ^ 0 ≤ totalKeys + 1`.
- Internal root: root occupancy supplies at least two children; every child is
  a non-root occupied subtree.  Apply the non-root theorem to each child,
  transport the exponent using `SameDepth`, and sum at least two identical
  powers.

## Textbook and Logarithmic Wrappers

In the nonempty branch,

```lean
2 * t ^ heightOf tr ≤ totalKeys tr + 1
```

implies

```lean
2 * t ^ heightOf tr - 1 ≤ totalKeys tr
```

by natural-number arithmetic, which is exactly
`minKeys t (heightOf tr) ≤ totalKeys tr`.

For the logarithmic theorem, the root inequality yields:

```lean
t ^ heightOf tr ≤ (totalKeys tr + 1) / 2
```

using `Nat.le_div_iff_mul_le`.  Then
`Nat.le_log_of_pow_le` applies because `2 ≤ t`.  The empty-root branch is
proved directly: both sides have lower bound zero and `heightOf` is zero.

## Test and Verification Design

Create `Tests/Chapter_18_Height_Interface.lean`.

The first test commit is intentionally RED and freezes all seven contracts.
It also includes executable boundary examples for:

- the legal empty root;
- a nonempty height-zero root;
- a height-one minimum-degree-two tree.

Implementation proceeds from exact accounting to the non-root induction, then
the root and log wrappers.

Every proof commit must pass:

```bash
lake env lean -DwarningAsError=true \
  CLRSLean/Chapter_18/Section_18_1_B_Tree_Model/HeightBound.lean
lake env lean -DwarningAsError=true \
  Tests/Chapter_18_Height_Interface.lean
lake build CLRSLean.Chapter_18
```

At completion, run all `Tests/Chapter_18*.lean` files with
`-DwarningAsError=true`, the progress/README/config consistency checks, an
unfinished-marker scan, and `git diff --check`.

Full-site `lake build :literateHtml` remains outside this single-chapter gate.

## Completion Semantics

Once these contracts pass and are registered:

- Chapter 18 has no remaining core correctness groups in the current
  functional B-tree model;
- its status may move from `partial` to the repository's
  correctness-complete label;
- disk pages, pointer mutation, I/O counts, and RAM costs remain explicitly
  optional lower-level refinements rather than hidden proof gaps.

