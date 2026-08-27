# Chapter 4 Integer Branching-Tree Design

## Goal

Close issue #336 with an explicit finite recursion tree for natural-number
subproblem sizes.  Unlike the existing fixed-depth real model, branches may
round differently and reach the base case at different depths.  The central
theorem must identify the tree's total cost with an independently stated
recurrence solution.

## Model

Keep `BranchingRecursionTree` unchanged: it is the useful exact-power,
common-depth model for level sums.  Add a separate unindexed tree:

```lean
inductive IntegerBranchingTree (Branch : Type)
  | leaf (size : Nat) (work : Real)
  | node (size : Nat) (work : Real)
      (children : Branch → IntegerBranchingTree Branch)
```

An `IntegerBranchingSpec` supplies a cutoff, one child-size function per
finite branch, local and base costs, and a proof that every child is strictly
smaller above the cutoff.  Its executable `build` function is defined by
well-founded recursion on the natural input size.  Consequently the tree is
finite without assuming a common height.

The tree exposes `rootSize`, `rootWork`, `totalCost`, and `height`.  Every
generated leaf carries a size at or below the cutoff; every generated
internal node carries a size above it.

## Semantic bridge

The recurrence predicate is deliberately independent of `build`:

```lean
def IntegerBranchingSpec.Satisfies (spec) (T : Nat → Real) : Prop :=
  (∀ n ≤ spec.cutoff, T n = spec.baseCost n) ∧
  (∀ n, spec.cutoff < n →
    T n = spec.localCost n + ∑ branch, T (spec.childSize branch n))
```

Strong induction proves

```lean
IntegerBranchingTree.totalCost (spec.build n) = T n
```

for every `T` satisfying the recurrence.  The equality therefore has proof
content: the recurrence is not defined to be the tree total.

## Textbook instances

### Balanced three-quarter example

Use branches `Fin 3`, cutoff `1`, child size `n / 4`, and local work
`c * n^2`.  Publish the familiar equation

```text
T(n) = 3 T(floor(n / 4)) + c n^2
```

and an exact equality between `T n` and the generated tree total.  The tree's
own cost function also yields a `FloorDivideRecurrence 3 4` instance with an
explicit forcing function.  Above the cutoff this forcing function is exactly
`c n^2`, connecting the concrete tree to the existing all-input master-theorem
layer without pretending that its separate analytic side conditions are
automatic.

### Unbalanced one-third/two-thirds example

Use two branches, cutoff `2`, child sizes `n / 3` and
`ceil((2*n) / 3)`, and local work `c * n`.  Prove both child sizes decrease
above the cutoff, prove the exact recurrence/tree equality, and exhibit a
small input whose two child subtrees have different heights.  The ceiling
branch is also related to the floor branch by a one-unit sandwich, and the
existing Akra--Bazzi theorem supplies the characteristic root `p = 1` for
the limiting ratios.

## Module boundaries

- `Branching/IntegerTree/Model.lean`: tree datatype and observations.
- `Branching/IntegerTree/Execution.lean`: specifications, well-founded build,
  leaf/internal invariants, and the exact recurrence bridge.
- `Branching/IntegerTree/Balanced.lean`: the `3T(n/4)+cn^2` instance and the
  all-input floor-recurrence connection.
- `Branching/IntegerTree/Unbalanced.lean`: floor/ceiling arithmetic, the
  `T(n/3)+T(2n/3)+cn` instance, unequal-depth witness, and Akra--Bazzi root.
- `Branching/IntegerTree.lean`: reader-facing facade.

The split keeps difficult termination, generic semantics, and arithmetic
examples independently compilable.

## Verification

Acceptance requires focused compilation of each new module, native evaluation
of representative tree shapes and totals, public interface checks, and native
axiom auditing of the flagship exact-equality theorems.  A Chapter 4 aggregate
build is reserved for the final checkpoint.

## Scope boundary

This closure proves the explicit finite integer recursion tree and its exact
recurrence semantics.  It reuses the already formalized master-theorem and
Akra--Bazzi asymptotic layers through honest bridge theorems; it does not
duplicate their analytic proofs or claim that rounding is definitionally
irrelevant.
