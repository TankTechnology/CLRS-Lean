# Chapter 6 Checked Heap Insert Design

## Goal

Close GitHub issue #320 at the repository's existing functional-array and
unit-control-step abstraction levels.  The result must support a heap stored in
an active prefix of a longer backing list, reject an invalid heap size, preserve
the inactive tail, and expose an honest logarithmic bubbling cost.

## Representation

For `heapSize ≤ a.length`, insertion splits the backing list into
`a.take heapSize` and `a.drop heapSize`.  It applies the already verified
full-prefix `arrayHeapInsert` to the active prefix and appends the inactive tail
again.  Thus the result has heap size `heapSize + 1`, backing length
`a.length + 1`, and multiset `key :: a`.

The checked API returns `none` exactly when `heapSize > a.length`.  This is a
total guard contract; the heap invariant itself remains a theorem hypothesis,
as in the existing checked priority-queue operations.

## Cost model

Instrument the existing upward-bubbling recursion with one unit for each
visited nonempty-fuel control frame.  The first projection must be definitionally
linked to the existing uncosted loop.  A parent step decreases
`⌊log₂(i + 1)⌋` by at least one, giving the bound
`cost ≤ ⌊log₂(i + 1)⌋ + 1`.  At insertion index `heapSize`, this becomes
`cost ≤ ⌊log₂(heapSize + 1)⌋ + 1`.

This is not a claim about Lean `List` allocation or RAM instruction costs.

## Module layout

- `Insert/Basic.lean`: the existing full-prefix insertion and its invariant,
  length, and permutation proofs.
- `Insert/Checked.lean`: active-prefix splitting, guard semantics, tail
  preservation, and checked state theorem.
- `Insert/Cost.lean`: costed bubbling, erasure, logarithmic bound, and the
  checked cost/state package.
- `Insert.lean`: stable facade importing the three focused modules.

## Verification

Build each focused module, the canonical and compatibility Chapter 6 roots,
the focused/public interface tests, and the Chapter 6 trust gate.  Then run the
repository consistency suite and `git diff --check`.
