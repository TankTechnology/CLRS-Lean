import Mathlib

/-!
# CLRS Section 2.3 - MERGE definitions

This module defines the executable two-list core of the textbook `MERGE`
procedure.  A single execution records both the merged value and the number of
head-to-head element comparisons.
-/

namespace CLRS
namespace Chapter02

/-- The observable result of one list-level MERGE execution. -/
structure MergeExecution where
  value : List Nat
  comparisons : Nat
  outputWrites : Nat
deriving DecidableEq, Repr

/--
Merge two lists by repeatedly emitting the smaller current head.

The empty-list cases copy the remaining suffix without another element
comparison.  The recursive cases consume exactly one input element and charge
one head comparison.
-/
def mergeWithCost : List Nat → List Nat → MergeExecution
  | [], right => ⟨right, 0, right.length⟩
  | left, [] => ⟨left, 0, left.length⟩
  | x :: xs, y :: ys =>
      if x ≤ y then
        let rest := mergeWithCost xs (y :: ys)
        ⟨x :: rest.value, rest.comparisons + 1, rest.outputWrites + 1⟩
      else
        let rest := mergeWithCost (x :: xs) ys
        ⟨y :: rest.value, rest.comparisons + 1, rest.outputWrites + 1⟩
termination_by left right => left.length + right.length

/-- The value-only projection of the costed MERGE execution. -/
def merge (left right : List Nat) : List Nat :=
  (mergeWithCost left right).value

end Chapter02
end CLRS
