import Mathlib

/-!
# Boundary-shift proof pattern

This module packages the small induction shape behind CLRS loop proofs where a
boundary moves one cell, one edge, or one processed item at a time.

Examples in the project include the heapsort sorted-suffix invariant, the
quicksort partition scan, counting-sort bucket scans, and Kruskal's processed
edge prefix.
-/

namespace CLRS
namespace ProofPatterns

/-- A trace of states indexed by a boundary position or iteration counter. -/
structure BoundaryTrace (State : Type u) where
  state : Nat -> State

/--
Unbounded boundary induction: if the invariant holds at boundary {lit}`0` and is
preserved by every one-step boundary shift, it holds at every boundary.
-/
theorem boundary_holds
    {State : Type u} {tr : BoundaryTrace State} {Invariant : Nat -> State -> Prop}
    (h0 : Invariant 0 (tr.state 0))
    (hstep :
      forall i, Invariant i (tr.state i) -> Invariant (i + 1) (tr.state (i + 1))) :
    forall n, Invariant n (tr.state n) := by
  intro n
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      exact hstep n ih

/--
Bounded boundary induction: the one-step preservation hypothesis only has to be
available while the boundary is below a fixed limit.
-/
theorem boundary_holds_upto
    {State : Type u} {tr : BoundaryTrace State} {Invariant : Nat -> State -> Prop}
    {limit : Nat}
    (h0 : Invariant 0 (tr.state 0))
    (hstep :
      forall i, i < limit ->
        Invariant i (tr.state i) -> Invariant (i + 1) (tr.state (i + 1))) :
    forall n, n <= limit -> Invariant n (tr.state n) := by
  intro n hn
  induction n with
  | zero =>
      exact h0
  | succ n ih =>
      have hn_lt : n < limit := Nat.lt_of_succ_le hn
      have hn_le : n <= limit := Nat.le_of_succ_le hn
      exact hstep n hn_lt (ih hn_le)

/--
Terminal readout: once a boundary invariant has been carried to a terminal
boundary, a reader-facing postcondition can be extracted there.
-/
theorem terminal_of_boundary
    {State : Type u} {tr : BoundaryTrace State} {Invariant : Nat -> State -> Prop}
    {Post : State -> Prop} {n : Nat}
    (hinv : Invariant n (tr.state n))
    (hterminal : Invariant n (tr.state n) -> Post (tr.state n)) :
    Post (tr.state n) :=
  hterminal hinv

end ProofPatterns
end CLRS
