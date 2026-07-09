import Mathlib

/-!
# Interval-nesting proof pattern

This module packages the strict interval relations used by DFS timestamps,
recursive divide-and-conquer intervals, and adjacent-power sandwich arguments.
-/

namespace CLRS
namespace ProofPatterns

/-- A closed natural-number interval represented by its endpoints. -/
structure NatInterval where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

namespace NatInterval

/-- The interval endpoints are in the expected order. -/
def Valid (I : NatInterval) : Prop :=
  I.lo <= I.hi

/-- Interval {lit}`I` ends strictly before interval {lit}`J` begins. -/
def StrictlyBefore (I J : NatInterval) : Prop :=
  I.hi < J.lo

/-- Interval {lit}`inner` is strictly nested inside interval {lit}`outer`. -/
def NestedInside (inner outer : NatInterval) : Prop :=
  outer.lo < inner.lo ∧ inner.hi < outer.hi

theorem nestedInside_trans {I J K : NatInterval}
    (hij : NestedInside I J) (hjk : NestedInside J K) :
    NestedInside I K := by
  unfold NestedInside at *
  omega

theorem nestedInside_irrefl (I : NatInterval) :
    ¬ NestedInside I I := by
  intro h
  unfold NestedInside at h
  omega

theorem nestedInside_asymm {I J : NatInterval}
    (hij : NestedInside I J) :
    ¬ NestedInside J I := by
  intro hji
  unfold NestedInside at hij hji
  omega

theorem strictlyBefore_trans {I J K : NatInterval}
    (hij : StrictlyBefore I J) (hJ : Valid J) (hjk : StrictlyBefore J K) :
    StrictlyBefore I K := by
  unfold StrictlyBefore at *
  unfold Valid at hJ
  omega

theorem strictlyBefore_asymm {I J : NatInterval}
    (hij : StrictlyBefore I J) (hI : Valid I) (hJ : Valid J) :
    ¬ StrictlyBefore J I := by
  intro hji
  unfold StrictlyBefore Valid at *
  omega

theorem nestedInside_not_inner_before_outer {inner outer : NatInterval}
    (hinner : Valid inner) (hnest : NestedInside inner outer) :
    ¬ StrictlyBefore inner outer := by
  intro hbefore
  unfold Valid NestedInside StrictlyBefore at *
  omega

theorem nestedInside_not_outer_before_inner {inner outer : NatInterval}
    (hinner : Valid inner) (hnest : NestedInside inner outer) :
    ¬ StrictlyBefore outer inner := by
  intro hbefore
  unfold Valid NestedInside StrictlyBefore at *
  omega

end NatInterval

end ProofPatterns
end CLRS
