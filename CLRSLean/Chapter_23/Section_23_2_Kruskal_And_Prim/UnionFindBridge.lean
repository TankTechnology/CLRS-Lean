import CLRSLean.Chapter_21
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim

/-!
# Chapter 23 - Union-find bridge for Kruskal

This module connects the executable Chapter 21 equivalence query to the
component-oracle interface used by the mathematical Kruskal proof.  The bridge
is extensional in the current selected edge set: a provider supplies a forest
and vertex encoding for every edge set and proves that forest equivalence is
exactly graph connectivity.  A later stateful scan refinement may reuse the
same invariant while constructing the states incrementally.

Main results:

- Theorem {lit}`UnionFindConnectivityRefinement.checkEquiv_iff_connected`:
  the executable Boolean query decides graph connectivity.
- Definition {lit}`UnionFindConnectivityRefinement.cycleTest`: a verified
  {lit}`CycleTestImplementation` accepted by the existing Kruskal theorems.
- Theorem {lit}`UnionFindConnectivityRefinement.cycleTest_correct`: the
  packaged implementation agrees with the component oracle.
-/

namespace CLRS
namespace MST

open Finset

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/--
A family of union-find states that represents connectivity in each selected
edge set.  The varying {lit}`Fin` type records that every supplied encoding is
in bounds for its corresponding executable forest.
-/
structure UnionFindConnectivityRefinement (G : Graph V E) where
  state : Finset E → Chapter21.Forest.State
  encode : ∀ A, V → Fin (state A).size
  sameSet_iff_connected :
    ∀ A u v,
      (Chapter21.Forest.partition (state A)).sameSet
          (encode A u) (encode A v) ↔
        G.ConnectedIn A u v

namespace UnionFindConnectivityRefinement

variable {G : Graph V E}

/-- The raw union-find cycle-test decision for a selected edge set. -/
def accept (R : UnionFindConnectivityRefinement G) (A : Finset E) (e : E) : Bool :=
  !((R.state A).checkEquiv
    (R.encode A (G.src e)) (R.encode A (G.dst e))).2

/-- The executable equivalence query agrees exactly with graph connectivity. -/
theorem checkEquiv_iff_connected (R : UnionFindConnectivityRefinement G)
    (A : Finset E) (u v : V) :
    ((R.state A).checkEquiv (R.encode A u) (R.encode A v)).2 = true ↔
      G.ConnectedIn A u v := by
  rw [Chapter21.Forest.checkEquiv_correct]
  exact R.sameSet_iff_connected A u v

/-- Union-find accepts exactly edges whose endpoints are not already connected. -/
theorem accept_eq_true_iff_not_connected
    (R : UnionFindConnectivityRefinement G) (A : Finset E) (e : E) :
    R.accept A e = true ↔
      ¬G.ConnectedIn A (G.src e) (G.dst e) := by
  unfold accept
  rw [Bool.not_eq_true_eq_eq_false]
  rw [Chapter21.Forest.checkEquiv_eq_false_iff]
  exact not_congr (R.sameSet_iff_connected A (G.src e) (G.dst e))

/-- Convert connectivity faithfulness into faithfulness for any exact oracle. -/
theorem sameSet_iff_mem_component
    (R : UnionFindConnectivityRefinement G) (C : ComponentOracle G)
    (hExact : ExactComponentOracle G C) (A : Finset E) (u v : V) :
    (Chapter21.Forest.partition (R.state A)).sameSet
        (R.encode A u) (R.encode A v) ↔
      v ∈ C.component A u := by
  rw [R.sameSet_iff_connected, hExact]

/--
The Chapter 21 union-find query packaged as the Chapter 23 cycle-test
implementation.  The exact component oracle is used only as the mathematical
specification of the Boolean result.
-/
def cycleTest (R : UnionFindConnectivityRefinement G) (C : ComponentOracle G)
    (hExact : ExactComponentOracle G C) :
    CycleTestImplementation G C where
  accept := R.accept
  correct := by
    intro A e
    apply Bool.eq_iff_iff.2
    rw [R.accept_eq_true_iff_not_connected]
    simp only [acceptByComponent, decide_eq_true_iff]
    exact not_congr (hExact A (G.src e) (G.dst e)).symm

/-- Public correctness theorem for the packaged union-find cycle test. -/
theorem cycleTest_correct
    (R : UnionFindConnectivityRefinement G) (C : ComponentOracle G)
    (hExact : ExactComponentOracle G C) (A : Finset E) (e : E) :
    (R.cycleTest C hExact).accept A e = acceptByComponent G C A e :=
  (R.cycleTest C hExact).correct A e

end UnionFindConnectivityRefinement
end MST
end CLRS
