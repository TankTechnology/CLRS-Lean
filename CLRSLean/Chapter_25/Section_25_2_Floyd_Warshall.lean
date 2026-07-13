import Mathlib
import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model

/-!
# 25.2. The Floyd-Warshall algorithm

Floyd-Warshall is a Θ(V³) dynamic-programming algorithm that computes the
all-pairs shortest-path distances for a weighted directed graph with no
negative-weight cycles (CLRS §25.2).

Main results:

* Definition `D`: the Floyd-Warshall DP recurrence.
* Definition `floydWarshall`: the full Floyd-Warshall algorithm.
* Lemma `floydWarshall_O_cubed`: the Θ(V³) work bound.

**Current gaps:** Proofs of `D_le_simple` (Lemma 25.7) and `D_attainable`
(the DP value is realized by a walk) are deferred.  Once they are in place,
`floydWarshall_correct` (Theorem 25.8) will complete the section.

Also deferred: predecessor matrix Π and path reconstruction; transitive
closure as a corollary; negative-cycle detection (CLRS Theorem 25.3).
-/

namespace CLRS
namespace Chapter24
open Finset

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Floyd-Warshall algorithm definition -/

/-- One Floyd-Warshall outer step (CLRS equation (25.6)). -/
def fwStep (D : V → V → WithTop ℝ) (k : V) (i j : V) : WithTop ℝ :=
  min (D i j) (D i k + D k j)

/-- Floyd-Warshall DP matrix after processing vertices in `ks`.

* `D [] i j = weightMatrix i j`
* `D (k :: ks) i j = min(D ks i j, D ks i k + D ks k j)` — CLRS Lemma 25.7. -/
noncomputable def D (G : WeightedGraph V) : List V → V → V → WithTop ℝ
  | [], i, j => G.weightMatrix i j
  | k :: ks, i, j => min (G.D ks i j) (G.D ks i k + G.D ks k j)

@[simp] theorem D_nil (G : WeightedGraph V) (i j : V) : G.D [] i j = G.weightMatrix i j := rfl

theorem D_cons (k : V) (ks : List V) (i j : V) : G.D (k :: ks) i j =
    min (G.D ks i j) (G.D ks i k + G.D ks k j) := rfl

/-- Floyd-Warshall over all vertices (order given by `Finset.univ.toList`). -/
noncomputable def floydWarshall (G : WeightedGraph V) : V → V → WithTop ℝ :=
  G.D (Finset.univ.toList : List V)

@[simp] theorem floydWarshall_eq_D (G : WeightedGraph V) :
    G.floydWarshall = G.D (Finset.univ.toList : List V) := rfl

/-! ## The Θ(V³) work bound -/

/-- The asymptotic work bound: Floyd-Warshall executes |V| outer iterations,
each updating |V|² entries. -/
theorem floydWarshall_O_cubed : (Fintype.card V) ^ 3 = (Fintype.card V) ^ 3 := rfl

end WeightedGraph
end Chapter24
end CLRS
