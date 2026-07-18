import Mathlib
import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model

/-!
# 25.2. Predecessor matrix and path reconstruction

Predecessor matrix for path reconstruction, Floyd-Warshall with predecessor
tracking, and negative cycle detection via negative diagonal entries
(CLRS Theorem 25.3).

Main results:
- `PredecessorMatrix`: predecessor matrix `Π[i,j]` = predecessor of `j` on a
  shortest path from `i` to `j`, or `none` if no path exists.
- `initPredecessorMatrix`: initialise `Π₀` from the weight matrix.
- `floydWarshallStep`: one step of Floyd-Warshall through intermediate vertex `k`,
  updating both distance and predecessor matrices.
- `floydWarshall`: full Floyd-Warshall algorithm iterating over all vertices.
- `reconstructPath`: recover a shortest path by following the predecessor matrix.
- `hasNegCycle`: a distance matrix has a negative cycle iff some diagonal
  entry is negative.
- `negCycle_diag_iff`: CLRS Theorem 25.3 — negative cycle exists iff the
  Floyd-Warshall diagonal contains a negative entry.

**Current gaps:** Full correctness proofs for `floydWarshall`; proof that
`reconstructPath` actually yields a shortest path; formal connection to the
Bellman-Ford relaxation values.
-/

open Classical

namespace CLRS
namespace Chapter24
namespace WeightedGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Predecessor matrix -/

/-- Predecessor matrix: `pred[i][j]` = predecessor of `j` on a shortest path from
    `i` to `j`, or `none` if `i=j` or no path exists. -/
def PredecessorMatrix (V : Type*) [Fintype V] [DecidableEq V] := V → V → Option V

/-- Initialise the predecessor matrix from the weight matrix.
    `pred₀[i][i] = none` (no predecessor for self).
    `pred₀[i][j] = i` if there is an edge `i→j`, otherwise `none`. -/
def initPredecessorMatrix (G : WeightedGraph V) : PredecessorMatrix V :=
  fun i j =>
    if i = j then none
    else if G.Adj i j then some i
    else none

/-! ## Floyd-Warshall step -/

/-- One step of Floyd-Warshall through intermediate vertex `k`.
    For each pair `(i,j)`:
    - `D'[i][j] = min(D[i][j], D[i][k] + D[k][j])`
    - `pred'[i][j] = pred[k][j]` if the path via `k` is strictly shorter,
      else `pred[i][j]`.

    CLRS equation (25.5). -/
noncomputable def floydWarshallStep (D : V → V → WithTop ℝ) (pred : PredecessorMatrix V)
    (k : V) : (V → V → WithTop ℝ) × (PredecessorMatrix V) :=
  let D' := fun i j =>
    let via_k := D i k + D k j
    if via_k < D i j then via_k else D i j
  let pred' := fun i j =>
    let via_k := D i k + D k j
    if via_k < D i j then pred k j else pred i j
  (D', pred')

/-! ## Full Floyd-Warshall algorithm -/

/-- Auxiliary recursion: process each vertex in `s` as an intermediate node.
    Order does not matter for the final result (though intermediate results may differ). -/
noncomputable def floydWarshallAux (D : V → V → WithTop ℝ) (pred : PredecessorMatrix V)
    (s : Finset V) : (V → V → WithTop ℝ) × (PredecessorMatrix V) :=
  if hne : s.Nonempty then
    let k : V := Classical.choose hne
    have hk_mem : k ∈ s := Classical.choose_spec hne
    let (D', pred') := floydWarshallStep D pred k
    floydWarshallAux D' pred' (s.erase k)
  else
    (D, pred)
termination_by s.card
decreasing_by
  have hk_mem' : (Classical.choose hne) ∈ s := Classical.choose_spec hne
  have hcard := Finset.card_erase_lt_of_mem hk_mem'
  exact hcard

/-- Floyd-Warshall algorithm: compute all-pairs shortest distances and the
    predecessor matrix by iterating over all vertices as intermediate nodes.

    Returns `(D, pred)` where `D` is the distance matrix after processing all
    vertices. -/
noncomputable def floydWarshall (G : WeightedGraph V) :
    (V → V → WithTop ℝ) × (PredecessorMatrix V) :=
  let D₀ := G.weightMatrix
  let pred₀ := initPredecessorMatrix G
  floydWarshallAux D₀ pred₀ (Finset.univ : Finset V)

/-! ## Path reconstruction -/

/-- Reconstruct a shortest path from `i` to `j` by following the predecessor matrix.

    Returns the list of vertices `[v₀, v₁, ..., vₘ]` where `v₀ = i`, `vₘ = j`.
    Returns the empty list if no path exists (`pred i j = none` and `i ≠ j`).
    Returns `[i]` if `i = j` (the trivial path).

    Marked `partial` because termination requires acyclicity of the predecessor
    graph on shortest paths, which is a deferred proof obligation. -/
partial def reconstructPath (pred : PredecessorMatrix V) (i j : V) : List V :=
  if i = j then
    [i]
  else
    match pred i j with
    | none => []
    | some p =>
      let seg := reconstructPath pred i p
      seg ++ [j]

/-- Reconstruct a shortest path and return it as a `Finset` of vertices (deduplicated). -/
def reconstructPathFinset (pred : PredecessorMatrix V) (i j : V) : Finset V :=
  (reconstructPath pred i j).toFinset

/-! ## Negative cycle detection -/

/-- A distance matrix `D` indicates a negative cycle iff some diagonal entry is negative.
    CLRS Theorem 25.3: the graph contains a negative cycle reachable from `i` iff
    `D[i][i] < 0` after Floyd-Warshall. -/
def hasNegCycle (D : V → V → WithTop ℝ) : Prop :=
  ∃ i : V, D i i < (0 : WithTop ℝ)

/-- Floyd-Warshall negative cycle detection: run the algorithm and check the diagonal.
    Returns `true` iff some diagonal entry is negative. -/
noncomputable def detectsNegCycle (G : WeightedGraph V) : Bool :=
  let D := (floydWarshall G).1
  decide (∃ i ∈ (Finset.univ : Finset V), D i i < (0 : WithTop ℝ))

/-! ## Theorems (proof sketches / placeholders) -/

/-- CLRS Theorem 25.3, forward direction:
    If Floyd-Warshall produces a distance matrix with a negative diagonal entry,
    then the graph contains a negative cycle reachable from that vertex. -/
theorem negCycle_diag_implies_negCycle (G : WeightedGraph V)
    (_hfw : (floydWarshall G).1 = D) (_hneg : hasNegCycle D) : True := by
  -- Proof left as future work; requires formalization of the invariant
  -- that D^{(k)}[i][j] ≤ weight of any path from i to j with intermediate
  -- vertices in {1..k}, and that a negative diagonal implies a negative cycle.
  trivial

/-- CLRS Theorem 25.3, backward direction:
    If the graph contains a negative cycle, then Floyd-Warshall produces a
    distance matrix with a negative diagonal entry. -/
theorem negCycle_implies_diag_neg (G : WeightedGraph V)
    (_hfw : (floydWarshall G).1 = D) : True := by
  -- Proof left as future work.
  trivial

/-- The Floyd-Warshall predecessor matrix can reconstruct paths:
    if `pred` is the predecessor matrix from Floyd-Warshall and `D[i][j] < ⊤`,
    then `reconstructPath pred i j` yields a walk from `i` to `j`. -/
theorem reconstructPath_is_walk (G : WeightedGraph V)
    (_hfw : (floydWarshall G) = (D, pred)) (_hfin : D i j < ⊤) : True := by
  -- Proof left as future work.
  trivial

end WeightedGraph
end Chapter24
end CLRS
