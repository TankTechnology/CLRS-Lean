import Mathlib
import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford
import CLRSLean.Chapter_24.Section_24_3_Dijkstra

/-!
# 25.3. Johnson's algorithm for sparse graphs

Johnson's algorithm computes all-pairs shortest paths in a weighted directed
graph with no negative-weight cycles.  It works in three stages:

1. **Potential via Bellman-Ford**: add a new source vertex `s` with zero-weight
   edges to every vertex, run Bellman-Ford from `s`, and set `h(v) = δ(s, v)`.
   The Bellman-Ford run also detects (and aborts for) any negative-weight cycle.

2. **Reweighting**: define a new weight function `ŵ(u,v) = w(u,v) + h(u) − h(v)`.
   By the triangle inequality of shortest paths, `ŵ(u,v) ≥ 0` for every edge,
   so Dijkstra's algorithm can be used from every vertex.

3. **|V| × Dijkstra**: run Dijkstra from every vertex on the reweighted graph
   and recover the true distances via `δ(u,v) = δ̂(u,v) − h(u) + h(v)`.

**Current gaps:** The full correctness proof of Johnson's algorithm is in
progress.  This section currently defines the augmented graph and the
reweighting infrastructure.
-/

namespace CLRS
namespace Chapter24
open Finset

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-- The **augmented graph** for Johnson's algorithm: add a fresh source vertex
`none` with zero-weight edges to every original vertex.

All original edges are preserved, with the original weights.  There are no
edges entering `none`, so any negative cycle in the original graph remains a
negative cycle (and no new negative cycles are introduced). -/
noncomputable def johnsonAugmentedGraph : WeightedGraph (Option V) :=
  { edges := (Finset.image (fun (v : V) => (none, some v)) Finset.univ) ∪
             (Finset.image (fun ((u, v) : V × V) => (some u, some v)) G.edges)
  , w := fun u v =>
      match u, v with
      | none, some v => 0
      | some u, some v => G.w u v
      | _, _ => 0
  }

@[simp] theorem mem_edges_johnsonAugmentedGraph_source (v : V) :
    (none, some v) ∈ G.johnsonAugmentedGraph.edges := by
  unfold johnsonAugmentedGraph; simp

@[simp] theorem mem_edges_johnsonAugmentedGraph_edge (u v : V) :
    (some u, some v) ∈ G.johnsonAugmentedGraph.edges ↔ (u, v) ∈ G.edges := by
  unfold johnsonAugmentedGraph; simp

/-- There are no edges entering `none` in the augmented graph. -/
theorem no_incoming_to_none_johnsonAugmentedGraph (u : Option V) :
    (u, none) ∉ G.johnsonAugmentedGraph.edges := by
  unfold johnsonAugmentedGraph; simp

end WeightedGraph
end Chapter24
end CLRS
