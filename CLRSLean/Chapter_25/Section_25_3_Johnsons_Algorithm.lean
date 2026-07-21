import Mathlib
import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford
import CLRSLean.Chapter_24.Section_24_3_Dijkstra

/-!
# 25.3. Johnson's algorithm for sparse graphs

Johnson's algorithm computes all-pairs shortest paths in a weighted directed
graph with no negative-weight cycles.  It works in three stages:

1. **Potential via Bellman-Ford**: add a new source vertex `s` with zero-weight
   edges to every vertex, run Bellman-Ford from `s`, and set `h(v) = delta(s, v)`.
   The Bellman-Ford run also detects (and aborts for) any negative-weight cycle.

2. **Reweighting**: define a new weight function `w^(u,v) = w(u,v) + h(u) - h(v)`.
   By the triangle inequality of shortest paths, `w^ >= 0` for every edge,
   so Dijkstra's algorithm can be used from every vertex.

3. **|V| x Dijkstra**: run Dijkstra from every vertex on the reweighted graph
   and recover the true distances via `delta(u,v) = delta^(u,v) - h(u) + h(v)`.

Main results:

- Theorem `reweightedWeight_nonneg`: reweighted edge weights are nonnegative.
- Theorem `reweightedWalkWeight_eq`: `w^(p) = w(p) + h(u) - h(v)` for any
  walk `p` from `u` to `v` (telescoping property).

**Current gaps:** The `noNegCycle_johnsonAugmentedGraph` proof and the
shortest-path preservation theorem are deferred to a follow-up commit.
The reweighted weight function, telescoping property, and nonnegativity
lemma below are complete.
-/

namespace CLRS
namespace Chapter24
open Finset

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Johnson's algorithm preliminary definitions -/

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

/-! ## Reweighting with a potential function -/

/-- The reweighted weight function `w^(u,v) = w(u,v) + h(u) - h(v)`, where
`h : V -> RR` is a potential function (typically `delta(s, .)` from Bellman-Ford). -/
def reweightedWeight (h : V → ℝ) (u v : V) : ℝ :=
  G.w u v + h u - h v

@[simp] theorem reweightedWeight_eq (h : V → ℝ) (u v : V) :
    G.reweightedWeight h u v = G.w u v + h u - h v := rfl

/-- The **reweighted graph** `G^` has the same edge set as `G` but with the
reweighted weight function `w^`. -/
noncomputable def reweightedGraph (h : V → ℝ) : WeightedGraph V :=
  { edges := G.edges
  , w := G.reweightedWeight h
  }

@[simp] theorem edges_reweightedGraph (h : V → ℝ) :
    (G.reweightedGraph h).edges = G.edges := rfl

@[simp] theorem w_reweightedGraph (h : V → ℝ) (u v : V) :
    (G.reweightedGraph h).w u v = G.reweightedWeight h u v := rfl

/-- **Telescoping property.**  For any walk `p` from `u` to `v`, the reweighted
walk weight equals the original walk weight plus `h(u) - h(v)`. -/
theorem reweightedWalkWeight_eq (h : V → ℝ) (u v : V) (p : List V)
    (hp : G.IsWalkFrom u v p) : walkWeight (G.reweightedWeight h) p = walkWeight G.w p + h u - h v := by
  induction p generalizing u v with
  | nil => exact absurd rfl hp.ne_nil
  | cons a as ih =>
    have ha_u : a = u := by
      have hh := hp.head; simpa using hh
    rw [ha_u]
    rw [ha_u] at hp
    cases as with
    | nil =>
      have hv_u : v = u := by
        have hl := hp.last; simp at hl; exact hl.symm
      rw [hv_u]; simp [walkWeight, reweightedWeight]
    | cons b bs =>
      have h_chain : List.IsChain G.Adj (u :: b :: bs) := hp.chain
      have h_chain_rest : List.IsChain G.Adj (b :: bs) := by
        cases h_chain with
        | cons_cons _ htail => exact htail
      have h_walk_rest : G.IsWalkFrom b v (b :: bs) :=
        ⟨h_chain_rest, by simp, by simpa using hp.last⟩
      simp [walkWeight, reweightedWeight]
      rw [ih b v h_walk_rest]
      ring

/-- **Nonnegativity of reweighted weights.**  If the potential `h` satisfies
the triangle inequality `h(v) <= h(u) + w(u, v)` for every edge `(u, v)`, then
every reweighted edge weight is nonnegative. -/
theorem reweightedWeight_nonneg (h : V → ℝ)
    (h_triangle : ∀ u v, (u, v) ∈ G.edges → h v ≤ h u + G.w u v) :
    ∀ u v, (u, v) ∈ G.edges → 0 ≤ G.reweightedWeight h u v := by
  intro u v h_edge
  dsimp [reweightedWeight]
  have hineq : h v ≤ h u + G.w u v := h_triangle u v h_edge
  linarith

/-! ## Shortest-path preservation under reweighting -/

/-- Walks are identical in G and the reweighted graph (same edges). -/
lemma IsWalkFrom_reweighted_iff (h : V → ℝ) (u v : V) (p : List V) :
    (G.reweightedGraph h).IsWalkFrom u v p ↔ G.IsWalkFrom u v p := by
  simp [IsWalkFrom, WeightedGraph.Adj, edges_reweightedGraph]

/-- **Shortest-path preservation.**  For any potential `h`, the reweighted
shortest distance equals the original shortest distance shifted by
`h(u) - h(v)`.  This holds without any feasibility assumption on `h`. -/
theorem reweighted_isShortestDist (h : V → ℝ) (u v : V) (d : WithTop ℝ) :
    (G.reweightedGraph h).IsShortestDist u v
      (d + (h u : WithTop ℝ) - (h v : WithTop ℝ)) ↔
    G.IsShortestDist u v d := by
  let h_u := (h u : WithTop ℝ)
  let h_v := (h v : WithTop ℝ)
  have h_walk_iff := IsWalkFrom_reweighted_iff G h
  have h_fin_diff : h_u - h_v ≠ ⊤ := by
    have h_sub_eq : (h u : WithTop ℝ) - (h v : WithTop ℝ) = ((h u - h v : ℝ) : WithTop ℝ) := by simp
    rw [h_u, h_v, h_sub_eq]
    simp
  constructor
  · intro h_rsd; rcases h_rsd with ⟨h_lower, h_att⟩; constructor
    · intro p hp
      have hp_hat : (G.reweightedGraph h).IsWalkFrom u v p := (h_walk_iff u v p).mpr hp
      have h_bound := h_lower p hp_hat
      -- h_bound: d + h_u - h_v ≤ walkWeight (G.reweightedWeight h) p
      -- reweightedWalkWeight_eq: walkWeight (reweighted) p = walkWeight G.w p + h u - h v (in ℝ)
      have h_rw := reweightedWalkWeight_eq G h u v p hp
      -- Lift to WithTop ℝ
      have h_rw' : (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
          (walkWeight G.w p : WithTop ℝ) + h_u - h_v := by
        push_cast; simpa [h_u, h_v] using congrArg (fun x : ℝ => (x : WithTop ℝ)) h_rw
      -- Now: d + h_u - h_v ≤ (walkWeight G.w p : WithTop ℝ) + h_u - h_v
      -- Cancel h_u - h_v
      have h_bound' : d + h_u - h_v ≤ (walkWeight G.w p : WithTop ℝ) + h_u - h_v :=
        calc
          d + h_u - h_v ≤ (walkWeight (G.reweightedWeight h) p : WithTop ℝ) := h_bound
          _ = (walkWeight G.w p : WithTop ℝ) + h_u - h_v := h_rw'
      exact (WithTop.add_le_add_iff_right h_fin_diff).mp h_bound'
    · rcases h_att with (h_dtop | ⟨p, hp_hat, hpw⟩)
      · left; rw [h_dtop]; simp
      · right
        have hp : G.IsWalkFrom u v p := (h_walk_iff u v p).mp hp_hat
        refine ⟨p, hp, ?_⟩
        have h_rw := reweightedWalkWeight_eq G h u v p hp
        have h_rw' : (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
            (walkWeight G.w p : WithTop ℝ) + h_u - h_v := by
          push_cast; simpa [h_u, h_v] using congrArg (fun x : ℝ => (x : WithTop ℝ)) h_rw
        have hpw' : (walkWeight G.w p : WithTop ℝ) + h_u - h_v = d + h_u - h_v := by
          simpa [h_rw'] using hpw
        -- hpw': (walkWeight G.w p : WithTop ℝ) + h_u - h_v = d + h_u - h_v
        have h_eq : (walkWeight G.w p : WithTop ℝ) = d := by
          apply le_antisymm
          · exact (WithTop.add_le_add_iff_right h_fin_diff).mp (by rw [hpw'])
          · exact (WithTop.add_le_add_iff_right h_fin_diff).mp (by rw [hpw'])
        rw [h_eq]
  · intro h_sd; rcases h_sd with ⟨h_lower, h_att⟩; constructor
    · intro p hp_hat
      have hp : G.IsWalkFrom u v p := (h_walk_iff u v p).mp hp_hat
      have h_rw := reweightedWalkWeight_eq G h u v p hp
      have h_rw' : (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
          (walkWeight G.w p : WithTop ℝ) + h_u - h_v := by
        push_cast; simpa [h_u, h_v] using congrArg (fun x : ℝ => (x : WithTop ℝ)) h_rw
      calc
        d + h_u - h_v ≤ (walkWeight G.w p : WithTop ℝ) + h_u - h_v :=
          add_le_add_right h_lower (h_u - h_v)
        _ = (walkWeight (G.reweightedWeight h) p : WithTop ℝ) := h_rw'.symm
    · rcases h_att with (h_dtop | ⟨p, hp, hpw⟩)
      · left; rw [h_dtop]; simp
      · right
        have hp_hat : (G.reweightedGraph h).IsWalkFrom u v p := (h_walk_iff u v p).mpr hp
        have h_rw := reweightedWalkWeight_eq G h u v p hp
        have h_rw' : (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
            (walkWeight G.w p : WithTop ℝ) + h_u - h_v := by
          push_cast; simpa [h_u, h_v] using congrArg (fun x : ℝ => (x : WithTop ℝ)) h_rw
        calc
          (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
              (walkWeight G.w p : WithTop ℝ) + h_u - h_v := h_rw'
          _ = d + h_u - h_v := by rw [hpw]
        refine ⟨p, hp_hat, this⟩

end WeightedGraph
end Chapter24
end CLRS
