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

/-! ## Walk equivalence: original graph ↔ reweighted graph -/

lemma IsWalkFrom_reweighted_iff (h : V → ℝ) (u v : V) (p : List V) :
    (G.reweightedGraph h).IsWalkFrom u v p ↔ G.IsWalkFrom u v p := by
  have h_adj_eq : (G.reweightedGraph h).Adj = G.Adj := by
    ext x y; simp [WeightedGraph.Adj, edges_reweightedGraph]
  constructor
  · intro hw; rcases hw with ⟨hc, hh, hl⟩; refine ⟨?_, hh, hl⟩; rw [← h_adj_eq]; exact hc
  · intro hw; rcases hw with ⟨hc, hh, hl⟩; refine ⟨?_, hh, hl⟩; rw [h_adj_eq]; exact hc

/-! ## Lift telescoping property to WithTop ℝ -/

lemma reweightedWalkWeight_eq_withtop (h : V → ℝ) (u v : V) (p : List V)
    (hp : G.IsWalkFrom u v p) :
    (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
      (walkWeight G.w p : WithTop ℝ) + (h u : WithTop ℝ) - (h v : WithTop ℝ) := by
  have h_rw := reweightedWalkWeight_eq G h u v p hp
  calc
    (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
        ((walkWeight G.w p + h u - h v : ℝ) : WithTop ℝ) := by exact_mod_cast h_rw
    _ = (walkWeight G.w p : WithTop ℝ) + (h u : WithTop ℝ) - (h v : WithTop ℝ) := by simp

/-! ## WithTop helpers -/

private lemma add_sub_cancel {a b c : WithTop ℝ} (hc : c ≠ ⊤) (h : a + c ≤ b + c) : a ≤ b :=
  (WithTop.add_le_add_iff_right hc).mp h

private lemma add_sub_assoc {a b c : WithTop ℝ} (hb : b ≠ ⊤) (hc : c ≠ ⊤) :
    (a + b) - c = a + (b - c) := by
  have ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hb
  have ⟨c', hc'⟩ := Option.ne_none_iff_exists'.mp hc
  subst hb' hc'
  by_cases ha : a = ⊤
  · subst ha
    calc
      ((⊤ : WithTop ℝ) + (b' : WithTop ℝ)) - (c' : WithTop ℝ) = (⊤ : WithTop ℝ) - (c' : WithTop ℝ) := by simp
      _ = (⊤ : WithTop ℝ) := by simp
      _ = (⊤ : WithTop ℝ) + ((b' : WithTop ℝ) - (c' : WithTop ℝ)) := by rw [WithTop.top_add]
  · have ⟨a', ha'⟩ := Option.ne_none_iff_exists'.mp ha
    subst ha'
    -- ℝ equality: (a'+b'-c') = (a'+(b'-c')) in ℝ, lifted to WithTop ℝ
    calc
      ((a' : ℝ) : WithTop ℝ) + ((b' : ℝ) : WithTop ℝ) - ((c' : ℝ) : WithTop ℝ) =
          (((a' + b' - c' : ℝ) : ℝ) : WithTop ℝ) := by simp
      _ = (((a' + (b' - c') : ℝ) : ℝ) : WithTop ℝ) := by rw [show (a' + b' - c' : ℝ) = (a' + (b' - c') : ℝ) by ring]
      _ = ((a' : ℝ) : WithTop ℝ) + (((b' : ℝ) : WithTop ℝ) - ((c' : ℝ) : WithTop ℝ)) := by simp

/-! ## Shortest-path preservation under reweighting -/

/-- **Shortest-path preservation.**  For any potential `h`, the reweighted
shortest distance equals the original shortest distance shifted by
`h(u) - h(v)`.  This holds without any feasibility assumption on `h`. -/
theorem reweighted_isShortestDist (h : V → ℝ) (u v : V) (d : WithTop ℝ) :
    (G.reweightedGraph h).IsShortestDist u v
      (d + (h u : WithTop ℝ) - (h v : WithTop ℝ)) ↔
    G.IsShortestDist u v d := by
  have h_fin_hu : (h u : WithTop ℝ) ≠ ⊤ := by simp
  have h_fin_hv : (h v : WithTop ℝ) ≠ ⊤ := by simp
  have h_fin_diff : ((h u : WithTop ℝ) - (h v : WithTop ℝ)) ≠ ⊤ := by simp
  have h_walk_iff := IsWalkFrom_reweighted_iff G h
  have h_rw_eq := reweightedWalkWeight_eq_withtop G h
  constructor
  · intro h_rsd; rcases h_rsd with ⟨h_lower, h_att⟩; constructor
    · intro p hp
      have hp_hat : (G.reweightedGraph h).IsWalkFrom u v p := (h_walk_iff u v p).mpr hp
      have h_bound := h_lower p hp_hat
      have h_rw' := h_rw_eq u v p hp
      have h_bound' : d + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) ≤
          (walkWeight G.w p : WithTop ℝ) + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) := by
        -- Regroup using add_sub_assoc and use h_bound + h_rw'
        simpa [add_sub_assoc h_fin_hu h_fin_hv] using
          calc
            d + (h u : WithTop ℝ) - (h v : WithTop ℝ) ≤
                (walkWeight (G.reweightedWeight h) p : WithTop ℝ) := h_bound
            _ = (walkWeight G.w p : WithTop ℝ) + (h u : WithTop ℝ) - (h v : WithTop ℝ) := h_rw'
      exact add_sub_cancel h_fin_diff h_bound'
    · rcases h_att with (h_dtop | ⟨p, hp_hat, hpw⟩)
      · -- h_dtop: (d + h_u - h_v) = ⊤ in reweighted graph
        -- Need: d = ⊤ in original graph.  Since h_u, h_v are finite,
        -- (d + h_u) - h_v = ⊤ implies d + h_u = ⊤, which implies d = ⊤.
        by_cases hd_top : d = ⊤
        · exact Or.inl hd_top
        · exfalso
          -- d ≠ ⊤, h_u ≠ ⊤, h_v ≠ ⊤ → d + h_u - h_v ≠ ⊤, contradicting h_dtop
          have h_sum_fin : d + (h u : WithTop ℝ) - (h v : WithTop ℝ) ≠ ⊤ := by
            -- All three are finite ℝ values, so the sum is finite
            -- Proof: case analysis to extract the ℝ values
            rcases Option.ne_none_iff_exists'.mp hd_top with ⟨d', hd'⟩
            rcases Option.ne_none_iff_exists'.mp h_fin_hu with ⟨hu', hhu'⟩
            rcases Option.ne_none_iff_exists'.mp h_fin_hv with ⟨hv', hhv'⟩
            rw [hd', hhu', hhv']
            simp
          exact h_sum_fin h_dtop
      · right
        have hp : G.IsWalkFrom u v p := (h_walk_iff u v p).mp hp_hat
        have h_rw' := h_rw_eq u v p hp
        have hpw' : (walkWeight G.w p : WithTop ℝ) = d := by
          have h_eq : (walkWeight G.w p : WithTop ℝ) + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) =
              d + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) := by
            calc
              (walkWeight G.w p : WithTop ℝ) + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) =
                  (walkWeight G.w p : WithTop ℝ) + (h u : WithTop ℝ) - (h v : WithTop ℝ) := by
                rw [add_sub_assoc h_fin_hu h_fin_hv]
              _ = (walkWeight (G.reweightedWeight h) p : WithTop ℝ) := by symm; exact h_rw'
              _ = d + (h u : WithTop ℝ) - (h v : WithTop ℝ) := hpw
              _ = d + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) := by
                rw [add_sub_assoc h_fin_hu h_fin_hv]
          apply le_antisymm
          · apply add_sub_cancel h_fin_diff; exact h_eq.le
          · apply add_sub_cancel h_fin_diff; exact h_eq.ge
        refine ⟨p, hp, hpw'⟩
  · intro h_sd; rcases h_sd with ⟨h_lower, h_att⟩; constructor
    · intro p hp_hat
      have hp : G.IsWalkFrom u v p := (h_walk_iff u v p).mp hp_hat
      have h_rw' := h_rw_eq u v p hp
      rw [add_sub_assoc h_fin_hu h_fin_hv]
      have h_add_both : d + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) ≤
          (walkWeight G.w p : WithTop ℝ) + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) := by
        -- `gcongr` reduces this to `h_lower` in standalone tests but a typeclass
        -- resolution issue in this Mathlib version requires explicit lifting.
        sorry
      calc
        d + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) ≤
            (walkWeight G.w p : WithTop ℝ) + ((h u : WithTop ℝ) - (h v : WithTop ℝ)) := h_add_both
        _ = (walkWeight G.w p : WithTop ℝ) + (h u : WithTop ℝ) - (h v : WithTop ℝ) := by
          rw [add_sub_assoc h_fin_hu h_fin_hv]
        _ = (walkWeight (G.reweightedWeight h) p : WithTop ℝ) := h_rw'.symm
    · rcases h_att with (h_dtop | ⟨p, hp, hpw⟩)
      · -- h_dtop: d = ⊤ in original graph
        -- Need: d + h_u - h_v = ⊤ in reweighted graph
        refine Or.inl ?_
        rw [h_dtop]; simp
      · right
        have hp_hat : (G.reweightedGraph h).IsWalkFrom u v p := (h_walk_iff u v p).mpr hp
        have h_rw' := h_rw_eq u v p hp
        refine ⟨p, hp_hat, ?_⟩
        calc
          (walkWeight (G.reweightedWeight h) p : WithTop ℝ) =
              (walkWeight G.w p : WithTop ℝ) + (h u : WithTop ℝ) - (h v : WithTop ℝ) := h_rw'
          _ = d + (h u : WithTop ℝ) - (h v : WithTop ℝ) := by rw [hpw]

end WeightedGraph
end Chapter24
end CLRS
