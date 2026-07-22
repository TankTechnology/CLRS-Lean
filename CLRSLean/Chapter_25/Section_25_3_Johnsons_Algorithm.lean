import Mathlib
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
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

- Lemma `isShortestDist_edge_ineq`: general triangle inequality `δ v ≤ δ u + w(u,v)`
  for the source `s`.
- Lemma `walk_johnsonAugmented_some_projection`: walks in the augmented graph
  project to walks in the original graph with the same weight.
- Theorem `noNegCycle_johnsonAugmentedGraph`: negative-cycle preservation in the
  augmented graph.
- Theorem `reweightedWeight_nonneg`: reweighted edge weights are nonnegative.
- Theorem `reweightedWalkWeight_eq`: `w^(p) = w(p) + h(u) - h(v)` for any
  walk `p` from `u` to `v` (telescoping property).
- Theorem `reweighted_isShortestDist`: shortest-path preservation under
  reweighting (the shift formula).
- Lemma `johnsonPotential_finite`: the Johnson potential `h(v)` is always finite.
- Lemma `johnsonPotential_triangle`: the potential satisfies the triangle
  inequality `h(v) ≤ h(u) + w(u,v)` for every edge `(u,v)` (CLRS Lemma 25.3).
- Theorem `johnsonReweightedNonneg`: the reweighted graph has nonnegative weights,
  so Dijkstra applies.
- Theorem `johnsonAllPairsDist_correct`: end-to-end correctness of Johnson's
  algorithm — `johnsonAllPairsDist` computes true all-pairs shortest distances
  (CLRS Theorem 25.6).

Notation conventions used in this section:

- `G` : weighted directed graph with vertex type `V`
- `G'` : the Johnson-augmented graph (new source `none`)
- `h` : Johnson potential function `h : V → ℝ`
- `Ĝ` : reweighted graph `G.reweightedGraph h`
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
        gcongr; exact h_lower p hp
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

/-! ## General triangle inequality -/

/-- The fundamental triangle inequality for shortest-path distances: for any edge
`(u, v)`, the shortest distance to `v` is at most the shortest distance to `u` plus
the edge weight.  No sign assumptions needed. -/
theorem isShortestDist_edge_ineq (s u v : V) (δ : V → WithTop ℝ)
    (hδ : ∀ t, G.IsShortestDist s t (δ t)) (h_edge : (u, v) ∈ G.edges) :
    δ v ≤ δ u + (G.w u v : WithTop ℝ) := by
  rcases (hδ u).2 with hutop | ⟨q, hq, hqw⟩
  · rw [hutop]; simp
  · have hq_ne : q ≠ [] := hq.ne_nil
    have h_last : q.getLast hq_ne = u := by
      have htemp := List.getLast?_eq_getLast_of_ne_nil hq_ne
      have h_eq_some : some u = some (q.getLast hq_ne) := by
        rw [← hq.last, htemp]
      exact (Option.some_inj.mp h_eq_some).symm
    have h_walk : G.IsWalkFrom s v (q ++ [v]) := by
      refine ⟨?_, ?_, ?_⟩
      · refine hq.chain.append (List.isChain_singleton v) ?_
        intro a ha b hb
        have ha_u : a = u := by
          rw [Option.mem_def, hq.last] at ha
          exact (Option.some.inj ha).symm
        subst ha_u
        have hb_v : b = v := by
          have hsing : [v].head? = some v := by simp
          rw [hsing, Option.mem_def] at hb
          simpa using hb.symm
        subst hb_v
        exact h_edge
      · rw [List.head?_append_of_ne_nil _ hq_ne]
        exact hq.head
      · simp
    have h_weight : (walkWeight G.w (q ++ [v]) : WithTop ℝ) = δ u + (G.w u v : WithTop ℝ) := by
      calc
        (walkWeight G.w (q ++ [v]) : WithTop ℝ) =
            ((walkWeight G.w q + G.w (q.getLast hq_ne) v : ℝ) : WithTop ℝ) := by
          exact_mod_cast walkWeight_append_singleton G.w q hq_ne v
        _ = (walkWeight G.w q : WithTop ℝ) + (G.w (q.getLast hq_ne) v : WithTop ℝ) := by simp
        _ = (walkWeight G.w q : WithTop ℝ) + (G.w u v : WithTop ℝ) := by rw [h_last]
        _ = δ u + (G.w u v : WithTop ℝ) := by rw [hqw]
    have h_bound : δ v ≤ (walkWeight G.w (q ++ [v]) : WithTop ℝ) := (hδ v).1 _ h_walk
    rw [h_weight] at h_bound
    exact h_bound

/-! ## Negative-cycle preservation in the augmented graph -/

/-- Every edge in the Johnson-augmented graph targets a `some _` vertex. -/
lemma edge_target_some {u v : Option V}
    (h : (u, v) ∈ G.johnsonAugmentedGraph.edges) : ∃ v', v = some v' := by
  unfold johnsonAugmentedGraph at h
  rcases Finset.mem_union.mp h with (h' | h')
  · rcases Finset.mem_image.mp h' with ⟨v', _, h_eq⟩
    have hv : v = some v' := by
      have h_snd := congrArg Prod.snd h_eq
      simpa using h_snd.symm
    exact ⟨v', hv⟩
  · rcases Finset.mem_image.mp h' with ⟨⟨u', v''⟩, _, h_eq⟩
    have hv : v = some v'' := by
      have h_snd := congrArg Prod.snd h_eq
      simpa using h_snd.symm
    exact ⟨v'', hv⟩

/-- Project a walk in the augmented graph from `some a` to `some b` to a walk
in `G` from `a` to `b` with the same weight. -/
lemma walk_johnsonAugmented_some_projection (a b : V) (c : List (Option V))
    (hc : G.johnsonAugmentedGraph.IsWalkFrom (some a) (some b) c) :
    ∃ (c' : List V), G.IsWalkFrom a b c' ∧
      walkWeight G.johnsonAugmentedGraph.w c = walkWeight G.w c' := by
  let G' := G.johnsonAugmentedGraph
  induction c generalizing a b with
  | nil => exact absurd rfl hc.ne_nil
  | cons x xs ih =>
    have hx : x = some a := by
      have hh := hc.head; simp at hh
      -- hh : some x = some (some a)
      simpa using hh
    -- Use rw instead of subst to preserve the IH
    rw [hx] at hc ⊢
    -- Now c = some a :: xs
    rcases (List.isChain_cons_iff G'.Adj (some a) xs).mp hc.chain with
      (hxs_nil | ⟨y, ys, h_adj, h_chain_rest, hxs_eq⟩)
    · -- xs = []
      rw [hxs_nil] at hc ⊢
      -- c = [some a]
      have hab : a = b := by
        have hl := hc.last; simp at hl; simpa using hl
      rw [hab]
      refine ⟨[b], ⟨List.isChain_singleton b, by simp, by simp⟩, ?_⟩
      simp [walkWeight]
    · -- xs = y :: ys; rewrite everything with this
      rw [hxs_eq] at hc ih ⊢
      -- c = some a :: y :: ys
      -- h_adj : G'.Adj (some a) y
      rcases edge_target_some G h_adj with ⟨c', hy⟩
      rw [hy] at hc ih h_adj h_chain_rest ⊢
      -- y = some c'; c = some a :: some c' :: ys
      have h_edge_orig : (a, c') ∈ G.edges :=
        (G.mem_edges_johnsonAugmentedGraph_edge a c').mp h_adj
      -- h_chain_rest : IsChain G'.Adj (some c' :: ys)
      -- Build rest walk
      have h_rest_head : (some c' :: ys).head? = some (some c') := by simp
      have h_rest_last : (some c' :: ys).getLast? = some (some b) := by
        have hl := hc.last; simpa using hl
      have h_rest_walk : G'.IsWalkFrom (some c') (some b) (some c' :: ys) :=
        ⟨h_chain_rest, h_rest_head, h_rest_last⟩
      rcases ih c' b h_rest_walk with ⟨c'_walk, h_walk, h_weight_eq⟩
      -- c'_walk starts at c' and ends at b; deconstruct into c' :: rest
      have h_c'_walk_ne_nil : c'_walk ≠ [] := h_walk.ne_nil
      rcases List.exists_cons_of_ne_nil h_c'_walk_ne_nil with ⟨d, rest, h_c'_walk_eq⟩
      -- d = c' because the walk starts at c'
      have hd_eq_c' : d = c' := by
        have h_walk_head := h_walk.head
        rw [h_c'_walk_eq] at h_walk_head
        simp at h_walk_head
        simpa using h_walk_head
      rw [hd_eq_c'] at h_c'_walk_eq
      -- h_c'_walk_eq : c'_walk = c' :: rest
      have h_walk' : G.IsWalkFrom c' b (c' :: rest) := by
        rwa [h_c'_walk_eq] at h_walk
      have h_weight_eq' : walkWeight G'.w (some c' :: ys) = walkWeight G.w (c' :: rest) := by
        rwa [h_c'_walk_eq] at h_weight_eq
      -- Build full walk a :: c' :: rest
      have h_full_chain : List.IsChain G.Adj (a :: c' :: rest) := by
        rw [List.isChain_cons_iff G.Adj a (c' :: rest)]
        right; exact ⟨c', rest, h_edge_orig, h_walk'.chain, rfl⟩
      have h_full_last : (a :: c' :: rest).getLast? = some b := by
        have hlast := h_walk'.last; simpa using hlast
      have h_full_walk : G.IsWalkFrom a b (a :: c' :: rest) :=
        ⟨h_full_chain, by simp, h_full_last⟩
      have h_weight_eq_full : walkWeight G'.w (some a :: some c' :: ys) =
          walkWeight G.w (a :: c' :: rest) := by
        calc
          walkWeight G'.w (some a :: some c' :: ys) =
              G'.w (some a) (some c') + walkWeight G'.w (some c' :: ys) := rfl
          _ = G.w a c' + walkWeight G'.w (some c' :: ys) := by simp [G', johnsonAugmentedGraph]
          _ = G.w a c' + walkWeight G.w (c' :: rest) := by rw [h_weight_eq']
          _ = walkWeight G.w (a :: c' :: rest) := rfl
      exact ⟨a :: c' :: rest, h_full_walk, h_weight_eq_full⟩

/-- **Negative-cycle preservation.** The Johnson-augmented graph has no negative
cycle iff the original graph has none. -/
theorem noNegCycle_johnsonAugmentedGraph (hNC : G.NoNegCycle) :
    G.johnsonAugmentedGraph.NoNegCycle := by
  intro x c hc
  let G' := G.johnsonAugmentedGraph
  cases x with
  | none =>
    rcases List.getLast?_eq_some_iff.mp hc.last with ⟨l', hl'⟩
    subst hl'
    by_cases hl'_empty : l' = []
    · subst hl'_empty; simp
    · have hchain : List.IsChain G'.Adj (l' ++ [none]) := hc.chain
      rcases List.isChain_append.mp hchain with ⟨_, _, h_conn⟩
      have h_last_eq : l'.getLast? = some (l'.getLast hl'_empty) :=
        List.getLast?_eq_getLast_of_ne_nil hl'_empty
      have h_none_head_eq : ([none] : List (Option V)).head? = some (none : Option V) := by simp
      rw [h_last_eq, h_none_head_eq] at h_conn
      have h_edge : G'.Adj (l'.getLast hl'_empty) none :=
        h_conn (l'.getLast hl'_empty) rfl none rfl
      exact absurd h_edge (G.no_incoming_to_none_johnsonAugmentedGraph (l'.getLast hl'_empty))
  | some x' =>
    rcases walk_johnsonAugmented_some_projection G x' x' c hc with ⟨c', h_walk', h_weight_eq⟩
    have h_nonneg : 0 ≤ walkWeight G.w c' := hNC x' c' h_walk'
    rw [h_weight_eq]
    exact h_nonneg

/-! ## Johnson potential function -/

/-- The **Johnson potential** `h(v) = δ(none, some v)` from Bellman-Ford on the
augmented graph.  Finite because of the direct `none→some v` edge (weight 0). -/
lemma johnsonPotential_finite (_hNC : G.NoNegCycle) (v : V) :
    G.johnsonAugmentedGraph.relaxDist none (Fintype.card (Option V) - 1) (some v) ≠ ⊤ := by
  let G' := G.johnsonAugmentedGraph
  have h1 : G'.relaxDist none 1 (some v) ≤ (0 : WithTop ℝ) := by
    calc
      G'.relaxDist none 1 (some v) = G'.relaxStep (G'.relaxDist none 0) (some v) := rfl
      _ ≤ G'.relaxDist none 0 none + (G'.w none (some v) : WithTop ℝ) :=
        G'.relaxStep_le_pred (by simp [G', mem_edges_johnsonAugmentedGraph_source])
      _ = (0 : WithTop ℝ) + (0 : WithTop ℝ) := by simp [G', johnsonAugmentedGraph]
      _ = (0 : WithTop ℝ) := by simp
  have hcardV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hcard_eq : Fintype.card (Option V) - 1 = Fintype.card V := by
    simp [Fintype.card_option]
  rw [hcard_eq]
  have h_noninc : ∀ m, 1 ≤ m → G'.relaxDist none m (some v) ≤ (0 : WithTop ℝ) :=
    Nat.le_induction h1 (fun n hn hle_n =>
      calc
        G'.relaxDist none (n + 1) (some v) ≤ G'.relaxDist none n (some v) :=
          G'.relaxDist_succ_le none n (some v)
        _ ≤ (0 : WithTop ℝ) := hle_n
    )
  have h_final : G'.relaxDist none (Fintype.card V) (some v) ≤ (0 : WithTop ℝ) :=
    h_noninc (Fintype.card V) hcardV
  intro htop; rw [htop] at h_final; simpa using h_final

/-- The **Johnson potential** `h(v) = δ(none, some v)` in the augmented graph,
computed via Bellman-Ford relaxation up to `|V'|-1` rounds.  The potential is
always finite (see `johnsonPotential_finite`), so the `⊤` branch is unreachable
and defaults to `0`. -/
noncomputable def johnsonPotential (_hNC : G.NoNegCycle) (v : V) : ℝ :=
  let G' := G.johnsonAugmentedGraph
  match G'.relaxDist none (Fintype.card (Option V) - 1) (some v) with
  | ⊤ => 0
  | some h => h

/-- The Johnson potential coerced to `WithTop ℝ` equals the `relaxDist` value
in the augmented graph.  This rewrites the unreachable-`⊤` match to a direct
coercion. -/
lemma johnsonPotential_eq (hNC : G.NoNegCycle) (v : V) :
    (G.johnsonPotential hNC v : WithTop ℝ) =
    G.johnsonAugmentedGraph.relaxDist none (Fintype.card (Option V) - 1) (some v) := by
  have h_fin := G.johnsonPotential_finite hNC v
  rcases Option.ne_none_iff_exists'.mp h_fin with ⟨h, hh⟩
  have h_pot_val : (G.johnsonPotential hNC v : WithTop ℝ) = (h : WithTop ℝ) := by
    unfold johnsonPotential
    dsimp
    -- After dsimp the let binder is gone; rewrite relaxDist with hh
    rw [hh]
  rw [h_pot_val, hh]
  -- Goal: (h : WithTop ℝ) = some h — definitional since the coercion is `some`
  rfl

/-- The Johnson potential is the shortest distance from `none` to `some v`
in the augmented graph: `IsShortestDist none (some v) h(v)`. -/
lemma johnsonPotential_isShortestDist (hNC : G.NoNegCycle) (v : V) :
    G.johnsonAugmentedGraph.IsShortestDist none (some v)
      ((G.johnsonPotential hNC v : ℝ) : WithTop ℝ) := by
  let G' := G.johnsonAugmentedGraph
  have hNC' : G'.NoNegCycle := G.noNegCycle_johnsonAugmentedGraph hNC
  have h_sd := G'.relaxDist_isShortestDist hNC' none (some v)
  rw [← G.johnsonPotential_eq hNC v] at h_sd
  exact h_sd

/-! ## Triangle inequality for the Johnson potential -/

theorem johnsonPotential_triangle (hNC : G.NoNegCycle) (u v : V) (h_edge : (u, v) ∈ G.edges) :
    G.johnsonPotential hNC v ≤ G.johnsonPotential hNC u + G.w u v := by
  let G' := G.johnsonAugmentedGraph
  have h_edge' : (some u, some v) ∈ G'.edges := by
    simpa [G'] using (G.mem_edges_johnsonAugmentedGraph_edge u v).mpr h_edge
  have h_δ : ∀ t : Option V, G'.IsShortestDist none t
      ((G'.relaxDist none (Fintype.card (Option V) - 1)) t) :=
    G'.relaxDist_isShortestDist (G.noNegCycle_johnsonAugmentedGraph hNC) none
  have h_ineq : G'.relaxDist none (Fintype.card (Option V) - 1) (some v) ≤
      G'.relaxDist none (Fintype.card (Option V) - 1) (some u) +
      (G'.w (some u) (some v) : WithTop ℝ) :=
    G'.isShortestDist_edge_ineq none (some u) (some v)
      (G'.relaxDist none (Fintype.card (Option V) - 1)) h_δ h_edge'
  rw [← G.johnsonPotential_eq hNC u, ← G.johnsonPotential_eq hNC v] at h_ineq
  -- h_ineq : (G.johnsonPotential hNC v : WithTop ℝ) ≤
  --   (G.johnsonPotential hNC u : WithTop ℝ) + (G'.w (some u) (some v) : WithTop ℝ)
  have h_w' : G'.w (some u) (some v) = G.w u v := by
    simp [G', johnsonAugmentedGraph]
  rw [h_w'] at h_ineq
  -- h_ineq : (G.johnsonPotential hNC v : WithTop ℝ) ≤
  --   (G.johnsonPotential hNC u : WithTop ℝ) + (G.w u v : WithTop ℝ)
  -- Goal : G.johnsonPotential hNC v ≤ G.johnsonPotential hNC u + G.w u v  (in ℝ)
  -- Use WithTop.coe_le_coe to strip coercions, and WithTop.coe_add to combine RHS
  apply (WithTop.coe_le_coe (α := ℝ)).mp
  rw [WithTop.coe_add (α := ℝ)]
  exact h_ineq

/-! ## Nonnegative reweighted weights -/

theorem johnsonReweightedNonneg (hNC : G.NoNegCycle) :
    (G.reweightedGraph (G.johnsonPotential hNC)).Nonneg := by
  intro u v h_edge
  have h_edge_orig : (u, v) ∈ G.edges := by
    simpa [reweightedGraph] using h_edge
  have h_triangle := G.johnsonPotential_triangle hNC u v h_edge_orig
  dsimp [reweightedGraph, reweightedWeight]
  linarith

/-! ## Johnson all-pairs distance -/

noncomputable def johnsonAllPairsDist (hNC : G.NoNegCycle) (u v : V) : WithTop ℝ :=
  let h := G.johnsonPotential hNC
  let G_hat := G.reweightedGraph h
  let st := G_hat.dijkstraLoop u (Fintype.card V)
  let d_hat := st.d v
  d_hat + (h v : WithTop ℝ) - (h u : WithTop ℝ)

/-! ## End-to-end correctness -/

theorem johnsonAllPairsDist_correct (hNC : G.NoNegCycle) (u v : V) :
    G.IsShortestDist u v (G.johnsonAllPairsDist hNC u v) := by
  let h := G.johnsonPotential hNC
  let G_hat := G.reweightedGraph h
  have hnn : G_hat.Nonneg := G.johnsonReweightedNonneg hNC
  have hNC_hat : G_hat.NoNegCycle := G_hat.noNegCycle_of_nonneg hnn
  let δ_hat (v : V) : WithTop ℝ := G_hat.relaxDist u (Fintype.card V - 1) v
  have hδ_hat (v : V) : G_hat.IsShortestDist u v (δ_hat v) :=
    G_hat.relaxDist_isShortestDist hNC_hat u v
  have h_dijkstra (v : V) : (G_hat.dijkstraLoop u (Fintype.card V)).d v = δ_hat v :=
    G_hat.dijkstraLoop_correct hnn u δ_hat hδ_hat (Fintype.card V)
      (le_refl (Fintype.card V)) v
  -- Expand johnsonAllPairsDist using the locally defined h and G_hat
  -- The local h and G_hat are definitionally equal to the ones in the definition
  have h_expand : G.johnsonAllPairsDist hNC u v =
      (G_hat.dijkstraLoop u (Fintype.card V)).d v + (h v : WithTop ℝ) - (h u : WithTop ℝ) := by
    unfold johnsonAllPairsDist
    rfl
  rw [h_expand]
  rw [h_dijkstra v]
  -- Goal: G.IsShortestDist u v (δ_hat v + (h v : WithTop ℝ) - (h u : WithTop ℝ))
  -- reweighted_isShortestDist: (G_hat).IsShortestDist u v (d + h_u - h_v) ↔ G.IsShortestDist u v d
  -- Let d := δ_hat v + h_v - h_u; then d + h_u - h_v = δ_hat v
  have h_fin_hu : (h u : WithTop ℝ) ≠ ⊤ := by simp
  have h_fin_hv : (h v : WithTop ℝ) ≠ ⊤ := by simp
  set d := δ_hat v + (h v : WithTop ℝ) - (h u : WithTop ℝ) with hd
  have h_eq : d + (h u : WithTop ℝ) - (h v : WithTop ℝ) = δ_hat v := by
    dsimp [d]
    rcases Option.ne_none_iff_exists'.mp h_fin_hu with ⟨hu_val, hhu⟩
    rcases Option.ne_none_iff_exists'.mp h_fin_hv with ⟨hv_val, hhv⟩
    rw [hhu, hhv]
    by_cases hδ_top : δ_hat v = ⊤
    · rw [hδ_top]; simp
    · rcases Option.ne_none_iff_exists'.mp hδ_top with ⟨δv_val, hδv⟩
      rw [hδv]; simp
  have h_sd_d : G_hat.IsShortestDist u v (d + (h u : WithTop ℝ) - (h v : WithTop ℝ)) := by
    rw [h_eq]; exact hδ_hat v
  exact (G.reweighted_isShortestDist h u v d).mp h_sd_d

end WeightedGraph
end Chapter24
end CLRS
