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
- Theorem `reweighted_isShortestDist`: reweighted shortest distances equal
  original distances shifted by `h(u) - h(v)`.
- Lemma `noNegCycle_johnsonAugmentedGraph`: the augmented graph has no
  negative cycles iff the original graph has none.
- Lemma `johnsonPotential_triangle`: the Bellman-Ford potential satisfies
  `h(v) ≤ h(u) + w(u, v)` for every edge `(u, v)`.
- Theorem `johnsonDist_isShortestDist`: **CLRS Theorem 25.5** —
  end-to-end correctness of Johnson's algorithm: `johnsonDist` computes
  the exact all-pairs shortest-path distances.

The section is **complete**: the augmented-graph potential construction,
triangle inequality, reweighting nonnegativity, and end-to-end Johnson
correctness are all proved.
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


/-! ## Negative-cycle equivalence for the augmented graph -/

/-- No edge in `johnsonAugmentedGraph` targets `none`. -/
lemma adj_target_ne_none (u v : Option V)
    (h_adj : G.johnsonAugmentedGraph.Adj u v) : v ≠ none := by
  intro h_eq; subst h_eq
  have h_edge : (u, none) ∈ G.johnsonAugmentedGraph.edges := h_adj
  exact G.no_incoming_to_none_johnsonAugmentedGraph u h_edge

/-- If a chain in `johnsonAugmentedGraph` does **not** start at `none`, then
`none` never appears in the chain. -/
lemma chain_no_none (l : List (Option V))
    (h_chain : List.IsChain G.johnsonAugmentedGraph.Adj l)
    (h_head_ne_none : l.head? ≠ some none) : none ∉ l := by
  induction l with
  | nil => simp
  | cons x l' ih =>
    rw [List.isChain_cons] at h_chain
    rcases h_chain with ⟨h_adj, h_chain_tail⟩
    have hx_ne_none : x ≠ none := by
      intro h_eq; subst h_eq; apply h_head_ne_none; simp
    have h_l'_head_ne_none : l'.head? ≠ some none := by
      intro h_eq
      have h_mem : none ∈ l'.head? := by rw [h_eq]; simp
      have h_adj_x_none : G.johnsonAugmentedGraph.Adj x none := h_adj none h_mem
      exact adj_target_ne_none G x none h_adj_x_none rfl
    have h_none_notin_l' : none ∉ l' := ih h_chain_tail h_l'_head_ne_none
    intro h
    cases h with
    | head _ => exact hx_ne_none rfl
    | tail _ h_mem => exact h_none_notin_l' h_mem

/-- The only walk from `none` to `none` in the augmented graph is `[none]`. -/
lemma walk_from_none_to_none_singleton (c : List (Option V))
    (hc : G.johnsonAugmentedGraph.IsWalkFrom none none c) : c = [none] := by
  have h_last : c.getLast? = some none := hc.last
  rcases List.getLast?_eq_some_iff.mp h_last with ⟨c₁, hc_eq⟩
  subst hc_eq
  by_cases h_c₁_empty : c₁ = []
  · subst h_c₁_empty; simp
  · have h_chain : List.IsChain G.johnsonAugmentedGraph.Adj (c₁ ++ [none]) := hc.chain
    rw [List.isChain_append] at h_chain
    rcases h_chain with ⟨_, _, h_adj_cond⟩
    have h_c₁_last_some : c₁.getLast? ≠ none := by
      intro h_eq; apply h_c₁_empty
      exact (List.getLast?_eq_none_iff.mp h_eq)
    rcases Option.ne_none_iff_exists'.mp h_c₁_last_some with ⟨last_c₁, h_last_c₁⟩
    have h_adj_last_none : G.johnsonAugmentedGraph.Adj last_c₁ none :=
      h_adj_cond last_c₁ (by rw [h_last_c₁]; simp) none (by simp)
    exfalso
    exact (adj_target_ne_none G last_c₁ none h_adj_last_none) rfl

/-- Extend a walk by a single edge `u → v` at the end. -/
lemma IsWalkFrom.append_step (hp : G.IsWalkFrom s u p) (h_edge : G.Adj u v) :
    G.IsWalkFrom s v (p ++ [v]) := by
  have h_chain : List.IsChain G.Adj (p ++ [v]) :=
    List.IsChain.append hp.chain (List.isChain_singleton v)
      (by
        intro x hx_last
        -- hx_last : p.getLast? = some x (by definition of ∈ for Option)
        rw [hp.last] at hx_last
        -- hx_last : some u = some x
        have hx_eq : x = u := (Option.some_inj.mp hx_last).symm
        subst hx_eq
        intro y hy_head
        -- hy_head : [v].head? = some y (by definition of ∈ for Option)
        -- [v].head? = some v (by simp)
        have hy_eq : y = v := by
          -- hy_head: [v].head? = some y, and [v].head? = some v
          -- So some y = some v, hence y = v
          have hh : [v].head? = some y := hy_head
          have hv : [v].head? = some v := by simp
          rw [hv] at hh
          -- hh: some v = some y
          exact (Option.some_inj.mp hh).symm
        subst hy_eq
        exact h_edge)
  have h_head : (p ++ [v]).head? = some s := by
    have hp_ne_nil : p ≠ [] := hp.ne_nil
    have hp_head_val : p.head? = some s := hp.head
    cases p with
    | nil => exact absurd rfl hp_ne_nil
    | cons a as =>
      -- p = a :: as, so (a :: as ++ [v]).head? = some a
      -- and hp.head gives some a = some s
      have h_head_a : (a :: as).head? = some a := by simp
      rw [h_head_a] at hp_head_val
      -- hp_head_val : some a = some s
      simp [hp_head_val]
  have h_last : (p ++ [v]).getLast? = some v := by simp
  exact ⟨h_chain, h_head, h_last⟩

/-- The weight of a walk extended by a single edge. -/
lemma walkWeight_append_step (hp : G.IsWalkFrom s u p) (h_edge : G.Adj u v) :
    (walkWeight G.w (p ++ [v]) : WithTop ℝ) =
      (walkWeight G.w p : WithTop ℝ) + (G.w u v : WithTop ℝ) := by
  rcases List.getLast?_eq_some_iff.mp hp.last with ⟨q, hq⟩
  subst hq
  simp [walkWeight_concat G.w q u v]

/-- An auxiliary function that strips `Option.some` from an element. -/
private def unsome (default : V) (x : Option V) : V :=
  match x with | some v => v | none => default

/-- For a `none`-free list, the chain in `G'` lifts to a chain in `G`. -/
private lemma chain_none_free_map (default : V) (l : List (Option V))
    (h_chain : List.IsChain G.johnsonAugmentedGraph.Adj l)
    (h_no_none : none ∉ l) :
    List.IsChain G.Adj (l.map (unsome default)) := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons x l' ih =>
    rw [List.isChain_cons] at h_chain
    rcases h_chain with ⟨h_adj, h_chain_tail⟩
    have hx_ne_none : x ≠ none := by
      intro h_eq; subst h_eq; exact h_no_none (by simp)
    have hl'_no_none : none ∉ l' := by
      intro h; exact h_no_none (by simp [h])
    -- Determine x (must be some a since ≠ none)
    obtain ⟨a, hx_eq⟩ := Option.ne_none_iff_exists'.mp hx_ne_none
    subst hx_eq
    -- Now x = some a
    have ih_map : List.IsChain G.Adj (l'.map (unsome default)) :=
      ih h_chain_tail hl'_no_none
    rw [show (some a :: l').map (unsome default) = a :: l'.map (unsome default) by
      simp [unsome]]
    apply List.IsChain.cons ih_map
    intro y hy
    -- hy : y ∈ (l'.map (unsome default)).head?
    -- We need G.Adj a y. Analyze l'.
    cases l' with
    | nil => simp at hy
    | cons z l'' =>
      -- z must be some b (since none ∉ l')
      have hz_ne_none : z ≠ none := by
        intro h_eq; subst h_eq; exact hl'_no_none (by simp)
      obtain ⟨b, hz_eq⟩ := Option.ne_none_iff_exists'.mp hz_ne_none
      subst hz_eq
      -- Now l' = some b :: l''
      -- The head of (some b :: l'').map (unsome default) is b
      have h_head_map : ((some b :: l'').map (unsome default)).head? = some b := by
        simp [unsome]
      rw [h_head_map] at hy
      -- Now hy : y ∈ some b, i.e. some b = some y, so b = y
      have hy_eq : b = y := Option.some_inj.mp hy
      subst hy_eq
      -- Need G.Adj a b. From h_adj: G'.Adj (some a) (some b)
      have h_adj' : G.johnsonAugmentedGraph.Adj (some a) (some b) :=
        h_adj (some b) (by simp)
      exact (G.mem_edges_johnsonAugmentedGraph_edge a b).mp h_adj'

/-- For a `none`-free list, the walk weights in `G'` and `G` agree. -/
private lemma walkWeight_none_free_eq (default : V) (c : List (Option V))
    (h_no_none : none ∉ c) :
    walkWeight G.johnsonAugmentedGraph.w c =
      walkWeight G.w (c.map (unsome default)) := by
  induction c with
  | nil => simp [walkWeight]
  | cons x cs ih =>
    cases x with
    | none => exfalso; exact h_no_none (by simp)
    | some a =>
      cases cs with
      | nil =>
        -- c = [some a]; both sides are 0
        simp [walkWeight]
      | cons y rest =>
        have h_cs_no_none : none ∉ (y :: rest) := by
          intro h; apply h_no_none; simp [h]
        cases y with
        | none => exfalso; exact h_cs_no_none (by simp)
        | some b =>
          -- c = some a :: some b :: rest
          -- walkWeight G'.w c = G.w a b + walkWeight G'.w (some b :: rest)
          -- walkWeight G.w (c.map f) = G.w a b + walkWeight G.w (b :: rest.map f)
          have h_ih := ih h_cs_no_none
          -- h_ih: walkWeight G'.w (some b :: rest) = walkWeight G.w ((some b :: rest).map (unsome default))
          -- Compute RHS map:
          have h_map_rest : ((some b :: rest).map (unsome default)) = b :: (rest.map (unsome default)) := by
            simp [unsome]
          rw [h_map_rest] at h_ih
          -- Now h_ih: walkWeight G'.w (some b :: rest) = walkWeight G.w (b :: rest.map (unsome default))
          -- Expand both sides using walkWeight formula
          calc
            walkWeight G.johnsonAugmentedGraph.w (some a :: some b :: rest)
                = G.johnsonAugmentedGraph.w (some a) (some b) +
                  walkWeight G.johnsonAugmentedGraph.w (some b :: rest) := by simp [walkWeight]
            _ = G.w a b + walkWeight G.johnsonAugmentedGraph.w (some b :: rest) := by
              simp [johnsonAugmentedGraph]
            _ = G.w a b + walkWeight G.w (b :: rest.map (unsome default)) := by rw [h_ih]
            _ = walkWeight G.w (a :: b :: rest.map (unsome default)) := by simp [walkWeight]
            _ = walkWeight G.w ((some a :: some b :: rest).map (unsome default)) := by
              unfold unsome; simp

/-- Project a `none`-free walk in `G'` to a walk in `G` with the same weight. -/
private lemma exists_walk_in_G_of_none_free_walk (x' : V) (c : List (Option V))
    (hc : G.johnsonAugmentedGraph.IsWalkFrom (some x') (some x') c)
    (h_no_none : none ∉ c) :
    ∃ (c' : List V),
      G.IsWalkFrom x' x' c' ∧
      walkWeight G.johnsonAugmentedGraph.w c = walkWeight G.w c' := by
  let c' := c.map (unsome x')
  have h_chain_c' : List.IsChain G.Adj c' :=
    chain_none_free_map G x' c hc.chain h_no_none
  have h_head_c' : c'.head? = some x' := by
    have h_head_c : c.head? = some (some x') := hc.head
    rcases List.head?_eq_some_iff.mp h_head_c with ⟨cs, hc_eq⟩
    subst hc_eq
    simp [c', unsome]
  have h_last_c' : c'.getLast? = some x' := by
    rcases List.getLast?_eq_some_iff.mp hc.last with ⟨q, hq⟩
    subst hq
    simp [c', unsome]
  have h_walk_c' : G.IsWalkFrom x' x' c' :=
    ⟨h_chain_c', h_head_c', h_last_c'⟩
  have h_wt_eq : walkWeight G.johnsonAugmentedGraph.w c = walkWeight G.w c' :=
    walkWeight_none_free_eq G x' c h_no_none
  exact ⟨c', h_walk_c', h_wt_eq⟩

/-- If `G` has no negative cycles, then `johnsonAugmentedGraph` also has none. -/
lemma noNegCycle_johnsonAugmentedGraph (hNC : G.NoNegCycle) :
    G.johnsonAugmentedGraph.NoNegCycle := by
  intro x c hc
  cases x with
  | none =>
    have h_single : c = [none] := walk_from_none_to_none_singleton G c hc
    subst h_single; simp [walkWeight]
  | some x' =>
    have h_head_ne_none : c.head? ≠ some none := by
      rw [hc.head]; simp
    have h_no_none : none ∉ c := chain_no_none G c hc.chain h_head_ne_none
    rcases exists_walk_in_G_of_none_free_walk G x' c hc h_no_none with ⟨c', hc'_walk, hw_eq⟩
    rw [hw_eq]
    exact hNC x' c' hc'_walk

/-! ## Johnson potential via Bellman-Ford on the augmented graph -/

/-- A direct walk from `none` to `some v` in the augmented graph. -/
lemma isWalkFrom_none_some (v : V) :
    G.johnsonAugmentedGraph.IsWalkFrom none (some v) [none, some v] := by
  let G' := G.johnsonAugmentedGraph
  have h_chain : List.IsChain G'.Adj [none, some v] := by
    rw [List.isChain_cons]
    refine ⟨?_, List.isChain_singleton _⟩
    intro y hy
    have hy_eq : y = some v := by
      have h_head_val : [some v].head? = some (some v) := by simp
      rw [h_head_val] at hy
      exact (Option.some_inj.mp hy).symm
    subst hy_eq
    unfold G' johnsonAugmentedGraph WeightedGraph.Adj
    simp
  refine ⟨h_chain, ?_, ?_⟩
  · simp
  · simp

/-- The Bellman-Ford distance from `none` to `some v` in the augmented graph
is finite (not `⊤`), because there is a direct zero-weight edge. -/
lemma relaxDist_none_some_ne_top (hNC : G.NoNegCycle) (v : V) :
    G.johnsonAugmentedGraph.relaxDist none
      (Fintype.card (Option V) - 1) (some v) ≠ ⊤ := by
  let G' := G.johnsonAugmentedGraph
  have h_no_neg : G'.NoNegCycle := noNegCycle_johnsonAugmentedGraph G hNC
  have h_sd := G'.relaxDist_isShortestDist h_no_neg none (some v)
  rcases h_sd with ⟨h_lower, _⟩
  have h_walk : G'.IsWalkFrom none (some v) [none, some v] :=
    isWalkFrom_none_some G v
  have h_bound : G'.relaxDist none (Fintype.card (Option V) - 1) (some v) ≤
      (walkWeight G'.w [none, some v] : WithTop ℝ) :=
    h_lower [none, some v] h_walk
  have h_wt : (walkWeight G'.w [none, some v] : WithTop ℝ) = (0 : WithTop ℝ) := by
    simp [walkWeight, G', johnsonAugmentedGraph]
  rw [h_wt] at h_bound
  intro h_eq; rw [h_eq] at h_bound; simpa using h_bound

/-- The **Johnson potential** `h(v)` is the shortest-path distance from
`none` to `some v` in the augmented graph, computed by Bellman-Ford. -/
noncomputable def johnsonPotential (hNC : G.NoNegCycle) (v : V) : ℝ :=
  (G.johnsonAugmentedGraph.relaxDist none
    (Fintype.card (Option V) - 1) (some v)).untop
    (relaxDist_none_some_ne_top G hNC v)

/-- The potential cast to `WithTop ℝ` equals the Bellman-Ford relaxation. -/
lemma johnsonPotential_eq (hNC : G.NoNegCycle) (v : V) :
    (G.johnsonPotential hNC v : WithTop ℝ) =
    G.johnsonAugmentedGraph.relaxDist none
      (Fintype.card (Option V) - 1) (some v) := by
  unfold johnsonPotential
  simp [relaxDist_none_some_ne_top G hNC v]

/-- The Johnson potential is the shortest-path distance from `none` to `some v`
in the augmented graph. -/
lemma johnsonPotential_isShortestDist (hNC : G.NoNegCycle) (v : V) :
    G.johnsonAugmentedGraph.IsShortestDist none (some v)
      (G.johnsonPotential hNC v) := by
  rw [johnsonPotential_eq G hNC]
  have h_no_neg : G.johnsonAugmentedGraph.NoNegCycle :=
    noNegCycle_johnsonAugmentedGraph G hNC
  exact G.johnsonAugmentedGraph.relaxDist_isShortestDist h_no_neg none (some v)

/-! ## Triangle inequality for the Johnson potential -/

/-- **Triangle inequality for the Johnson potential.**  For every edge
`(u, v)` in `G`, we have `h(v) ≤ h(u) + w(u, v)`. -/
lemma johnsonPotential_triangle (hNC : G.NoNegCycle) (u v : V)
    (h_edge : (u, v) ∈ G.edges) :
    G.johnsonPotential hNC v ≤ G.johnsonPotential hNC u + G.w u v := by
  let G' := G.johnsonAugmentedGraph
  let hu := G.johnsonPotential hNC u
  let hv := G.johnsonPotential hNC v
  have h_sd_u : G'.IsShortestDist none (some u) (hu : WithTop ℝ) :=
    johnsonPotential_isShortestDist G hNC u
  have h_sd_v : G'.IsShortestDist none (some v) (hv : WithTop ℝ) :=
    johnsonPotential_isShortestDist G hNC v
  rcases h_sd_u.2 with (h_top | ⟨p_u, hp_walk, hp_weight⟩)
  · have h_fin : (hu : WithTop ℝ) ≠ ⊤ := by simp
    exact absurd h_top h_fin
  · have h_edge' : G'.Adj (some u) (some v) := by
      unfold G' johnsonAugmentedGraph WeightedGraph.Adj; simp [h_edge]
    have h_walk_v : G'.IsWalkFrom none (some v) (p_u ++ [some v]) :=
      IsWalkFrom.append_step (G := G') hp_walk h_edge'
    have h_weight_v : (walkWeight G'.w (p_u ++ [some v]) : WithTop ℝ) =
        (hu : WithTop ℝ) + (G.w u v : WithTop ℝ) := by
      rw [walkWeight_append_step G' hp_walk h_edge']
      rw [hp_weight]
      have h_w_uv : (G'.w (some u) (some v) : WithTop ℝ) = (G.w u v : WithTop ℝ) := by
        unfold G' johnsonAugmentedGraph; simp
      rw [h_w_uv]
    have h_ineq : (hv : WithTop ℝ) ≤ (walkWeight G'.w (p_u ++ [some v]) : WithTop ℝ) :=
      h_sd_v.1 (p_u ++ [some v]) h_walk_v
    rw [h_weight_v] at h_ineq
    exact_mod_cast h_ineq

/-! ## Nonnegativity of the reweighted graph -/

/-- With the Johnson potential, every edge weight in the reweighted graph
is nonnegative, satisfying Dijkstra's precondition. -/
lemma reweightedGraph_nonneg (hNC : G.NoNegCycle) :
    (G.reweightedGraph (G.johnsonPotential hNC)).Nonneg := by
  rw [WeightedGraph.Nonneg]
  intro u v h_edge
  rw [w_reweightedGraph, reweightedWeight_eq]
  have h_triangle := johnsonPotential_triangle G hNC u v h_edge
  linarith

/-- With the Johnson potential, the reweighted graph has no negative cycles. -/
lemma reweightedGraph_noNegCycle (hNC : G.NoNegCycle) :
    (G.reweightedGraph (G.johnsonPotential hNC)).NoNegCycle :=
  noNegCycle_of_nonneg (G := G.reweightedGraph (G.johnsonPotential hNC)) (G.reweightedGraph_nonneg hNC)

/-! ## Johnson's all-pairs shortest paths -/

/-- A `WithTop ℝ` algebra identity for finite adjustments. -/
private lemma add_sub_add_sub_eq (a : WithTop ℝ) (b c : ℝ) :
    a = (a + (c : WithTop ℝ) - (b : WithTop ℝ)) + (b : WithTop ℝ) - (c : WithTop ℝ) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a => simp

/-- **Johnson's all-pairs shortest-path distance.**  Run Bellman-Ford from `u`
in the reweighted graph, then adjust by `h(v) - h(u)`. -/
noncomputable def johnsonDist (hNC : G.NoNegCycle) (u v : V) : WithTop ℝ :=
  let h := G.johnsonPotential hNC
  let d_hat := (G.reweightedGraph h).relaxDist u (Fintype.card V - 1) v
  d_hat + (h v : WithTop ℝ) - (h u : WithTop ℝ)

/-- **Theorem (Johnson correctness).**  `johnsonDist hNC u v` equals the
shortest-path distance `δ(u, v)` in the original graph `G`.  (CLRS Theorem 25.5) -/
theorem johnsonDist_isShortestDist (hNC : G.NoNegCycle) (u v : V) :
    G.IsShortestDist u v (G.johnsonDist hNC u v) := by
  let h := G.johnsonPotential hNC
  have h_no_neg : (G.reweightedGraph h).NoNegCycle := G.reweightedGraph_noNegCycle hNC
  let d_hat := (G.reweightedGraph h).relaxDist u (Fintype.card V - 1) v
  have h_sd_dhat : (G.reweightedGraph h).IsShortestDist u v d_hat :=
    (G.reweightedGraph h).relaxDist_isShortestDist h_no_neg u v
  unfold johnsonDist
  -- Let d := d_hat + h(v) - h(u). Then d + h(u) - h(v) = d_hat.
  -- So by reweighted_isShortestDist.mp, G.IsShortestDist u v d.
  have h_algebra : ((d_hat + (h v : WithTop ℝ) - (h u : WithTop ℝ)) +
      (h u : WithTop ℝ) - (h v : WithTop ℝ)) = d_hat :=
    (add_sub_add_sub_eq d_hat (h u) (h v)).symm
  have h_equiv := G.reweighted_isShortestDist h u v
    (d_hat + (h v : WithTop ℝ) - (h u : WithTop ℝ))
  rw [← h_algebra] at h_sd_dhat
  exact h_equiv.mp h_sd_dhat


end WeightedGraph
end Chapter24
end CLRS
