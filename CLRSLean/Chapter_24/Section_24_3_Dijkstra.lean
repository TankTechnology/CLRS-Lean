import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

/-!
# 24.3. Dijkstra's algorithm

Building on the weighted directed-graph model and the shortest-path distance
{lit}`δ` of Section 24.1, this section formalizes the correctness core of
Dijkstra's algorithm under nonnegative edge weights: the **greedy invariant**
(CLRS Theorem 24.6), stating that the unsettled vertex with minimum tentative
distance already has the correct shortest-path distance.  It also records the
{lit}`O(E log V)` binary-heap work decomposition.

Main results:

- {lit}`CLRS.Chapter24.WeightedGraph.Nonneg`: nonnegative edge weights.
- {lit}`CLRS.Chapter24.WeightedGraph.noNegCycle_of_nonneg`: nonnegative weights
  have no negative cycle, so Section 24.1's {lit}`δ` machinery applies.
- {lit}`CLRS.Chapter24.WeightedGraph.walkWeight_nonneg`: walks have nonnegative
  weight.
- {lit}`CLRS.Chapter24.WeightedGraph.exists_crossing`: a walk from a settled to
  an unsettled vertex crosses the settled frontier.
- {lit}`CLRS.Chapter24.WeightedGraph.dijkstra_extractMin_correct`: **CLRS
  Theorem 24.6 (greedy invariant)** — under the Dijkstra relaxation invariants,
  the extracted minimum-tentative-distance vertex has {lit}`d u = δ u`.
- {lit}`CLRS.Chapter24.WeightedGraph.dijkstraWork_le_edge_log`: the
  {lit}`(|V| + |E|)·log|V|` binary-heap work is {lit}`O(E log V)` for connected
  graphs.

The greedy invariant is the mathematical heart of Dijkstra: a standard induction
using it settles every reachable vertex with its exact distance.  The executable
priority-queue loop and its state threading are a separate refinement layer,
consistent with the Chapter 22/23 graph track.

Notation conventions:

- {lit}`S` : the set of settled vertices
- {lit}`d` : tentative distances
- {lit}`δ` : true shortest-path distances (from Section 24.1)
- {lit}`u` : the vertex extracted with minimum tentative distance
-/

namespace CLRS
namespace Chapter24

open Finset

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Nonnegative weights -/

/-- All edge weights are nonnegative (Dijkstra's hypothesis). -/
def Nonneg : Prop := ∀ u v, (u, v) ∈ G.edges → 0 ≤ G.w u v

/-- With nonnegative weights every walk has nonnegative weight. -/
theorem walkWeight_nonneg (hnn : G.Nonneg) :
    ∀ {p : List V}, List.IsChain G.Adj p → 0 ≤ walkWeight G.w p := by
  intro p
  induction p with
  | nil => intro _; simp [walkWeight]
  | cons a t ih =>
    intro hp
    cases t with
    | nil => simp [walkWeight]
    | cons b t' =>
      rw [walkWeight_cons_cons]
      have hedge : (a, b) ∈ G.edges := hp.rel_head
      have h1 : 0 ≤ G.w a b := hnn a b hedge
      have h2 : 0 ≤ walkWeight G.w (b :: t') := ih hp.tail
      linarith

/-- Nonnegative weights have no negative cycle, so the Section 24.1 shortest-path
distance {lit}`δ` is well defined. -/
theorem noNegCycle_of_nonneg (hnn : G.Nonneg) : G.NoNegCycle := by
  intro x c hc
  exact G.walkWeight_nonneg hnn hc.chain

/-! ## Crossing the settled frontier -/

/-- A walk from a settled vertex {lit}`a ∈ S` to an unsettled vertex {lit}`u ∉ S` contains
a frontier edge {lit}`(x, y)` with {lit}`x ∈ S`, {lit}`y ∉ S`, and a settled prefix reaching
{lit}`x`. -/
theorem exists_crossing (S : Finset V) :
    ∀ (p : List V) (a u : V), G.IsWalkFrom a u p → a ∈ S → u ∉ S →
      ∃ (P R : List V) (x y : V), p = P ++ x :: y :: R ∧ x ∈ S ∧ y ∉ S ∧
        G.IsWalkFrom a x (P ++ [x]) := by
  intro p
  induction p with
  | nil => intro a u hp _ _; exact absurd rfl hp.ne_nil
  | cons a' rest ih =>
    intro a u hp haS huS
    have ha' : a' = a := by simpa using hp.head
    subst a'
    cases rest with
    | nil =>
      have hau : a = u := by simpa using hp.last
      exact absurd (hau ▸ haS) huS
    | cons c rest' =>
      have hac : G.Adj a c := hp.chain.rel_head
      by_cases hcS : c ∈ S
      · have hcwalk : G.IsWalkFrom c u (c :: rest') := by
          refine ⟨hp.chain.tail, by simp, ?_⟩
          rw [← List.getLast?_cons_cons (a := a)]; exact hp.last
        obtain ⟨P', R', x, y, heq, hx, hy, hwx⟩ := ih c u hcwalk hcS huS
        refine ⟨a :: P', R', x, y, by rw [heq]; simp, hx, hy, ?_⟩
        refine ⟨?_, by simp, List.getLast?_concat⟩
        refine hwx.chain.cons ?_
        intro z hz
        have hzc : z = c := by
          rw [Option.mem_def, hwx.head] at hz
          exact (Option.some.inj hz).symm
        rw [hzc]; exact hac
      · exact ⟨[], rest', a, c, by simp, haS, hcS,
          ⟨List.isChain_singleton a, by simp, by simp⟩⟩

/-! ## The greedy invariant (CLRS Theorem 24.6) -/

/-- **CLRS Theorem 24.6 (Dijkstra greedy invariant).**  Suppose the source {lit}`s` is
settled ({lit}`s ∈ S`), tentative distances never underestimate {lit}`δ` on the frontier
({lit}`hvalid`), and every frontier edge out of a settled vertex has been relaxed
({lit}`htent`).  Then the unsettled vertex {lit}`u` of minimum tentative distance already
has the correct shortest-path distance {lit}`d u = δ u`.

This is the invariant that makes Dijkstra correct under nonnegative weights: it
justifies moving {lit}`u` into the settled set with a final, correct distance. -/
theorem dijkstra_extractMin_correct
    (hnn : G.Nonneg) (s : V) (δ : V → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v))
    (S : Finset V) (hsS : s ∈ S) (d : V → WithTop ℝ)
    (htent : ∀ y, y ∉ S → ∀ x, x ∈ S → (x, y) ∈ G.edges →
      d y ≤ δ x + (G.w x y : WithTop ℝ))
    (hvalid : ∀ y, y ∉ S → δ y ≤ d y)
    (u : V) (hu : u ∉ S) (hmin : ∀ y, y ∉ S → d u ≤ d y) :
    d u = δ u := by
  refine le_antisymm ?_ (hvalid u hu)
  rcases (hδ u).2 with hutop | ⟨p, hp, hpw⟩
  · rw [hutop]; exact le_top
  · obtain ⟨P, R, x, y, heq, hxS, hyS, hwx⟩ := G.exists_crossing S p s u hp hsS hu
    obtain ⟨hPx_chain, hxy, hyR_chain⟩ :=
      List.isChain_append_cons_cons.1 (show List.IsChain G.Adj (P ++ x :: y :: R) by
        rw [← heq]; exact hp.chain)
    have hxy_edge : (x, y) ∈ G.edges := hxy
    -- weight of the prefix through the frontier edge is at most the whole walk
    have hp_eq2 : p = (P ++ [x]) ++ (y :: R) := by rw [heq]; simp
    have hsplit : walkWeight G.w p
        = walkWeight G.w ((P ++ [x]) ++ [y]) + walkWeight G.w (y :: R) := by
      rw [hp_eq2, walkWeight_split G.w (P ++ [x]) y R]
    have hconcat : walkWeight G.w ((P ++ [x]) ++ [y])
        = walkWeight G.w (P ++ [x]) + G.w x y := by
      rw [List.append_assoc]; exact walkWeight_concat G.w P x y
    have htail_nonneg : 0 ≤ walkWeight G.w (y :: R) := G.walkWeight_nonneg hnn hyR_chain
    have hprefix_le : walkWeight G.w (P ++ [x]) + G.w x y ≤ walkWeight G.w p := by
      rw [hsplit, hconcat]; linarith
    have hδx : δ x ≤ (walkWeight G.w (P ++ [x]) : WithTop ℝ) := (hδ x).1 (P ++ [x]) hwx
    have hdy : d y ≤ δ x + (G.w x y : WithTop ℝ) := htent y hyS x hxS hxy_edge
    calc d u ≤ d y := hmin y hyS
      _ ≤ δ x + (G.w x y : WithTop ℝ) := hdy
      _ ≤ (walkWeight G.w (P ++ [x]) : WithTop ℝ) + (G.w x y : WithTop ℝ) := by gcongr
      _ ≤ (walkWeight G.w p : WithTop ℝ) := by
          rw [← WithTop.coe_add]; exact_mod_cast hprefix_le
      _ = δ u := hpw

/-! ## Work bound: {lit}`O(E log V)` -/

/-- Binary-heap Dijkstra work: {lit}`|V|` extract-mins and {lit}`|E|` decrease-keys, each
{lit}`O(log |V|)`, i.e. {lit}`(|V| + |E|)·(log₂|V| + 1)`. -/
def dijkstraWork (vertices edges : Nat) : Nat :=
  (vertices + edges) * (Nat.log2 vertices + 1)

/-- **{lit}`O(E log V)` work.**  For a connected graph ({lit}`|V| ≤ 2|E|`) the binary-heap
Dijkstra work is {lit}`O(E log V)`. -/
theorem dijkstraWork_le_edge_log {vertices edges : Nat} (hconn : vertices ≤ 2 * edges) :
    dijkstraWork vertices edges ≤ 3 * edges * (Nat.log2 vertices + 1) := by
  unfold dijkstraWork
  apply Nat.mul_le_mul_right
  omega

/-! ## Executable priority-queue loop -/

/-- The state of the Dijkstra algorithm: the set of settled vertices and the current
tentative distance map. -/
@[ext]
structure DijkstraState (V : Type*) where
  /-- Settled vertices (those whose exact distance is known). -/
  S : Finset V
  /-- Tentative distances. -/
  d : V → WithTop ℝ

/-- The initial state: all unsettled, source at distance `0`, all others at `⊤`. -/
def dijkstraInit (s : V) : DijkstraState V :=
  { S := ∅, d := fun v => if v = s then (0 : WithTop ℝ) else ⊤ }

/-- One iteration: extract an unsettled vertex of minimum tentative distance,
settle it, and relax its outgoing edges.  When no unsettled vertex remains, the
state is unchanged.  Noncomputable because `V` is not assumed to be linearly
ordered. -/
noncomputable def dijkstraStep (G : WeightedGraph V) (st : DijkstraState V) : DijkstraState V :=
  let U := Finset.univ \ st.S
  if hU : U.Nonempty then
    have h_min : ∃ u ∈ U, ∀ v ∈ U, st.d u ≤ st.d v := U.exists_min_image st.d hU
    let u := Classical.choose h_min
    { S := insert u st.S
      d := fun v => if (u, v) ∈ G.edges then min (st.d v) (st.d u + (G.w u v : WithTop ℝ)) else st.d v }
  else st

/-- The Dijkstra loop invariant.  For a state `st` satisfying this invariant,
settled vertices have their exact shortest-path distance, and the unsettled
vertices satisfy the two properties required by CLRS Theorem 24.6. -/
structure DijkstraInvariant (hnn : G.Nonneg) (s : V) (δ : V → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v)) (st : DijkstraState V) : Prop where
  /-- The source is settled. -/
  hsS : s ∈ st.S
  /-- Every settled vertex has its exact distance. -/
  hsettled : ∀ x ∈ st.S, st.d x = δ x
  /-- For every frontier edge, the tentative distance at the unsettled endpoint
  is at most the optimal distance to the settled endpoint plus the edge weight. -/
  htent : ∀ y ∉ st.S, ∀ x ∈ st.S, (x, y) ∈ G.edges →
    st.d y ≤ δ x + (G.w x y : WithTop ℝ)
  /-- Tentative distances never underestimate the true shortest-path distance. -/
  hvalid : ∀ y ∉ st.S, δ y ≤ st.d y

/-- The shortest-path distance from a vertex to itself is zero. -/
theorem isShortestDist_self_zero (hnn : G.Nonneg) (s : V) (δ : V → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v)) : δ s = (0 : WithTop ℝ) := by
  have h_walk : G.IsWalkFrom s s [s] :=
    ⟨List.isChain_singleton s, by simp, by simp⟩
  have h_le : δ s ≤ (0 : WithTop ℝ) := (hδ s).1 [s] h_walk
  rcases (hδ s).2 with htop | ⟨p, hp, hpw⟩
  · rw [htop] at h_le; simp at h_le
  · have h_nonneg : (0 : ℝ) ≤ walkWeight G.w p := G.walkWeight_nonneg hnn hp.chain
    have hδ_nonneg : (0 : WithTop ℝ) ≤ δ s := by
      rw [← hpw]; exact_mod_cast h_nonneg
    exact le_antisymm h_le hδ_nonneg

/-- If `(u, v)` is an edge, then the shortest-path distance to `v` is bounded above
by the shortest-path distance to `u` plus the edge weight (triangle inequality). -/
theorem delta_le_delta_add_edge (hnn : G.Nonneg) (s : V) (δ : V → WithTop ℝ)
    (hδ : ∀ t, G.IsShortestDist s t (δ t)) (u v : V) (h_edge : (u, v) ∈ G.edges) :
    δ v ≤ δ u + (G.w u v : WithTop ℝ) := by
  rcases (hδ u).2 with hutop | ⟨q, hq, hqw⟩
  · -- δ u = ⊤, then RHS = ⊤, and the inequality holds trivially
    rw [hutop]; simp
  · -- δ u is finite, realized by walk q from s to u
    rcases (hδ v).2 with htop | ⟨p, hp, hpw⟩
    · -- δ v = ⊤: impossible because q ++ [v] is a walk from s to v (via u)
      exfalso
      have h_walk : G.IsWalkFrom s v (q ++ [v]) := by
        refine ⟨?_, ?_, ?_⟩
        · refine hq.chain.append (List.isChain_singleton v) ?_
          intro a ha b hb
          have ha_u : a = u := by
            rw [Option.mem_def, hq.last] at ha
            exact (Option.some.inj ha).symm
          subst ha_u
          have hb_v : b = v := by
            simpa using hb.symm
          subst hb_v
          exact h_edge
        · rw [List.head?_append_of_ne_nil _ hq.ne_nil]
          exact hq.head
        · simp
      have h_contra : δ v ≤ (walkWeight G.w (q ++ [v]) : WithTop ℝ) := (hδ v).1 _ h_walk
      rw [htop] at h_contra
      simp at h_contra
    · -- both δ u and δ v are finite
      have h_getlast_u : q.getLast hq.ne_nil = u := by
        have htemp := List.getLast?_eq_getLast_of_ne_nil hq.ne_nil
        have h_eq_some : some u = some (q.getLast hq.ne_nil) := by
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
            simpa using hb.symm
          subst hb_v
          exact h_edge
        · rw [List.head?_append_of_ne_nil _ hq.ne_nil]
          exact hq.head
        · simp
      have h_weight : (walkWeight G.w (q ++ [v]) : WithTop ℝ) = δ u + (G.w u v : WithTop ℝ) := by
        calc
          (walkWeight G.w (q ++ [v]) : WithTop ℝ) = ((walkWeight G.w q + G.w (q.getLast hq.ne_nil) v : ℝ) : WithTop ℝ) := by
            exact_mod_cast walkWeight_append_singleton G.w q hq.ne_nil v
          _ = (walkWeight G.w q : WithTop ℝ) + (G.w (q.getLast hq.ne_nil) v : WithTop ℝ) := by simp
          _ = (walkWeight G.w q : WithTop ℝ) + (G.w u v : WithTop ℝ) := by simp [h_getlast_u]
          _ = δ u + (G.w u v : WithTop ℝ) := by rw [hqw]
      have h_walk_weight : δ v ≤ (walkWeight G.w (q ++ [v]) : WithTop ℝ) :=
        (hδ v).1 (q ++ [v]) h_walk
      rw [h_weight] at h_walk_weight
      exact h_walk_weight

/-- If the Dijkstra invariant holds, then any unsettled vertex `u` that minimizes
`st.d` among unsettled vertices satisfies `st.d u = δ u`. -/
theorem extractMin_correct_of_invariant (hnn : G.Nonneg) (s : V) (δ : V → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v))
    (st : DijkstraState V) (h_inv : DijkstraInvariant G hnn s δ hδ st)
    (u : V) (hu : u ∉ st.S) (hmin : ∀ y, y ∉ st.S → st.d u ≤ st.d y) :
    st.d u = δ u :=
  G.dijkstra_extractMin_correct hnn s δ hδ st.S h_inv.hsS st.d h_inv.htent h_inv.hvalid u hu hmin


/-- If the Dijkstra invariant holds for `st`, then it also holds after one more
`dijkstraStep`. -/
theorem dijkstraStep_invariant (hnn : G.Nonneg) (s : V) (δ : V → WithTop ℝ)
    (hδ : ∀ v, G.IsShortestDist s v (δ v))
    (st : DijkstraState V) (h_inv : DijkstraInvariant G hnn s δ hδ st) :
    DijkstraInvariant G hnn s δ hδ (dijkstraStep G st) := by
  unfold dijkstraStep
  let U := Finset.univ \ st.S
  by_cases hU : U.Nonempty
  · have h_min : ∃ u ∈ U, ∀ v ∈ U, st.d u ≤ st.d v := U.exists_min_image st.d hU
    let u := Classical.choose h_min
    have hu_mem : u ∈ U := (Classical.choose_spec h_min).1
    have hu_min : ∀ v ∈ U, st.d u ≤ st.d v := (Classical.choose_spec h_min).2
    have hu_notin_S : u ∉ st.S := (Finset.mem_sdiff.1 hu_mem).2
    have hu_min_all : ∀ y, y ∉ st.S → st.d u ≤ st.d y := by
      intro y hy
      apply hu_min y
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩
    have h_du_eq_δu : st.d u = δ u :=
      G.extractMin_correct_of_invariant hnn s δ hδ st h_inv u hu_notin_S hu_min_all
    rw [dif_pos hU]
    let S' := insert u st.S
    let d' := fun v => if (u, v) ∈ G.edges then min (st.d v) (st.d u + (G.w u v : WithTop ℝ)) else st.d v
    have h_s_S' : s ∈ S' := Finset.mem_insert_of_mem h_inv.hsS
    have h_settled' : ∀ x ∈ S', d' x = δ x := by
      intro x hx
      rcases Finset.mem_insert.1 hx with (rfl | hx_S)
      · -- x = u
        dsimp [d']
        by_cases h_edge_uu : (u, u) ∈ G.edges
        · have h_nonneg_w : 0 ≤ G.w u u := hnn u u h_edge_uu
          have h_add : st.d u ≤ st.d u + (G.w u u : WithTop ℝ) := by
            have h_nonneg_w' : (0 : WithTop ℝ) ≤ (G.w u u : WithTop ℝ) := by exact_mod_cast h_nonneg_w
            exact le_add_of_nonneg_right h_nonneg_w'
          simp [h_edge_uu]
          have h_min_eq : min (st.d u) (st.d u + (G.w u u : WithTop ℝ)) = st.d u :=
            min_eq_left h_add
          rw [h_min_eq, h_du_eq_δu]
        · simp [h_edge_uu, h_du_eq_δu]
      · -- x ∈ st.S
        have h_dx_eq_δx : st.d x = δ x := h_inv.hsettled x hx_S
        dsimp [d']
        by_cases h_edge_ux : (u, x) ∈ G.edges
        · have h_ineq : δ x ≤ δ u + (G.w u x : WithTop ℝ) :=
            G.delta_le_delta_add_edge hnn s δ hδ u x h_edge_ux
          have h_add : st.d x ≤ st.d u + (G.w u x : WithTop ℝ) := by
            rw [h_dx_eq_δx, h_du_eq_δu]
            exact h_ineq
          simp [h_edge_ux]
          have h_min_eq : min (st.d x) (st.d u + (G.w u x : WithTop ℝ)) = st.d x :=
            min_eq_left h_add
          rw [h_min_eq, h_dx_eq_δx]
        · simp [h_edge_ux, h_dx_eq_δx]
    have h_htent' : ∀ y ∉ S', ∀ x ∈ S', (x, y) ∈ G.edges → d' y ≤ δ x + (G.w x y : WithTop ℝ) := by
      intro y hy_S' x hx_S' h_edge
      have hy_notin_S : y ∉ st.S := by
        intro hy_S; apply hy_S'; simp [S', hy_S]
      rcases Finset.mem_insert.1 hx_S' with (rfl | hx_S)
      · -- x = u
        dsimp [d']
        have h_edge_uy : (u, y) ∈ G.edges := h_edge
        calc
          (if (u, y) ∈ G.edges then min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) else st.d y)
              = min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) := by simp [h_edge_uy]
          _ ≤ st.d u + (G.w u y : WithTop ℝ) := min_le_right _ _
          _ = δ u + (G.w u y : WithTop ℝ) := by rw [h_du_eq_δu]
      · -- x ∈ st.S
        have h_old_htent : st.d y ≤ δ x + (G.w x y : WithTop ℝ) :=
          h_inv.htent y hy_notin_S x hx_S h_edge
        dsimp [d']
        by_cases h_edge_uy : (u, y) ∈ G.edges
        · calc
            (if (u, y) ∈ G.edges then min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) else st.d y)
                = min (st.d y) (st.d u + (G.w u y : WithTop ℝ)) := by simp [h_edge_uy]
            _ ≤ st.d y := min_le_left _ _
            _ ≤ δ x + (G.w x y : WithTop ℝ) := h_old_htent
        · simp [h_edge_uy, h_old_htent]
    have h_valid' : ∀ y ∉ S', δ y ≤ d' y := by
      intro y hy_S'
      have hy_notin_S : y ∉ st.S := by
        intro hy_S; apply hy_S'; simp [S', hy_S]
      have h_old_valid : δ y ≤ st.d y := h_inv.hvalid y hy_notin_S
      by_cases h_edge_uy : (u, y) ∈ G.edges
      · have h_ineq : δ y ≤ δ u + (G.w u y : WithTop ℝ) :=
          G.delta_le_delta_add_edge hnn s δ hδ u y h_edge_uy
        have h_hvalid_via_add : δ y ≤ st.d u + (G.w u y : WithTop ℝ) := by
          rw [h_du_eq_δu]
          exact h_ineq
        simpa [d', h_edge_uy] using le_min_iff.mpr ⟨h_old_valid, h_hvalid_via_add⟩
      · simpa [d', h_edge_uy] using h_old_valid
    exact ⟨h_s_S', h_settled', h_htent', h_valid'⟩
  · rw [dif_neg hU]
    exact h_inv

/-- Fuelled Dijkstra loop.  `dijkstraLoop G s n` runs `n` iterations from the initial
state. -/
noncomputable def dijkstraLoop (G : WeightedGraph V) (s : V) (n : ℕ) : DijkstraState V :=
  Nat.recOn n (dijkstraInit s) (fun _ st => dijkstraStep G st)

/-- Each step adds exactly one vertex (if unsettled vertices remain) or zero (if all are settled).
    Returns `(card unchanged ∧ already all settled)` or `(+1 advancement)`. -/
lemma dijkstraStep_card_S (st : DijkstraState V) :
    ((dijkstraStep G st).S.card = st.S.card ∧ st.S = Finset.univ) ∨
    (dijkstraStep G st).S.card = st.S.card + 1 := by
  by_cases h_all : st.S = Finset.univ
  · -- all settled, step adds nothing
    have hcard : (dijkstraStep G st).S.card = st.S.card := by
      unfold dijkstraStep
      simp [h_all]
    left
    exact ⟨hcard, h_all⟩
  · -- unsettled vertices remain, step adds one
    have hU : (Finset.univ \ st.S).Nonempty := by
      have h_exists : ∃ v, v ∉ st.S := by
        by_contra! h_all_in
        apply h_all
        exact Finset.eq_univ_iff_forall.mpr h_all_in
      rcases h_exists with ⟨v, hv⟩
      refine ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩
    have hcard' : (dijkstraStep G st).S.card = st.S.card + 1 := by
      unfold dijkstraStep
      rw [dif_pos hU]
      have h_min : ∃ u ∈ (Finset.univ \ st.S), ∀ v ∈ (Finset.univ \ st.S), st.d u ≤ st.d v :=
        (Finset.univ \ st.S).exists_min_image st.d hU
      let u := Classical.choose h_min
      have hu_mem : u ∈ (Finset.univ \ st.S) :=
        (Classical.choose_spec h_min).1
      have hu_notin_S : u ∉ st.S := (Finset.mem_sdiff.1 hu_mem).2
      dsimp
      rw [Finset.card_insert_of_notMem hu_notin_S]
    right
    exact hcard'

/-- After `k` steps from the initial state, the settled set has size at least
`min k (Fintype.card V)`. -/
lemma dijkstraLoop_card_ge (G : WeightedGraph V) (s : V) (k : ℕ) :
    (dijkstraLoop G s k).S.card ≥ min k (Fintype.card V) := by
  induction k with
  | zero => simp [dijkstraLoop]
  | succ k ih =>
    have h_eq : dijkstraLoop G s (k+1) = dijkstraStep G (dijkstraLoop G s k) := by
      simp [dijkstraLoop]
    rw [h_eq]
    have hcases := G.dijkstraStep_card_S (dijkstraLoop G s k)
    rcases hcases with (⟨hcard, h_univ⟩ | hcard)
    · -- No addition, all vertices are already settled
      rw [hcard]
      have hcard' : (dijkstraLoop G s k).S.card = Fintype.card V := by
        simp [h_univ]
      rw [hcard']
      exact Nat.min_le_right (k+1) (Fintype.card V)
    · -- Added one unsettled vertex
      rw [hcard]
      omega

/-- After at least `Fintype.card V` iterations, all vertices are settled. -/
theorem dijkstraLoop_finish (G : WeightedGraph V) (s : V) (n : ℕ) (hn : Fintype.card V ≤ n) :
    (dijkstraLoop G s n).S = Finset.univ := by
  have hcard_ge : (dijkstraLoop G s n).S.card ≥ Fintype.card V := by
    have hmin : min n (Fintype.card V) = Fintype.card V := Nat.min_eq_right hn
    have h := G.dijkstraLoop_card_ge s n
    rw [hmin] at h
    exact h
  have hcard_le : (dijkstraLoop G s n).S.card ≤ Fintype.card V := by
    calc
      (dijkstraLoop G s n).S.card ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := card_univ
  have hcard_eq : (dijkstraLoop G s n).S.card = Fintype.card V := by omega
  have h_sub : (dijkstraLoop G s n).S ⊆ Finset.univ := Finset.subset_univ _
  exact Finset.eq_of_subset_of_card_le h_sub (by
    rw [hcard_eq, card_univ])

end WeightedGraph
end Chapter24
end CLRS