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

end WeightedGraph
end Chapter24
end CLRS
