import CLRSLean.FourthEdition.Chapter_22.Section_22_1_Bellman_Ford

/-!
# CLRS Section 22.5 - Proofs of shortest paths

This section formalizes the theoretical properties of single-source shortest
paths that CLRS proves in §22.5, building on the walk and relaxation model of
Section 22.1.  For a graph with no negative-weight cycle, the single-source
distance {lit}`δ(s, v)` is the exact shortest-path weight; the Bellman-Ford
relaxation computes it after {lit}`|V| - 1` rounds
({lit}`CLRS.Chapter24.WeightedGraph.relaxDist_isShortestDist`, Theorem 22.4).

We introduce {lit}`shortestDist` as the distance function {lit}`δ`, and prove
the CLRS §22.5 backbone:

* **No-path property** (Lemma 22.13): {lit}`δ(s, v) = ⊤` iff no walk reaches
  {lit}`v` from {lit}`s`.
* **Upper-bound property** (Lemma 22.12): {lit}`δ(s, v)` lower-bounds the
  weight of every walk from {lit}`s` to {lit}`v`.
* **Triangle inequality** (Lemma 22.11): for every edge {lit}`(u, v)`,
  {lit}`δ(s, v) ≤ δ(s, u) + w(u, v)`.

## Main results

- Theorem `shortestDist_isShortestDist`: {lit}`δ(s, v)` is characterized as a
  lower bound on all walk weights that is either {lit}`⊤` or attained
- Theorem `noPath_iff_top` (Lemma 22.13)
- Theorem `shortestDist_le_walkWeight` (Lemma 22.12)
- Theorem `IsWalkFrom.append_edge`: appending a vertex along an edge extends a
  walk
- Theorem `shortestDist_triangleInequality` (Lemma 22.11)
- Theorem `shortestDist_triangle_walk`: the triangle inequality iterated along
  a walk
- Theorem `subpath_isShortest` (Lemma 22.10): a prefix of a shortest walk is
  shortest
- Theorem `shortestDist_convergence` (Lemma 22.14): relaxing a shortest path's
  final edge converges the endpoint estimate
- Theorem `relaxDist_eq_of_shortest_walk` (Lemma 22.15): after enough rounds a
  shortest walk is fully relaxed
- Theorem `predecessor_tight` (Lemma 22.16): the predecessor edge is tight, so
  the predecessor subgraph is a shortest-paths tree rooted at the source

The Dijkstra-correctness reformulation (Theorem 22.17) is not restated here;
Dijkstra correctness is already proved in Section 22.3.
-/

namespace CLRS
namespace Chapter24

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## The single-source shortest-path distance -/

/--
The single-source shortest-path distance {lit}`δ(s, v)`, defined via the
Bellman-Ford relaxation after {lit}`|V| - 1` rounds.  With no negative-weight
cycle this is the exact minimum weight of any walk from {lit}`s` to {lit}`v`
(Theorem 22.4).
-/
def shortestDist (s v : V) : WithTop ℝ :=
  G.relaxDist s (Fintype.card V - 1) v

/-- With no negative-weight cycle, {lit}`δ(s, v)` is a valid shortest distance:
it lower-bounds every walk weight and is either {lit}`⊤` or attained. -/
theorem shortestDist_isShortestDist (hNC : G.NoNegCycle) (s v : V) :
    G.IsShortestDist s v (G.shortestDist s v) := by
  unfold shortestDist
  exact G.relaxDist_isShortestDist hNC s v

/-- **Upper-bound property** (Lemma 22.12): the shortest distance {lit}`δ(s, v)`
lower-bounds the weight of every walk from {lit}`s` to {lit}`v`. -/
theorem shortestDist_le_walkWeight (hNC : G.NoNegCycle) (s v : V) (p : List V)
    (hp : G.IsWalkFrom s v p) :
    G.shortestDist s v ≤ (walkWeight G.w p : WithTop ℝ) :=
  (G.shortestDist_isShortestDist hNC s v).1 p hp

/-- **No-path property** (Lemma 22.13): {lit}`δ(s, v) = ⊤` iff there is no walk
from {lit}`s` to {lit}`v`. -/
theorem noPath_iff_top (hNC : G.NoNegCycle) (s v : V) :
    G.shortestDist s v = (⊤ : WithTop ℝ) ↔ ¬ ∃ p : List V, G.IsWalkFrom s v p := by
  constructor
  · intro htop hp
    rcases hp with ⟨p, hp⟩
    have hle : G.shortestDist s v ≤ (walkWeight G.w p : WithTop ℝ) :=
      (G.shortestDist_isShortestDist hNC s v).1 p hp
    rw [htop] at hle
    exact absurd hle (by
      intro htop_le
      -- ⊤ ≤ a real-typed WithTop value is impossible
      simpa [WithTop.top_le_iff] using htop_le)
  · intro hnp
    by_cases h : G.shortestDist s v = (⊤ : WithTop ℝ)
    · exact h
    · have hattained := (G.shortestDist_isShortestDist hNC s v).2
      rcases hattained with htop | ⟨p, hp, _⟩
      · exact False.elim (h htop)
      · exact False.elim (hnp ⟨p, hp⟩)

/-! ## Triangle inequality (Lemma 22.11) -/

/-- Appending the vertex {lit}`v` to a walk that ends at {lit}`u` along an edge
{lit}`(u, v)` yields a walk to {lit}`v`. -/
theorem IsWalkFrom.append_edge {s u v : V} {p : List V} (hp : G.IsWalkFrom s u p)
    (huv : (u, v) ∈ G.edges) :
    G.IsWalkFrom s v (p ++ [v]) := by
  refine ⟨?_, ?_, ?_⟩
  · refine List.IsChain.append hp.chain (by simp) ?_
    intro x hx y hy
    simp [hp.last] at hx
    simp at hy
    subst x
    subst y
    simpa [WeightedGraph.Adj] using huv
  · have hpne : p ≠ [] := hp.ne_nil
    simpa [List.head?_append_of_ne_nil p hpne] using hp.head
  · have hpne : p ≠ [] := hp.ne_nil
    simp [List.getLast?_append_of_ne_nil p]

/-- **Triangle inequality** (Lemma 22.11): for every edge {lit}`(u, v)`,
{lit}`δ(s, v) ≤ δ(s, u) + w(u, v)`. -/
theorem shortestDist_triangleInequality (hNC : G.NoNegCycle) (s u v : V)
    (huv : (u, v) ∈ G.edges) :
    G.shortestDist s v ≤ G.shortestDist s u + (G.w u v : WithTop ℝ) := by
  have hsu := G.shortestDist_isShortestDist hNC s u
  have hsv := G.shortestDist_isShortestDist hNC s v
  by_cases htop : G.shortestDist s u = (⊤ : WithTop ℝ)
  · -- δ(s,u) = ⊤ : RHS is ⊤
    rw [htop]
    exact le_top
  · rcases hsu.2 with htop' | ⟨p, hp, hpw⟩
    · exact False.elim (htop htop')
    · -- p is an s→u walk of weight δ(s,u); append the edge (u,v)
      have hpv : G.IsWalkFrom s v (p ++ [v]) := IsWalkFrom.append_edge G hp huv
      have hw : (walkWeight G.w (p ++ [v]) : WithTop ℝ) =
          (walkWeight G.w p : WithTop ℝ) + (G.w u v : WithTop ℝ) := by
        have hpne : p ≠ [] := hp.ne_nil
        have hlast : p.getLast hpne = u := by
          -- p is an s→u walk, so p.getLast? = some u
          simpa [List.getLast?_eq_some_getLast hpne] using hp.last
        rw [walkWeight_append_singleton G.w p hpne v, hlast]
        simp
      have hle := hsv.1 (p ++ [v]) hpv
      rw [hw, hpw] at hle
      exact hle

/-! ## Triangle inequality along a walk -/

/--
**Triangle inequality along a walk.**  If `q` is a walk from `u` to `v`, then
the shortest distance {lit}`δ(s, v)` is at most {lit}`δ(s, u)` plus the weight
of `q` (the CLRS triangle inequality, Lemma 22.11, iterated along the walk).
-/
theorem shortestDist_triangle_walk (hNC : G.NoNegCycle) (s : V) {u v : V} {q : List V}
    (hq : G.IsWalkFrom u v q) :
    G.shortestDist s v ≤ G.shortestDist s u + (walkWeight G.w q : WithTop ℝ) := by
  induction q generalizing u v with
  | nil => exact False.elim (by simpa using hq.head)
  | cons a t ih =>
      have ha : a = u := by simpa using hq.head
      subst ha
      cases t with
      | nil =>
          have hv : a = v := by simpa using hq.last
          subst hv
          simp
      | cons b t' =>
          have hchain := List.isChain_cons_cons.mp hq.chain
          have hedge : (a, b) ∈ G.edges := by simpa [WeightedGraph.Adj] using hchain.1
          have htail : G.IsWalkFrom b v (b :: t') := by
            refine ⟨hchain.2, ?_, ?_⟩
            · rfl
            · simpa using hq.last
          have htri : G.shortestDist s b ≤ G.shortestDist s a + (G.w a b : WithTop ℝ) :=
            G.shortestDist_triangleInequality hNC s a b hedge
          calc
            G.shortestDist s v ≤ G.shortestDist s b + (walkWeight G.w (b :: t') : WithTop ℝ) := ih htail
            _ ≤ (G.shortestDist s a + (G.w a b : WithTop ℝ)) + (walkWeight G.w (b :: t') : WithTop ℝ) := by
                gcongr
            _ = G.shortestDist s a + ((G.w a b : WithTop ℝ) + (walkWeight G.w (b :: t') : WithTop ℝ)) := by
                rw [add_assoc]
            _ = G.shortestDist s a + (walkWeight G.w (a :: b :: t') : WithTop ℝ) := rfl

/-! ## Subpath property (Lemma 22.10) -/

/--
**Subpath property (Lemma 22.10).**  If a shortest walk from `s` to `v`
decomposes as {lit}`l₁ ++ [u] ++ l₂` with {lit}`l₁ ++ [u]` a walk from `s` to
`u` and {lit}`u :: l₂` a walk from `u` to `v`, then the prefix {lit}`l₁ ++ [u]`
is a shortest walk from `s` to `u`.
-/
theorem subpath_isShortest (hNC : G.NoNegCycle) {s u v : V} {l₁ l₂ : List V}
    (hprefix : G.IsWalkFrom s u (l₁ ++ [u]))
    (hsuffix : G.IsWalkFrom u v (u :: l₂))
    (hshort : (walkWeight G.w (l₁ ++ u :: l₂) : WithTop ℝ) = G.shortestDist s v) :
    (walkWeight G.w (l₁ ++ [u]) : WithTop ℝ) = G.shortestDist s u := by
  have hsplit : walkWeight G.w (l₁ ++ u :: l₂) =
      walkWeight G.w (l₁ ++ [u]) + walkWeight G.w (u :: l₂) :=
    walkWeight_split G.w l₁ u l₂
  have hdecomp : G.shortestDist s v =
      (walkWeight G.w (l₁ ++ [u]) : WithTop ℝ) + (walkWeight G.w (u :: l₂) : WithTop ℝ) := by
    rw [← hshort, hsplit]
    push_cast
    rfl
  have hlb : G.shortestDist s u ≤ (walkWeight G.w (l₁ ++ [u]) : WithTop ℝ) :=
    G.shortestDist_le_walkWeight hNC s u (l₁ ++ [u]) hprefix
  have htri : G.shortestDist s v ≤ G.shortestDist s u + (walkWeight G.w (u :: l₂) : WithTop ℝ) :=
    G.shortestDist_triangle_walk hNC s hsuffix
  have hcombined : (walkWeight G.w (l₁ ++ [u]) : WithTop ℝ) + (walkWeight G.w (u :: l₂) : WithTop ℝ)
      ≤ G.shortestDist s u + (walkWeight G.w (u :: l₂) : WithTop ℝ) := by
    rw [← hdecomp]
    exact htri
  have hcancel := (WithTop.add_le_add_iff_right
    (WithTop.coe_ne_top : (walkWeight G.w (u :: l₂) : WithTop ℝ) ≠ ⊤)).mp hcombined
  exact le_antisymm hcancel hlb

/-! ## Convergence and path relaxation (Lemmas 22.14-22.15) -/

/-- **Nonincreasing rounds.**  Bellman-Ford estimates never increase as the
round count grows. -/
theorem relaxDist_antitone (s v : V) : Antitone (fun k : ℕ => G.relaxDist s k v) := by
  refine antitone_nat_of_succ_le ?_
  intro k
  exact G.relaxDist_succ_le s k v

/--
**Convergence property (Lemma 22.14).**  If the estimate at `u` has converged
to {lit}`δ(s, u)` after `k` rounds and {lit}`(u, v)` is the final edge of a
shortest path ({lit}`δ(s, v) = δ(s, u) + w(u, v)`), then one more relaxation
round brings the estimate at `v` to {lit}`δ(s, v)`.
-/
theorem shortestDist_convergence {s u v : V} (huv : (u, v) ∈ G.edges)
    {k : ℕ} (hk : k + 1 ≤ Fintype.card V - 1)
    (hconv : G.relaxDist s k u = G.shortestDist s u)
    (hshort : G.shortestDist s v = G.shortestDist s u + (G.w u v : WithTop ℝ)) :
    G.relaxDist s (k + 1) v = G.shortestDist s v := by
  apply le_antisymm
  · rw [relaxDist_succ_apply]
    calc G.relaxStep (G.relaxDist s k) v
        ≤ G.relaxDist s k u + (G.w u v : WithTop ℝ) := G.relaxStep_le_pred huv
      _ = G.shortestDist s v := by rw [hconv, hshort]
  · simpa [WeightedGraph.shortestDist] using G.relaxDist_antitone s v hk

/--
**Path-relaxation property (Lemma 22.15).**  If `p` is a shortest walk from `s`
to `v` with at most {lit}`|V|` vertices, then after {lit}`p.length - 1`
relaxation rounds the estimate at `v` equals the walk weight.
-/
theorem relaxDist_eq_of_shortest_walk (s v : V) (p : List V)
    (hp : G.IsWalkFrom s v p)
    (hshort : (walkWeight G.w p : WithTop ℝ) = G.shortestDist s v)
    (hlen : p.length ≤ Fintype.card V) :
    G.relaxDist s (p.length - 1) v = (walkWeight G.w p : WithTop ℝ) := by
  apply le_antisymm
  · refine G.relaxDist_le_walkWeight s (p.length - 1) v p hp ?_
    have hpne : p ≠ [] := hp.ne_nil
    have hpos : 0 < p.length := List.length_pos_iff.mpr hpne
    omega
  · rw [hshort]
    have hpne : p ≠ [] := hp.ne_nil
    have hpos : 0 < p.length := List.length_pos_iff.mpr hpne
    have hk : p.length - 1 ≤ Fintype.card V - 1 := by omega
    simpa [WeightedGraph.shortestDist] using G.relaxDist_antitone s v hk

/-! ## Predecessor subgraph (Lemma 22.16) -/

/-- The vertex `u` in the predecessor set of `v` that minimizes
{lit}`δ(s, u) + w(u, v)`: the predecessor of `v` on a shortest `s`-rooted path.
If `v` has no incoming edge the value is `v` (a junk value). -/
noncomputable def predecessor (s v : V) : V :=
  if h : (G.preds v).Nonempty then
    Classical.choose (Finset.exists_mem_eq_inf (G.preds v) h
      (fun u => G.shortestDist s u + (G.w u v : WithTop ℝ)))
  else v

/-- A reachable non-source vertex has an incoming edge, so its predecessor set
is nonempty. -/
theorem preds_nonempty_of_walk (s v : V) (hv : v ≠ s) (hreach : ∃ p : List V, G.IsWalkFrom s v p) :
    (G.preds v).Nonempty := by
  rcases hreach with ⟨p, hp⟩
  have hpne : p ≠ [] := hp.ne_nil
  have hlast : p.getLast hpne = v := by
    have := hp.last
    rw [List.getLast?_eq_some_getLast hpne] at this
    exact Option.some.inj this
  have hsplit : p = p.dropLast ++ [v] := by
    conv_lhs => rw [← List.dropLast_append_getLast hpne]
    rw [hlast]
  have hdl_ne : p.dropLast ≠ [] := by
    intro hcontra
    have hlen1 : p.length = 1 := by rw [hsplit, hcontra]; simp
    rcases p with _ | ⟨x, t⟩
    · exact hpne rfl
    · have ht : t = [] := by
        have : (x :: t).length = 1 := hlen1
        simpa using this
      subst ht
      have hxs : x = s := by simpa using hp.head
      have hxv : x = v := by simpa using hp.last
      exact hv (hxv.symm.trans hxs)
  have hu : ∃ u : V, p.dropLast.getLast? = some u := by
    rw [List.getLast?_eq_some_getLast hdl_ne]
    exact ⟨_, rfl⟩
  rcases hu with ⟨u, hu⟩
  have hchain : List.IsChain G.Adj (p.dropLast ++ [v]) := by rw [← hsplit]; exact hp.chain
  have happ := List.isChain_append.1 hchain
  have hedge : G.Adj u v := happ.2.2 u (Option.mem_def.mpr hu) v (Option.mem_def.mpr (by simp))
  refine ⟨u, ?_⟩
  simpa [WeightedGraph.preds, WeightedGraph.Adj] using hedge

/--
**Bellman equation (incoming-edge form).**  For a reachable non-source vertex
`v`, the shortest distance is the minimum over incoming edges {lit}`(u, v)` of
{lit}`δ(s, u) + w(u, v)`.
-/
theorem shortestDist_eq_inf_preds (hNC : G.NoNegCycle) (s v : V) (hv : v ≠ s)
    (hreach : ∃ p : List V, G.IsWalkFrom s v p) :
    G.shortestDist s v = (G.preds v).inf (fun u => G.shortestDist s u + (G.w u v : WithTop ℝ)) := by
  apply le_antisymm
  · apply Finset.le_inf
    intro u hu
    have hedge : (u, v) ∈ G.edges := by simpa [WeightedGraph.preds] using hu
    exact G.shortestDist_triangleInequality hNC s u v hedge
  · rcases (G.shortestDist_isShortestDist hNC s v).2 with htop | ⟨p, hp, hpw⟩
    · exact False.elim ((G.noPath_iff_top hNC s v).mp htop hreach)
    · have hpne : p ≠ [] := hp.ne_nil
      have hlast : p.getLast hpne = v := by
        have := hp.last
        rw [List.getLast?_eq_some_getLast hpne] at this
        exact Option.some.inj this
      have hsplit : p = p.dropLast ++ [v] := by
        conv_lhs => rw [← List.dropLast_append_getLast hpne]
        rw [hlast]
      have hdl_ne : p.dropLast ≠ [] := by
        intro hcontra
        have hlen1 : p.length = 1 := by rw [hsplit, hcontra]; simp
        rcases p with _ | ⟨x, t⟩
        · exact hpne rfl
        · have ht : t = [] := by
            have : (x :: t).length = 1 := hlen1
            simpa using this
          subst ht
          have hxs : x = s := by simpa using hp.head
          have hxv : x = v := by simpa using hp.last
          exact hv (hxv.symm.trans hxs)
      have hu : ∃ u : V, p.dropLast.getLast? = some u := by
        rw [List.getLast?_eq_some_getLast hdl_ne]
        exact ⟨_, rfl⟩
      rcases hu with ⟨u, hu⟩
      have hchain : List.IsChain G.Adj (p.dropLast ++ [v]) := by rw [← hsplit]; exact hp.chain
      have happ := List.isChain_append.1 hchain
      have hedge : G.Adj u v := happ.2.2 u (Option.mem_def.mpr hu) v (Option.mem_def.mpr (by simp))
      have hu_pred : u ∈ G.preds v := by simpa [WeightedGraph.preds, WeightedGraph.Adj] using hedge
      have hprefix_head : (p.dropLast).head? = some s := by
        have hph := hp.head
        rw [hsplit, List.head?_append_of_ne_nil _ hdl_ne] at hph
        exact hph
      have hprefix_walk : G.IsWalkFrom s u (p.dropLast) := ⟨happ.1, hprefix_head, hu⟩
      have hlb_u : G.shortestDist s u ≤ (walkWeight G.w (p.dropLast) : WithTop ℝ) :=
        (G.shortestDist_isShortestDist hNC s u).1 (p.dropLast) hprefix_walk
      have hgl : p.dropLast.getLast hdl_ne = u := by
        have := List.getLast?_eq_some_getLast hdl_ne
        rw [hu] at this
        exact (Option.some.inj this).symm
      have hweight : walkWeight G.w p = walkWeight G.w (p.dropLast) + G.w u v := by
        conv_lhs => rw [hsplit]
        rw [walkWeight_append_singleton G.w (p.dropLast) hdl_ne v, hgl]
      calc
        (G.preds v).inf (fun x => G.shortestDist s x + (G.w x v : WithTop ℝ))
            ≤ G.shortestDist s u + (G.w u v : WithTop ℝ) := Finset.inf_le hu_pred
        _ ≤ (walkWeight G.w (p.dropLast) : WithTop ℝ) + (G.w u v : WithTop ℝ) := by gcongr
        _ = (walkWeight G.w p : WithTop ℝ) := by rw [hweight]; push_cast; rfl
        _ = G.shortestDist s v := hpw

/-- The chosen predecessor is a genuine incoming neighbor of `v`. -/
theorem predecessor_isPredecessor (s v : V) (hv : v ≠ s) (hreach : ∃ p : List V, G.IsWalkFrom s v p) :
    G.predecessor s v ∈ G.preds v := by
  have hne : (G.preds v).Nonempty := G.preds_nonempty_of_walk s v hv hreach
  unfold predecessor
  rw [dif_pos hne]
  exact (Classical.choose_spec (Finset.exists_mem_eq_inf (G.preds v) hne
    (fun u => G.shortestDist s u + (G.w u v : WithTop ℝ)))).1

/-- The chosen predecessor minimizes {lit}`δ(s, ·) + w(·, v)` over the incoming
neighbors of `v`. -/
theorem predecessor_inf_eq (s v : V) (hv : v ≠ s) (hreach : ∃ p : List V, G.IsWalkFrom s v p) :
    (G.preds v).inf (fun u => G.shortestDist s u + (G.w u v : WithTop ℝ)) =
      G.shortestDist s (G.predecessor s v) + (G.w (G.predecessor s v) v : WithTop ℝ) := by
  have hne : (G.preds v).Nonempty := G.preds_nonempty_of_walk s v hv hreach
  unfold predecessor
  rw [dif_pos hne]
  exact (Classical.choose_spec (Finset.exists_mem_eq_inf (G.preds v) hne
    (fun u => G.shortestDist s u + (G.w u v : WithTop ℝ)))).2

/--
**Predecessor-subgraph property (Lemma 22.16).**  The predecessor edge is
tight: for a reachable non-source vertex `v`,
{lit}`δ(s, v) = δ(s, π(v)) + w(π(v), v)`.  This is the condition under which
the predecessor subgraph is a shortest-paths tree rooted at `s`.
-/
theorem predecessor_tight (hNC : G.NoNegCycle) (s v : V) (hv : v ≠ s)
    (hreach : ∃ p : List V, G.IsWalkFrom s v p) :
    G.shortestDist s v = G.shortestDist s (G.predecessor s v) +
        (G.w (G.predecessor s v) v : WithTop ℝ) := by
  rw [G.shortestDist_eq_inf_preds hNC s v hv hreach]
  exact G.predecessor_inf_eq s v hv hreach

end WeightedGraph

end Chapter24
end CLRS
