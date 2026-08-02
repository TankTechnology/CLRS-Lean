import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

/-!
# CLRS Section 24.5 - Proofs of shortest paths

This section formalizes the theoretical properties of single-source shortest
paths that CLRS proves in §24.5, building on the walk and relaxation model of
Section 24.1.  For a graph with no negative-weight cycle, the single-source
distance {lit}`δ(s, v)` is the exact shortest-path weight; the Bellman-Ford
relaxation computes it after {lit}`|V| - 1` rounds
({lit}`CLRS.Chapter24.WeightedGraph.relaxDist_isShortestDist`, Theorem 24.4).

We introduce {lit}`shortestDist` as the distance function {lit}`δ`, and prove
the CLRS §24.5 backbone:

* **No-path property** (Lemma 24.13): {lit}`δ(s, v) = ⊤` iff no walk reaches
  {lit}`v` from {lit}`s`.
* **Upper-bound property** (Lemma 24.12): {lit}`δ(s, v)` lower-bounds the
  weight of every walk from {lit}`s` to {lit}`v`.
* **Triangle inequality** (Lemma 24.11): for every edge {lit}`(u, v)`,
  {lit}`δ(s, v) ≤ δ(s, u) + w(u, v)`.

## Main results

- Theorem `shortestDist_isShortestDist`: {lit}`δ(s, v)` is characterized as a
  lower bound on all walk weights that is either {lit}`⊤` or attained
- Theorem `noPath_iff_top` (Lemma 24.13)
- Theorem `shortestDist_le_walkWeight` (Lemma 24.12)
- Theorem `IsWalkFrom.append_edge`: appending a vertex along an edge extends a
  walk
- Theorem `shortestDist_triangleInequality` (Lemma 24.11)

## Current gaps

The subpath property (Lemma 24.10), the convergence/path-relaxation lemmas
(Lemmas 24.14-24.15), the predecessor-subgraph property (Lemma 24.16), and the
Dijkstra-correctness reformulation (Theorem 24.17) are not restated here;
Dijkstra correctness is already proved in Section 24.3, and
{lit}`relaxDist_stabilizes` records the Bellman-Ford convergence.
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
(Theorem 24.4).
-/
def shortestDist (s v : V) : WithTop ℝ :=
  G.relaxDist s (Fintype.card V - 1) v

/-- With no negative-weight cycle, {lit}`δ(s, v)` is a valid shortest distance:
it lower-bounds every walk weight and is either {lit}`⊤` or attained. -/
theorem shortestDist_isShortestDist (hNC : G.NoNegCycle) (s v : V) :
    G.IsShortestDist s v (G.shortestDist s v) := by
  unfold shortestDist
  exact G.relaxDist_isShortestDist hNC s v

/-- **Upper-bound property** (Lemma 24.12): the shortest distance {lit}`δ(s, v)`
lower-bounds the weight of every walk from {lit}`s` to {lit}`v`. -/
theorem shortestDist_le_walkWeight (hNC : G.NoNegCycle) (s v : V) (p : List V)
    (hp : G.IsWalkFrom s v p) :
    G.shortestDist s v ≤ (walkWeight G.w p : WithTop ℝ) :=
  (G.shortestDist_isShortestDist hNC s v).1 p hp

/-- **No-path property** (Lemma 24.13): {lit}`δ(s, v) = ⊤` iff there is no walk
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

/-! ## Triangle inequality (Lemma 24.11) -/

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

/-- **Triangle inequality** (Lemma 24.11): for every edge {lit}`(u, v)`,
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

end WeightedGraph

end Chapter24
end CLRS
