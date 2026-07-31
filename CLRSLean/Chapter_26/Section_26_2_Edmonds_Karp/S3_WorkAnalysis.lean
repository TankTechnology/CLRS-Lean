import Mathlib
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S1_ShortestAugmentingPath
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S2_EK_Loop

/-!
# 26.2 S3. The O(VE²) work analysis

This module develops the mathematical core of the Edmonds-Karp complexity
analysis: critical edges and the distance-growth lemma.

An edge `(u,v)` of the selected augmenting path is *critical* when
augmentation saturates it (its residual capacity drops to zero).  Every
augmentation saturates at least one edge (the bottleneck is attained by some
path edge).  The key lemma (CLRS Lemma 26.8) states that when `(u,v)` is on a
shortest augmenting path and later `(v,u)` is on another shortest augmenting
path (the only way the residual capacity of `(u,v)` can recover), the residual
distance to `u` has increased by at least two:

`δ'(u) = δ'(v) + 1 ≥ δ(v) + 1 = δ(u) + 2`

Here the first equality is the BFS-path property on the later path, the
inequality is monotonicity (Lemma 26.7), and the last equality is the
BFS-path property on the earlier path.  Since residual distances are bounded
by `|V| - 1` (shortest paths are simple), each edge can be critical at most
`|V|` times, giving `O(VE)` augmentations and `O(VE²)` total work.

Main results:

- `Flow.AugmentingPath.isCritical`: an edge saturated by the augmentation
- `exists_critical_edge`: every augmentation saturates at least one edge
- `shortest_edge_dist`: edges of a shortest path join adjacent distance
  levels
- `critical_dist_increase`: CLRS Lemma 26.8 (distance to `u` grows by at
  least two between consecutive critical appearances)
- `IsShortestDist.lt_card`: residual distances are bounded by `|V| - 1`
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- An edge of the selected augmenting path is *critical* when augmentation
saturates it: its residual capacity after augmentation is zero. -/
def Flow.AugmentingPath.isCritical {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {φ : Flow V G} (p : Flow.AugmentingPath φ) (u v : V) : Prop :=
  (u, v) ∈ p.edges ∧ (φ.augment p).residualCapacity u v = 0

/-- In a simple list, equal elements occur at the same index. -/
lemma nodup_getElem_inj {α : Type*} {l : List α} (h : l.Nodup)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : l[i] = l[j]) : i = j := by
  revert h i j hi hj
  induction l with
  | nil => simp
  | cons a l ih =>
      intro h i j hi hj hij
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              exfalso
              have hj' : j < l.length := by simpa using hj
              have ha_eq : a = l[j] := by simpa using hij
              have ha : a ∈ l := by
                simp [ha_eq]
              exact (List.nodup_cons.mp h).1 ha
      | succ i =>
          cases j with
          | zero =>
              exfalso
              have hi' : i < l.length := by simpa using hi
              have ha_eq : a = l[i] := by
                have hla : l[i] = a := by simpa using hij
                exact hla.symm
              have ha : a ∈ l := by
                simp [ha_eq]
              exact (List.nodup_cons.mp h).1 ha
          | succ j =>
              have hi' : i < l.length := by simpa using hi
              have hj' : j < l.length := by simpa using hj
              have hih : i = j :=
                ih (List.nodup_cons.mp h).2 hi' hj' (by simpa using hij)
              omega

/-- A simple path contains no pair of opposite directed edges. -/
lemma edge_reverse_not_mem {φ : Flow V G} (p : Flow.AugmentingPath φ) {u v : V}
    (huv : (u, v) ∈ p.edges) : (v, u) ∉ p.edges := by
  intro hvu
  rcases p.exists_index_of_mem_edges huv with ⟨i, hi, hvi, hui⟩
  rcases p.exists_index_of_mem_edges hvu with ⟨j, hj, hvj, huj⟩
  have h1 : i + 1 = j := by
    exact nodup_getElem_inj p.nodup (by omega) (by omega) (hui.trans hvj.symm)
  have h2 : i = j + 1 := by
    exact nodup_getElem_inj p.nodup (by omega) (by omega) (hvi.trans huj.symm)
  omega

/-- Every augmentation saturates at least one edge of the selected path. -/
lemma exists_critical_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {φ : Flow V G} (p : Flow.AugmentingPath φ) :
    ∃ u v, p.isCritical u v := by
  have hmem : p.bottleneck ∈ p.edges.toFinset.image (fun e => φ.residualCapacity e.1 e.2) := by
    unfold Flow.AugmentingPath.bottleneck
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨e, he, hEq⟩
  have he_edges : e ∈ p.edges := List.mem_toFinset.mp he
  have hpost : (φ.augment p).residualCapacity e.1 e.2 = 0 := by
    rw [Flow.augment_residualCapacity]
    have hrev : (e.2, e.1) ∉ p.edges := edge_reverse_not_mem p he_edges
    rw [hEq]
    simp [he_edges, hrev]
  exact ⟨e.1, e.2, he_edges, hpost⟩

/-- Every edge of a shortest augmenting path joins adjacent distance levels:
`δ(u) = i` and `δ(v) = i + 1`. -/
lemma shortest_edge_dist {φ : Flow V G} (p : ShortestAugmentingPath φ) {u v : V}
    (huv : (u, v) ∈ p.path.edges) :
    ∃ d, IsShortestDist φ G.s u d ∧ IsShortestDist φ G.s v (d + 1) := by
  rcases p.path.exists_index_of_mem_edges huv with ⟨i, hi, hvi, hui⟩
  have hpref_u := p.shortest_prefix i (by omega)
  have hpref_v := p.shortest_prefix (i + 1) hi
  refine ⟨i, ?_, ?_⟩
  · simpa [hvi] using hpref_u
  · simpa [hui] using hpref_v

/-- **CLRS Lemma 26.8 (critical-edge distance growth).**  If `(u,v)` is on a
shortest augmenting path of `φ` and later `(v,u)` is on a shortest augmenting
path of `ψ`, with residual distances not decreasing from `φ` to `ψ`, then the
residual distance to `u` in `ψ` exceeds that in `φ` by at least two:

`δ_ψ(u) = δ_ψ(v) + 1 ≥ δ_φ(v) + 1 = δ_φ(u) + 2`. -/
lemma critical_dist_increase {φ : Flow V G} (p : ShortestAugmentingPath φ)
    {ψ : Flow V G} (q : ShortestAugmentingPath ψ) {u v : V}
    (hp : (u, v) ∈ p.path.edges) (hq : (v, u) ∈ q.path.edges)
    (hmono : ∀ w d, IsShortestDist φ G.s w d →
      ∃ d', IsShortestDist ψ G.s w d' ∧ d ≤ d') :
    ∃ du du', IsShortestDist φ G.s u du ∧ IsShortestDist ψ G.s u du' ∧ du + 2 ≤ du' := by
  rcases shortest_edge_dist p hp with ⟨du, hdu, hdv⟩
  rcases shortest_edge_dist q hq with ⟨dv', hdv', hdu'⟩
  rcases hmono v (du + 1) hdv with ⟨dv'', hdv'', hle⟩
  have hdv_eq : dv'' = dv' := hdv''.unique hdv'
  refine ⟨du, dv' + 1, hdu, hdu', ?_⟩
  have : du + 1 ≤ dv'' := hle
  omega

/-- Residual distances are bounded by the number of vertices minus one:
shortest paths are simple. -/
lemma IsShortestDist.lt_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {φ : Flow V G} {v : V} {d : ℕ}
    (hd : IsShortestDist φ G.s v d) : d < Fintype.card V := by
  have hlen : (back d v hd).length = d + 1 := back_length d v hd
  have hcard : (back d v hd).length ≤ Fintype.card V :=
    List.Nodup.length_le_card (back_nodup d v hd)
  omega

end Chapter26
end CLRS
