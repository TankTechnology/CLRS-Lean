import Mathlib
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.Ford_Fulkerson_Augmentation

/-!
# 26.2. The Edmonds-Karp Algorithm (partial)

This section formalizes the residual-distance infrastructure used by the
Edmonds-Karp analysis and proves the monotonic residual-distance theorem
(CLRS Lemma 26.7) for augmentation along a shortest residual path.

Main results:

- `ResidualPathLength`: inductive predicate for path existence in `G_f`
- `IsShortestDist`: shortest-path distance in `G_f`
- `isShortestDist_self`: the residual distance from a vertex to itself is zero
- `IsShortestDist.unique`: shortest residual distances are unique
- `isShortestDist_triangle`: one residual edge extends a shortest path by at
  most one step
- `ShortestAugmentingPath`: bundled shortest source-to-sink residual path data
- `IsShortestDist.exists_predecessor`: predecessor and exact-distance witness
  for a positive shortest path
- `ShortestAugmentingPath.shortest_prefix`: every prefix of a shortest
  augmenting path is itself shortest
- `ShortestAugmentingPath.exists_shortestDist_le_augment`: augmentation cannot
  create a smaller finite source distance
- `shortest_path_nondec`: CLRS Lemma 26.7

The shortest-path construction itself lives in the companion submodule
`S1_ShortestAugmentingPath`, whose headline result
`exists_shortest_augmenting_path` turns residual reachability into an explicit
shortest augmenting path.

The work analysis lives in `S3_WorkAnalysis`: critical edges, Lemma 26.8,
the recovery-step timeline lemma, and the full `O(VE²)` counting argument
(`critical_count_bound` and `augmentation_count_bound`).

Current gaps:

- Add an executable BFS.
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

inductive ResidualPathLength (φ : Flow V G) : V → V → ℕ → Prop where
  | refl (u : V) : ResidualPathLength φ u u 0
  | tail (u v w : V) (n : ℕ) : ResidualPathLength φ u v n → Flow.residualEdge φ v w →
      ResidualPathLength φ u w (n + 1)

/-- Concatenation of length-indexed residual paths. -/
theorem ResidualPathLength.trans {φ : Flow V G} {u v w : V} {m n : ℕ}
    (h₁ : ResidualPathLength φ u v m) (h₂ : ResidualPathLength φ v w n) :
    ResidualPathLength φ u w (m + n) := by
  induction h₂ generalizing u with
  | refl => simpa using h₁
  | tail mid w n hprev hedge ih =>
      have h := ResidualPathLength.tail u mid w (m + n) (ih h₁) hedge
      simpa [Nat.add_assoc] using h

def IsShortestDist (φ : Flow V G) (u v : V) (d : ℕ) : Prop :=
  ResidualPathLength φ u v d ∧ ∀ n, ResidualPathLength φ u v n → d ≤ n

lemma isShortestDist_self (φ : Flow V G) (u : V) : IsShortestDist φ u u 0 := by
  refine ⟨ResidualPathLength.refl u, ?_⟩
  intro n hn
  cases hn with
  | refl => exact Nat.zero_le _
  | tail _ _ _ _ _ => apply Nat.zero_le

lemma IsShortestDist.unique {φ : Flow V G} {u v : V} {d₁ d₂ : ℕ}
    (h₁ : IsShortestDist φ u v d₁) (h₂ : IsShortestDist φ u v d₂) : d₁ = d₂ := by
  rcases h₁ with ⟨hpath₁, hmin₁⟩
  rcases h₂ with ⟨hpath₂, hmin₂⟩
  exact le_antisymm (hmin₁ d₂ hpath₂) (hmin₂ d₁ hpath₁)

lemma isShortestDist_triangle (φ : Flow V G) (s u v : V) (d : ℕ)
    (hsu : IsShortestDist φ s u d) (h_edge : Flow.residualEdge φ u v) :
    ∃ d', IsShortestDist φ s v d' ∧ d' ≤ d + 1 := by
  rcases hsu with ⟨hsu_path, hsu_min⟩
  have hsv_path : ResidualPathLength φ s v (d + 1) :=
    ResidualPathLength.tail s u v d hsu_path h_edge
  have h_exists_v : ∃ n, ResidualPathLength φ s v n := ⟨d + 1, hsv_path⟩
  let d' := Nat.find h_exists_v
  have h_d'_path : ResidualPathLength φ s v d' := Nat.find_spec h_exists_v
  have h_d'_min : ∀ n, ResidualPathLength φ s v n → d' ≤ n :=
    fun n hn => Nat.find_min' h_exists_v hn
  have h_d'_le : d' ≤ d + 1 := Nat.find_min' h_exists_v hsv_path
  exact ⟨d', ⟨h_d'_path, h_d'_min⟩, h_d'_le⟩

/-- A positive-length shortest residual path has a predecessor whose distance
is exactly one smaller. -/
lemma exists_pred_on_path {φ : Flow V G} {s v : V} {d : ℕ}
    (hd : IsShortestDist φ s v d) (hd_pos : d ≠ 0) :
    ∃ u, Flow.residualEdge φ u v ∧ IsShortestDist φ s u (d - 1) := by
  rcases hd with ⟨hpath, hmin⟩
  cases hpath with
  | refl => exact (hd_pos rfl).elim
  | tail u v n hpath_to_u hedge =>
      have hu_min : ∀ m, ResidualPathLength φ s u m → n ≤ m := by
        intro m hm
        have hextend : ResidualPathLength φ s v (m + 1) :=
          ResidualPathLength.tail s u v m hm hedge
        have := hmin (m + 1) hextend
        omega
      refine ⟨u, hedge, ?_⟩
      simpa [IsShortestDist] using And.intro hpath_to_u hu_min

/-- Successor-form predecessor theorem, convenient for induction on a known
positive distance. -/
theorem IsShortestDist.exists_predecessor {φ : Flow V G} {s v : V} {d : ℕ}
    (hd : IsShortestDist φ s v (d + 1)) :
    ∃ u, Flow.residualEdge φ u v ∧ IsShortestDist φ s u d := by
  simpa using exists_pred_on_path hd (by omega)

/-- A shortest augmenting path tied directly to the concrete path consumed by
`Flow.augment`. -/
structure ShortestAugmentingPath (φ : Flow V G) where
  /-- The concrete simple residual path to augment. -/
  path : Flow.AugmentingPath φ
  /-- Its edge count realizes the source-to-sink residual distance. -/
  h_shortest : IsShortestDist φ G.s G.t path.edges.length

private lemma residualPathLength_segment (φ : Flow V G) (xs : List V)
    (hchain : xs.IsChain φ.residualEdge) (i k : ℕ)
    (hik : i + k < xs.length) :
    ResidualPathLength φ xs[i] xs[i + k] k := by
  induction k with
  | zero => simpa using ResidualPathLength.refl (φ := φ) xs[i]
  | succ k ih =>
      have hik' : i + k < xs.length := by omega
      have hedge : φ.residualEdge xs[i + k] xs[i + k + 1] :=
        hchain.getElem (i + k) (by omega)
      have htail := ResidualPathLength.tail (φ := φ)
        xs[i] xs[i + k] xs[i + k + 1] k (ih hik') hedge
      simpa [Nat.add_assoc] using htail

private lemma getElem_zero_eq_of_head?_eq_some {α : Type*} {xs : List α} {u : α}
    (hzero : 0 < xs.length) (hhead : xs.head? = some u) :
    xs[0] = u := by
  cases xs with
  | nil => simp at hzero
  | cons x tail => simpa using hhead

private lemma getElem_last_eq_of_getLast?_eq_some
    {α : Type*} {xs : List α} {u : α}
    (hne : xs ≠ []) (hlast : xs.getLast? = some u) :
    xs[xs.length - 1]'(Nat.sub_lt (List.length_pos_iff.mpr hne) (by omega)) = u := by
  rw [← List.getLast_eq_getElem hne]
  exact List.getLast_of_getLast?_eq_some hlast

/-- The prefix through index `i` is a residual path of exactly `i` edges. -/
theorem ShortestAugmentingPath.prefix_path {φ : Flow V G}
    (p : ShortestAugmentingPath φ) (i : ℕ)
    (hi : i < p.path.vertices.length) :
    ResidualPathLength φ G.s p.path.vertices[i] i := by
  have hsegment := residualPathLength_segment φ p.path.vertices p.path.chain 0 i (by
    simpa using hi)
  have hfirst : p.path.vertices[0] = G.s :=
    getElem_zero_eq_of_head?_eq_some (by omega) p.path.head_eq
  simpa [hfirst] using hsegment

/-- The suffix from index `i` reaches the sink in the remaining edge count. -/
theorem ShortestAugmentingPath.suffix_path {φ : Flow V G}
    (p : ShortestAugmentingPath φ) (i : ℕ)
    (hi : i < p.path.vertices.length) :
    ResidualPathLength φ p.path.vertices[i] G.t (p.path.edges.length - i) := by
  have hne : p.path.vertices ≠ [] := by
    intro hnil
    simpa [hnil] using p.path.head_eq
  have hedges_length := p.path.edges_length
  have hi_le_edges : i ≤ p.path.edges.length := by omega
  have hsegment := residualPathLength_segment φ p.path.vertices p.path.chain i
    (p.path.edges.length - i) (by omega)
  have hlast : p.path.vertices[p.path.edges.length] = G.t := by
    simpa only [hedges_length] using
      getElem_last_eq_of_getLast?_eq_some hne p.path.last_eq
  simpa [Nat.add_sub_of_le hi_le_edges, hlast] using hsegment

/-- Every prefix of a shortest augmenting path is itself shortest. -/
theorem ShortestAugmentingPath.shortest_prefix {φ : Flow V G}
    (p : ShortestAugmentingPath φ) (i : ℕ)
    (hi : i < p.path.vertices.length) :
    IsShortestDist φ G.s p.path.vertices[i] i := by
  refine ⟨p.prefix_path i hi, ?_⟩
  intro n hn
  have htotal := hn.trans (p.suffix_path i hi)
  have hmin := p.h_shortest.2 _ htotal
  have hi_le_edges : i ≤ p.path.edges.length := by
    rw [p.path.edges_length]
    omega
  omega

private theorem ShortestAugmentingPath.exists_shortestDist_le_pathLength_augment
    {φ : Flow V G} (p : ShortestAugmentingPath φ) {v : V} {n : ℕ}
    (hpath : ResidualPathLength (φ.augment p.path) G.s v n) :
    ∃ d, IsShortestDist φ G.s v d ∧ d ≤ n := by
  induction hpath with
  | refl =>
      exact ⟨0, isShortestDist_self φ G.s, le_rfl⟩
  | tail u v n hpath_to_u hedge ih =>
      rcases ih with ⟨du, hdu, hdu_le⟩
      by_cases hold : φ.residualEdge u v
      · rcases isShortestDist_triangle φ G.s u v du hdu hold with
          ⟨dv, hdv, hdv_le⟩
        exact ⟨dv, hdv, by omega⟩
      · have hreverse : (v, u) ∈ p.path.edges :=
          p.path.reverse_mem_edges_of_new_residualEdge hedge hold
        rcases p.path.exists_index_of_mem_edges hreverse with
          ⟨i, hi, hvi, hui⟩
        have hpref_v := p.shortest_prefix i (by omega)
        have hpref_u := p.shortest_prefix (i + 1) hi
        have hdv : IsShortestDist φ G.s v i := by
          simpa [hvi] using hpref_v
        have hdu_path : IsShortestDist φ G.s u (i + 1) := by
          simpa [hui] using hpref_u
        have hdu_eq : du = i + 1 := hdu.unique hdu_path
        exact ⟨i, hdv, by omega⟩

/-- Every vertex at finite residual distance after augmentation already had a
finite residual distance before augmentation, no larger than the new one.

This is the path-lifting core of Lemma 26.7.  An edge that already existed uses
the one-edge triangle theorem.  If an edge is new, the concrete augmentation
formula identifies its reverse on the chosen augmenting path; shortest-prefix
optimality then supplies the old distance directly.
-/
theorem ShortestAugmentingPath.exists_shortestDist_le_augment
    {φ : Flow V G} (p : ShortestAugmentingPath φ) {v : V} {d' : ℕ}
    (hd' : IsShortestDist (φ.augment p.path) G.s v d') :
    ∃ d, IsShortestDist φ G.s v d ∧ d ≤ d' := by
  exact p.exists_shortestDist_le_pathLength_augment hd'.1

/-- **CLRS Lemma 26.7 (monotonic residual distance).**  Augmenting along a
shortest residual source-to-sink path cannot decrease the finite residual
distance from the source to any vertex. -/
theorem shortest_path_nondec (φ : Flow V G) (p : ShortestAugmentingPath φ)
    {v : V} {d d' : ℕ}
    (hd : IsShortestDist φ G.s v d)
    (hd' : IsShortestDist (φ.augment p.path) G.s v d') :
    d ≤ d' := by
  rcases p.exists_shortestDist_le_augment hd' with ⟨d₀, hd₀, hd₀_le⟩
  have hdist : d = d₀ := hd.unique hd₀
  omega

end Chapter26
end CLRS
