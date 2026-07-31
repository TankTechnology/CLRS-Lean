import Mathlib
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.Ford_Fulkerson_Augmentation

/-!
# 26.2. The Edmonds-Karp Algorithm (partial)

This section currently formalizes the residual-distance infrastructure used by
the Edmonds-Karp analysis.  It does not yet prove the monotonic distance lemma
(CLRS Lemma 26.7).

Main results:

- `ResidualPathLength`: inductive predicate for path existence in `G_f`
- `IsShortestDist`: shortest-path distance in `G_f`
- `isShortestDist_self`: the residual distance from a vertex to itself is zero
- `IsShortestDist.unique`: shortest residual distances are unique
- `isShortestDist_triangle`: one residual edge extends a shortest path by at
  most one step
- `ShortestAugmentingPath`: bundled shortest source-to-sink residual path data

Current gaps:

- Prove the predecessor/prefix and augmentation-edge bridges, then Lemma 26.7.
- Add executable BFS, the Edmonds-Karp augmentation loop, and its `O(VE²)` work
  theorem.
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

end Chapter26
end CLRS
