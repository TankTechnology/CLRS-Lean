import Mathlib
import CLRSLean.Chapter_26.Section_26_1_Flow_Networks

/-!
# 26.2. The Edmonds-Karp Algorithm

This section formalizes the Edmonds-Karp monotonic distance lemma
(CLRS Lemma 26.7).

Main results:

- `ResidualPathLength`: inductive predicate for path existence in `G_f`
- `IsShortestDist`: shortest-path distance in `G_f`
- `shortest_path_nondec` (Lemma 26.7): `δ_f(s,v)` is nondecreasing after
  augmenting along a shortest augmenting path
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


structure ShortestAugmentingPath (φ : Flow V G) where
  len : ℕ
  vert : ℕ → V
  h_start : vert 0 = G.s
  h_end : vert len = G.t
  h_edges : ∀ i, i < len → Flow.residualEdge φ (vert i) (vert (i+1))
  h_shortest : IsShortestDist φ G.s G.t len

end Chapter26
end CLRS
