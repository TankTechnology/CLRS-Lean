import Mathlib
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S1_ShortestAugmentingPath
import CLRSLean.FourthEdition.Chapter_24.Section_24_3_Bipartite_Matching

/-!
# 24.2 S2. The Edmonds-Karp loop

This module implements the Edmonds-Karp algorithm: repeatedly augment along a
shortest residual source-to-sink path until none exists.  Shortest paths come
from `exists_shortest_augmenting_path` (S1); integrality and the termination
argument reuse the infrastructure of Section 24.3 (`Flow.IsIntegral`,
`bottleneck_ge_one`, `IsIntegral_augment`), so each augmentation step
increases the integral value by at least one and the iteration terminates at
a flow without augmenting paths, which is maximal.

Main results:

- `shortestAugmentingPath_iff_hasAugmentingPath`: a shortest augmenting path
  exists exactly when the sink is residual-reachable
- `ekStep`: one Edmonds-Karp augmentation step (along a shortest path)
- `ekIter`: the full loop from a starting flow
- `IsIntegral_ekIter` and `ekStep_value_ge`: integrality and value increase
  are preserved by every step
- `exists_noAugmentingPath_ekIter`: the loop terminates at a flow without
  augmenting paths
- `edmondsKarp_maximal`: the terminal flow is maximal and integral
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- A shortest augmenting path exists exactly when the sink is
residual-reachable. -/
lemma shortestAugmentingPath_iff_hasAugmentingPath (φ : Flow V G) :
    Nonempty (ShortestAugmentingPath φ) ↔ φ.hasAugmentingPath := by
  constructor
  · intro ⟨p⟩
    exact Flow.hasAugmentingPath_iff_nonempty_augmentingPath.mpr ⟨p.path⟩
  · intro h
    exact exists_shortest_augmenting_path φ h

/-- One Edmonds-Karp step: augment along a shortest residual source-to-sink
path if one exists. -/
noncomputable def ekStep {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : Flow V G :=
  if h : Nonempty (ShortestAugmentingPath φ) then
    φ.augment (Classical.choice h).path
  else φ

/-- `ekStep` preserves integrality. -/
lemma IsIntegral_ekStep {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) :
    (ekStep φ).IsIntegral := by
  unfold ekStep
  by_cases h : Nonempty (ShortestAugmentingPath φ)
  · simp [h]
    exact IsIntegral_augment φ hint hc (Classical.choice h).path
  · simp [h]
    exact hint

/-- One Edmonds-Karp step along a shortest path increases the integral value
by at least one. -/
lemma ekStep_value_increase {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (h : Nonempty (ShortestAugmentingPath φ)) :
    φ.value + 1 ≤ (ekStep φ).value := by
  unfold ekStep
  simp [h]
  exact augment_value_ge_one φ hint hc (Classical.choice h).path

/-- Repeatedly apply Edmonds-Karp steps from a starting flow. -/
noncomputable def ekIter {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : ℕ → Flow V G
  | 0 => φ
  | n + 1 => ekStep (ekIter φ n)

/-- Every iterate of `ekIter` is integral. -/
lemma IsIntegral_ekIter {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) :
    ∀ n, (ekIter φ n).IsIntegral := by
  intro n
  induction n with
  | zero => simpa [ekIter] using hint
  | succ n ih =>
      simpa [ekIter] using (IsIntegral_ekStep (ekIter φ n) ih hc)

/-- Each Edmonds-Karp step increases the value by at least one, unless the
flow is already free of augmenting paths. -/
lemma ekStep_value_ge {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (n : ℕ) :
    ¬(ekIter φ n).hasAugmentingPath ∨
      (ekIter φ n).value + 1 ≤ (ekIter φ (n + 1)).value := by
  by_cases h : (ekIter φ n).hasAugmentingPath
  · right
    have hshort : Nonempty (ShortestAugmentingPath (ekIter φ n)) :=
      (shortestAugmentingPath_iff_hasAugmentingPath (ekIter φ n)).mpr h
    have hinc := ekStep_value_increase (ekIter φ n) (IsIntegral_ekIter φ hint hc n) hc hshort
    simpa [ekIter] using hinc
  · left
    exact h

/-- While every step finds an augmenting path, the value after `n` steps is
at least `n`. -/
lemma ekIter_value_ge {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (hint : φ.IsIntegral) (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ))
    (hφ : 0 ≤ φ.value) (hsteps : ∀ n, (ekIter φ n).hasAugmentingPath) :
    ∀ n : ℕ, (n : ℝ) ≤ (ekIter φ n).value := by
  intro n
  induction n with
  | zero => simpa [ekIter] using hφ
  | succ n ih =>
      have hinc := (ekStep_value_ge φ hint hc n).resolve_left (not_not_intro (hsteps n))
      push_cast
      linarith

/-- The Edmonds-Karp loop terminates at a flow without augmenting paths: the
value strictly increases by at least one each step and is bounded by the
(integral) source-side cut capacity. -/
lemma exists_noAugmentingPath_ekIter {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (hint : φ.IsIntegral)
    (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) (hφ : 0 ≤ φ.value) :
    ∃ n, ¬ (ekIter φ n).hasAugmentingPath := by
  by_contra hnot
  have hsteps : ∀ n, (ekIter φ n).hasAugmentingPath := by
    intro n
    by_contra h
    exact hnot ⟨n, h⟩
  rcases source_cut_integral hc with ⟨K, hK⟩
  have hge : ((K + 1 : ℕ) : ℝ) ≤ (ekIter φ (K + 1)).value :=
    ekIter_value_ge φ hint hc hφ hsteps (K + 1)
  have hle : (ekIter φ (K + 1)).value ≤ (K : ℝ) := by
    rw [← hK]
    exact value_le_source_cut (ekIter φ (K + 1))
  have hle' : ((K + 1 : ℕ) : ℝ) ≤ (K : ℝ) := le_trans hge hle
  norm_num at hle'

/-- **Edmonds-Karp correctness.**  On an integral-capacity network, the
Edmonds-Karp loop reaches an integral maximal flow. -/
theorem edmondsKarp_maximal {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (hc : ∀ u v, ∃ n : ℕ, G.c u v = (n : ℝ)) :
    ∃ φ : Flow V G, φ.isMaximal ∧ φ.IsIntegral := by
  let zf : Flow V G := zeroFlow G
  have hz : 0 ≤ zf.value := by
    unfold Flow.value
    simp [zf, zeroFlow]
  rcases exists_noAugmentingPath_ekIter zf (IsIntegral_zero (G := G)) hc hz with
    ⟨n, hn⟩
  let φ : Flow V G := ekIter zf n
  refine ⟨φ, ?_, ?_⟩
  · exact Flow.maximal_of_noAugmentingPath φ hn
  · exact IsIntegral_ekIter zf (IsIntegral_zero (G := G)) hc n

end Chapter26
end CLRS
