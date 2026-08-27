import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Model

/-!
# BFS-selected unit-capacity augmentation

This module defines the flow iteration used by the executable §25.1 algorithm.
Unlike the abstract existence-level loop, an active step augments along the
shortest path reconstructed by the executable residual BFS.
-/

namespace CLRS
namespace Matchings

open Finset Classical
open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One BFS-selected augmentation step in the bipartite flow network. -/
noncomputable def bfsFlowStep (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) :
    Flow (V ⊕ Bool) (toFlowNetwork V G) :=
  if h : φ.hasAugmentingPath then
    φ.augment (bfs_shortestAugmenting φ h).path
  else φ

theorem bfsFlowStep_of_hasAugmentingPath (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (h : φ.hasAugmentingPath) :
    bfsFlowStep G φ = φ.augment (bfs_shortestAugmenting φ h).path := by
  simp [bfsFlowStep, h]

theorem bfsFlowStep_of_noAugmentingPath (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (h : ¬ φ.hasAugmentingPath) :
    bfsFlowStep G φ = φ := by
  simp [bfsFlowStep, h]

/-- The BFS step preserves integrality on the unit-capacity network. -/
theorem bfsFlowStep_integral (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (hint : φ.IsIntegral) :
    (bfsFlowStep G φ).IsIntegral := by
  by_cases h : φ.hasAugmentingPath
  · rw [bfsFlowStep_of_hasAugmentingPath G φ h]
    exact IsIntegral_augment φ hint toFlowNetwork_integral_capacity _
  · rw [bfsFlowStep_of_noAugmentingPath G φ h]
    exact hint

/-- An active BFS step increases the integral flow value by at least one. -/
theorem bfsFlowStep_value_ge_one (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (hint : φ.IsIntegral)
    (h : φ.hasAugmentingPath) :
    φ.value + 1 ≤ (bfsFlowStep G φ).value := by
  rw [bfsFlowStep_of_hasAugmentingPath G φ h]
  exact augment_value_ge_one φ hint toFlowNetwork_integral_capacity _

/-- Iterate the BFS step from an arbitrary starting flow. -/
noncomputable def bfsFlowIterFrom (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) : ℕ →
    Flow (V ⊕ Bool) (toFlowNetwork V G)
  | 0 => φ
  | n + 1 => bfsFlowStep G (bfsFlowIterFrom G φ n)

/-- The §25.1 flow iteration starts from the zero flow. -/
noncomputable def bfsFlowIter (G : BipartiteGraph V) (n : ℕ) :
    Flow (V ⊕ Bool) (toFlowNetwork V G) :=
  bfsFlowIterFrom G (zeroFlow (toFlowNetwork V G)) n

@[simp]
theorem bfsFlowIterFrom_zero (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) :
    bfsFlowIterFrom G φ 0 = φ := rfl

@[simp]
theorem bfsFlowIterFrom_succ (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (n : ℕ) :
    bfsFlowIterFrom G φ (n + 1) = bfsFlowStep G (bfsFlowIterFrom G φ n) := rfl

/-- Iteration composes over addition of step counts. -/
theorem bfsFlowIterFrom_add (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G)) (m n : ℕ) :
    bfsFlowIterFrom G φ (m + n) =
      bfsFlowIterFrom G (bfsFlowIterFrom G φ m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, bfsFlowIterFrom_succ, bfsFlowIterFrom_succ, ih]

/-- Once no augmenting path exists, every later iterate is the same flow. -/
theorem bfsFlowIterFrom_eq_of_noAugmentingPath (G : BipartiteGraph V)
    (φ : Flow (V ⊕ Bool) (toFlowNetwork V G))
    (h : ¬ φ.hasAugmentingPath) :
    ∀ n, bfsFlowIterFrom G φ n = φ := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [bfsFlowIterFrom_succ, ih, bfsFlowStep_of_noAugmentingPath G φ h]

/-- A later augmenting path implies that all earlier iterates also had one. -/
theorem bfsFlowIter_hasAugmentingPath_of_le (G : BipartiteGraph V)
    {i j : ℕ} (hij : i ≤ j)
    (hj : (bfsFlowIter G j).hasAugmentingPath) :
    (bfsFlowIter G i).hasAugmentingPath := by
  by_contra hi
  have hji : j = i + (j - i) := by omega
  have hstable := bfsFlowIterFrom_eq_of_noAugmentingPath G (bfsFlowIter G i) hi (j - i)
  have heq : bfsFlowIter G j = bfsFlowIter G i := by
    unfold bfsFlowIter
    rw [hji, bfsFlowIterFrom_add]
    change bfsFlowIterFrom G (bfsFlowIter G i) (j - i) = bfsFlowIter G i
    exact hstable
  rw [heq] at hj
  exact hi hj

/-- Every iterate from the zero flow is integral. -/
theorem bfsFlowIter_integral (G : BipartiteGraph V) :
    ∀ n, (bfsFlowIter G n).IsIntegral := by
  intro n
  induction n with
  | zero =>
      exact IsIntegral_zero
  | succ n ih =>
      simpa [bfsFlowIter, bfsFlowIterFrom] using bfsFlowStep_integral G _ ih

/-- The source cut of the constructed network has capacity exactly `|L|`. -/
theorem matchingNetwork_sourceCut (G : BipartiteGraph V) :
    ∑ v : V ⊕ Bool,
        (toFlowNetwork V G).c (toFlowNetwork V G).s v = (G.L.card : ℝ) := by
  simp [toFlowNetwork, capFunc]

/-- Every iterate is bounded by the source cut. -/
theorem bfsFlowIter_value_le_left_card (G : BipartiteGraph V) (n : ℕ) :
    (bfsFlowIter G n).value ≤ (G.L.card : ℝ) := by
  rw [← matchingNetwork_sourceCut G]
  exact value_le_source_cut (bfsFlowIter G n)

/-- If the first `n` iterates all admit augmentation, the `n`th flow has
value at least `n`. -/
theorem bfsFlowIter_value_ge_of_prefix (G : BipartiteGraph V) (n : ℕ)
    (hsteps : ∀ i < n, (bfsFlowIter G i).hasAugmentingPath) :
    (n : ℝ) ≤ (bfsFlowIter G n).value := by
  induction n with
  | zero => simp [bfsFlowIter, bfsFlowIterFrom, zeroFlow, Flow.value]
  | succ n ih =>
      have hn : (bfsFlowIter G n).hasAugmentingPath := hsteps n (by omega)
      have hprefix : ∀ i < n, (bfsFlowIter G i).hasAugmentingPath :=
        fun i hi => hsteps i (by omega)
      have hge := ih hprefix
      have hinc := bfsFlowStep_value_ge_one G (bfsFlowIter G n)
        (bfsFlowIter_integral G n) hn
      have hnext : bfsFlowIter G (n + 1) = bfsFlowStep G (bfsFlowIter G n) := rfl
      rw [hnext]
      push_cast
      linarith

end Matchings
end CLRS
