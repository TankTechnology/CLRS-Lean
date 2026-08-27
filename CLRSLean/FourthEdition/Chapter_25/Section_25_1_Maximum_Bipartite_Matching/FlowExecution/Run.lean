import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Step

/-!
# The costed §25.1 flow run

The flow, number of successful augmentations, and adjacency-list work are
advanced together.  This prevents the complexity statement from drifting
away from the execution that returns the final flow.
-/

namespace CLRS
namespace Matchings

open Finset Classical
open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- State returned by a fixed number of costed BFS augmentation attempts. -/
structure CostedFlowRun (G : BipartiteGraph V) where
  /-- Current feasible flow. -/
  flow : Flow (V ⊕ Bool) (toFlowNetwork V G)
  /-- Number of attempts whose input flow admitted an augmenting path. -/
  augmentations : ℕ
  /-- Accumulated adjacency-list work. -/
  work : ℕ

/-- Run `n` BFS augmentation attempts from the zero flow, accumulating the
work and successful-augmentation counters in the same recursion. -/
noncomputable def costedFlowRun (G : BipartiteGraph V) : ℕ → CostedFlowRun G
  | 0 =>
      { flow := zeroFlow (toFlowNetwork V G)
        augmentations := 0
        work := 0 }
  | n + 1 =>
      let previous := costedFlowRun G n
      { flow := bfsFlowStep G previous.flow
        augmentations := previous.augmentations +
          if previous.flow.hasAugmentingPath then 1 else 0
        work := previous.work + augmentationAttemptWork G }

/-- Erasing counters from the costed run gives the BFS flow iteration. -/
theorem costedFlowRun_flow (G : BipartiteGraph V) :
    ∀ n, (costedFlowRun G n).flow = bfsFlowIter G n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [costedFlowRun]
      rw [ih]
      rfl

/-- The work field is exactly the sum of the per-attempt charges. -/
theorem costedFlowRun_work (G : BipartiteGraph V) :
    ∀ n, (costedFlowRun G n).work = n * augmentationAttemptWork G := by
  intro n
  induction n with
  | zero => simp [costedFlowRun]
  | succ n ih =>
      simp only [costedFlowRun]
      rw [ih, Nat.succ_mul]

/-- There is at most one successful augmentation per attempted step. -/
theorem costedFlowRun_augmentations_le (G : BipartiteGraph V) :
    ∀ n, (costedFlowRun G n).augmentations ≤ n := by
  intro n
  induction n with
  | zero => simp [costedFlowRun]
  | succ n ih =>
      simp only [costedFlowRun]
      split_ifs <;> omega

/-- Every flow stored by the costed run is integral. -/
theorem costedFlowRun_integral (G : BipartiteGraph V) (n : ℕ) :
    (costedFlowRun G n).flow.IsIntegral := by
  rw [costedFlowRun_flow]
  exact bfsFlowIter_integral G n

/-- After `|L|` BFS attempts the unit-capacity flow has no augmenting path.

If the final flow still had a path, stability would imply that all earlier
flows had paths.  Their integral values would therefore reach at least
`|L|`, and one more active step would exceed the source cut of capacity
`|L|`. -/
theorem bfsFlowIter_noAugmentingPath_left_card (G : BipartiteGraph V) :
    ¬ (bfsFlowIter G G.L.card).hasAugmentingPath := by
  intro hfinal
  have hprefix : ∀ i < G.L.card, (bfsFlowIter G i).hasAugmentingPath := by
    intro i hi
    exact bfsFlowIter_hasAugmentingPath_of_le G (by omega) hfinal
  have hge := bfsFlowIter_value_ge_of_prefix G G.L.card hprefix
  have hinc := bfsFlowStep_value_ge_one G (bfsFlowIter G G.L.card)
    (bfsFlowIter_integral G G.L.card) hfinal
  have hle := bfsFlowIter_value_le_left_card G (G.L.card + 1)
  have hnext : bfsFlowIter G (G.L.card + 1) =
      bfsFlowStep G (bfsFlowIter G G.L.card) := rfl
  rw [hnext] at hle
  linarith

/-- The flow returned after `|L|` attempts is maximal. -/
theorem costedFlowRun_maximal (G : BipartiteGraph V) :
    (costedFlowRun G G.L.card).flow.isMaximal := by
  apply Flow.maximal_of_noAugmentingPath
  rw [costedFlowRun_flow]
  exact bfsFlowIter_noAugmentingPath_left_card G

/-- The successful-augmentation count of the textbook run is at most `|V|`. -/
theorem costedFlowRun_augmentations_le_vertex_card (G : BipartiteGraph V) :
    (costedFlowRun G G.L.card).augmentations ≤ Fintype.card V := by
  exact (costedFlowRun_augmentations_le G G.L.card).trans
    (left_card_le_vertex_card G)

/-- Exact `O(VE)` arithmetic bound for the costed run, where `E` is the
support-arc count of the constructed flow network. -/
theorem costedFlowRun_work_le_OVE (G : BipartiteGraph V) :
    (costedFlowRun G G.L.card).work ≤
      Fintype.card V * (4 * (flowArcCount G + 1)) := by
  rw [costedFlowRun_work]
  exact (Nat.mul_le_mul (left_card_le_vertex_card G)
    (augmentationAttemptWork_le G))

end Matchings
end CLRS
