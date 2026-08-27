import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Step

/-!
# The §25.1 BFS-selected flow run

The flow and number of successful augmentations are advanced together.  The
current Chapter 24 residual BFS enumerates all finite vertices; consequently
this module makes no adjacency-list `O(VE)` claim.
-/

namespace CLRS
namespace Matchings

open Finset Classical
open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- State returned by a fixed number of BFS augmentation attempts. -/
structure FlowRun (G : BipartiteGraph V) where
  /-- Current feasible flow. -/
  flow : Flow (V ⊕ Bool) (toFlowNetwork V G)
  /-- Number of attempts whose input flow admitted an augmenting path. -/
  augmentations : ℕ

/-- Run `n` BFS augmentation attempts from the zero flow, accumulating the
successful-augmentation counter in the same recursion. -/
noncomputable def flowRun (G : BipartiteGraph V) : ℕ → FlowRun G
  | 0 =>
      { flow := zeroFlow (toFlowNetwork V G)
        augmentations := 0 }
  | n + 1 =>
      let previous := flowRun G n
      { flow := bfsFlowStep G previous.flow
        augmentations := previous.augmentations +
          if previous.flow.hasAugmentingPath then 1 else 0 }

/-- Erasing the augmentation counter gives the BFS flow iteration. -/
theorem flowRun_flow (G : BipartiteGraph V) :
    ∀ n, (flowRun G n).flow = bfsFlowIter G n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [flowRun]
      rw [ih]
      rfl

/-- There is at most one successful augmentation per attempted step. -/
theorem flowRun_augmentations_le (G : BipartiteGraph V) :
    ∀ n, (flowRun G n).augmentations ≤ n := by
  intro n
  induction n with
  | zero => simp [flowRun]
  | succ n ih =>
      simp only [flowRun]
      split_ifs <;> omega

/-- Every flow stored by the run is integral. -/
theorem flowRun_integral (G : BipartiteGraph V) (n : ℕ) :
    (flowRun G n).flow.IsIntegral := by
  rw [flowRun_flow]
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
theorem flowRun_maximal (G : BipartiteGraph V) :
    (flowRun G G.L.card).flow.isMaximal := by
  apply Flow.maximal_of_noAugmentingPath
  rw [flowRun_flow]
  exact bfsFlowIter_noAugmentingPath_left_card G

/-- The successful-augmentation count of the textbook run is at most `|V|`. -/
theorem flowRun_augmentations_le_vertex_card (G : BipartiteGraph V) :
    (flowRun G G.L.card).augmentations ≤ Fintype.card V := by
  exact (flowRun_augmentations_le G G.L.card).trans
    (left_card_le_vertex_card G)

end Matchings
end CLRS
