import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Run

/-!
# Matching refinement and the executable §25.1 headline

Every integral state of the costed flow run is refined to a matching of the
same value.  The final state is a maximal flow, so its recovered matching is
maximum.  The executable run also bounds the number of augmentations; an
attached adjacency-list work theorem is supplied by the sibling `CostedRun`
module, while this file remains the semantic flow reference.
-/

namespace CLRS
namespace Matchings

open Finset Classical
open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Matching recovered from the integral flow stored after `n`
augmentation attempts. -/
noncomputable def flowMatchingAt (G : BipartiteGraph V) (n : ℕ) : Matching V G :=
  matchingOfIntegralFlow (flowRun G n).flow (flowRun_integral G n)

/-- At every index, the recovered matching size is exactly the flow value. -/
theorem flowMatchingAt_size (G : BipartiteGraph V) (n : ℕ) :
    ((flowMatchingAt G n).size : ℝ) = (flowRun G n).flow.value := by
  exact matchingOfIntegralFlow_size _ _

/-- Every successful BFS augmentation strictly grows the recovered matching
size (in fact by at least one). -/
theorem flowMatchingAt_size_increase (G : BipartiteGraph V) (n : ℕ)
    (h : (flowRun G n).flow.hasAugmentingPath) :
    (flowMatchingAt G n).size + 1 ≤ (flowMatchingAt G (n + 1)).size := by
  have hinc := bfsFlowStep_value_ge_one G (flowRun G n).flow
    (flowRun_integral G n) h
  have hstep : (flowRun G (n + 1)).flow =
      bfsFlowStep G (flowRun G n).flow := by
    simp [flowRun]
  rw [← hstep, ← flowMatchingAt_size G n, ← flowMatchingAt_size G (n + 1)] at hinc
  exact_mod_cast hinc

/-- The matching recovered after `|L|` attempts is maximum. -/
theorem flowMatchingAt_maximum (G : BipartiteGraph V) :
    (flowMatchingAt G G.L.card).IsMaximum := by
  intro M'
  have hle := flowRun_maximal G (matchingToFlow M')
  rw [matchingToFlow_value, ← flowMatchingAt_size G G.L.card] at hle
  exact_mod_cast hle

/-- **Executable bipartite-flow method (CLRS §25.1).**  One concrete BFS
augmentation run returns a maximum matching and a maximal integral flow of
the same value and records at most `|V|` augmentations. -/
theorem flowMethod_finds_maximum_matching_with_bfs (G : BipartiteGraph V) :
    let run := flowRun G G.L.card
    let M := flowMatchingAt G G.L.card
    M.IsMaximum ∧
      run.flow.isMaximal ∧
      run.flow.IsIntegral ∧
      run.flow.value = (M.size : ℝ) ∧
      run.augmentations ≤ Fintype.card V := by
  dsimp only
  exact ⟨flowMatchingAt_maximum G,
    flowRun_maximal G,
    flowRun_integral G G.L.card,
    (flowMatchingAt_size G G.L.card).symm,
    flowRun_augmentations_le_vertex_card G⟩

end Matchings
end CLRS
