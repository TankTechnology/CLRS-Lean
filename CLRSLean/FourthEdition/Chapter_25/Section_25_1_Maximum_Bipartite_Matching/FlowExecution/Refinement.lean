import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Run

/-!
# Matching refinement and the costed §25.1 headline

Every integral state of the costed flow run is refined to a matching of the
same value.  The final state is a maximal flow, so its recovered matching is
maximum; its counters carry the `O(VE)` certificate from the same run.
-/

namespace CLRS
namespace Matchings

open Finset Classical
open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Matching recovered from the integral flow stored after `n` costed
augmentation attempts. -/
noncomputable def flowMatchingAt (G : BipartiteGraph V) (n : ℕ) : Matching V G :=
  matchingOfIntegralFlow (costedFlowRun G n).flow (costedFlowRun_integral G n)

/-- At every index, the recovered matching size is exactly the flow value. -/
theorem flowMatchingAt_size (G : BipartiteGraph V) (n : ℕ) :
    ((flowMatchingAt G n).size : ℝ) = (costedFlowRun G n).flow.value := by
  exact matchingOfIntegralFlow_size _ _

/-- Every successful BFS augmentation strictly grows the recovered matching
size (in fact by at least one). -/
theorem flowMatchingAt_size_increase (G : BipartiteGraph V) (n : ℕ)
    (h : (costedFlowRun G n).flow.hasAugmentingPath) :
    (flowMatchingAt G n).size + 1 ≤ (flowMatchingAt G (n + 1)).size := by
  have hinc := bfsFlowStep_value_ge_one G (costedFlowRun G n).flow
    (costedFlowRun_integral G n) h
  have hstep : (costedFlowRun G (n + 1)).flow =
      bfsFlowStep G (costedFlowRun G n).flow := by
    simp [costedFlowRun]
  rw [← hstep, ← flowMatchingAt_size G n, ← flowMatchingAt_size G (n + 1)] at hinc
  exact_mod_cast hinc

/-- The matching recovered after `|L|` attempts is maximum. -/
theorem flowMatchingAt_maximum (G : BipartiteGraph V) :
    (flowMatchingAt G G.L.card).IsMaximum := by
  intro M'
  have hle := costedFlowRun_maximal G (matchingToFlow M')
  rw [matchingToFlow_value, ← flowMatchingAt_size G G.L.card] at hle
  exact_mod_cast hle

/-- **Costed bipartite-flow method (CLRS §25.1).**  One concrete BFS
augmentation run returns a maximum matching and a maximal integral flow of
the same value.  The same run records at most `|V|` augmentations and total
adjacency-list work bounded by `|V| · 4(E_flow + 1)`.

Since `E_flow = |V| + |G.E|`, this is the textbook `O(VE)` bound for the
constructed unit-capacity flow network. -/
theorem flowMethod_finds_maximum_matching_in_OVE (G : BipartiteGraph V) :
    let run := costedFlowRun G G.L.card
    let M := flowMatchingAt G G.L.card
    M.IsMaximum ∧
      run.flow.isMaximal ∧
      run.flow.IsIntegral ∧
      run.flow.value = (M.size : ℝ) ∧
      run.augmentations ≤ Fintype.card V ∧
      run.work ≤ Fintype.card V * (4 * (flowArcCount G + 1)) := by
  dsimp only
  exact ⟨flowMatchingAt_maximum G,
    costedFlowRun_maximal G,
    costedFlowRun_integral G G.L.card,
    (flowMatchingAt_size G G.L.card).symm,
    costedFlowRun_augmentations_le_vertex_card G,
    costedFlowRun_work_le_OVE G⟩

end Matchings
end CLRS
