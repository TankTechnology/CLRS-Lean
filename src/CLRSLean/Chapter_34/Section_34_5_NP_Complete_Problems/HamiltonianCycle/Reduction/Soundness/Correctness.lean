import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.SelectorBudget

/-!
# Soundness of VERTEX-COVER to HAM-CYCLE

The selected source vertices extracted from a Hamiltonian cycle form a cover,
and the selector-slot injection bounds their cardinality by the source target.
The total reduction's two degenerate branches are then discharged directly.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem clrsHamiltonianInstance_hasVertexCover_of_hasHamiltonianCycle
    {I : VertexCoverInstance} (hwellFormed : I.WellFormed)
    (htarget : 0 < I.targetSize)
    (hcycle : (clrsHamiltonianInstance I).HasHamiltonianCycle) :
    I.HasVertexCover := by
  rcases hcycle with ⟨vertices, hvertices⟩
  exact ⟨cycleSelectedSourceVertices I vertices,
    cycleSelectedSourceVertices_card_le_targetSize hvertices htarget,
    cycleSelectedSourceVertices_isVertexCover
      hwellFormed hvertices htarget⟩

theorem hasVertexCover_of_edges_eq_nil
    {I : VertexCoverInstance} (hedges : I.edges = []) :
    I.HasVertexCover := by
  refine ⟨∅, by simp, ?_⟩
  constructor
  · simp
  · intro edge hedge
    rw [hedges] at hedge
    simp at hedge

/-! Soundness direction of the total typed CLRS reduction. -/
theorem vertexCoverToHamiltonianInstance_sound
    {I : VertexCoverInstance} (hwellFormed : I.WellFormed) :
    (vertexCoverToHamiltonianInstance I).HasHamiltonianCycle →
      I.HasVertexCover := by
  intro hcycle
  by_cases hedges : I.edges = []
  · exact hasVertexCover_of_edges_eq_nil hedges
  · by_cases htarget : I.targetSize = 0
    · rw [vertexCoverToHamiltonianInstance, if_neg hedges,
        if_pos htarget] at hcycle
      exact (not_canonicalHamiltonianNoInstance_hasHamiltonianCycle
        hcycle).elim
    · rw [vertexCoverToHamiltonianInstance, if_neg hedges,
        if_neg htarget] at hcycle
      exact clrsHamiltonianInstance_hasVertexCover_of_hasHamiltonianCycle
        hwellFormed (Nat.pos_of_ne_zero htarget) hcycle

end CLRS.Chapter34.HamiltonianCycleReduction
