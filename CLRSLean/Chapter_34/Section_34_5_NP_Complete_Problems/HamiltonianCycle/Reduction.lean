import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness

/-!
# The typed VERTEX-COVER to HAM-CYCLE reduction

This facade exports the total well-formed construction and its bidirectional
typed semantic correctness theorem.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem vertexCoverToHamiltonianInstance_correct
    {I : VertexCoverInstance} (hwellFormed : I.WellFormed) :
    I.HasVertexCover ↔
      (vertexCoverToHamiltonianInstance I).HasHamiltonianCycle :=
  ⟨vertexCoverToHamiltonianInstance_complete hwellFormed,
    vertexCoverToHamiltonianInstance_sound hwellFormed⟩

end CLRS.Chapter34.HamiltonianCycleReduction
