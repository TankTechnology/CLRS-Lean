import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.TypedTotal.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Ordinary.Semantics

/-!
# VERTEX-COVER to HAM-CYCLE: total typed semantic bridge
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.TypedTotal

open HamiltonianCycleReduction

/-- The machine-order target and textbook-order target have identical
Hamiltonian-cycle semantics in every branch. -/
theorem hasHamiltonianCycle_iff (I : VertexCoverInstance) :
    (machineInstance I).HasHamiltonianCycle ↔
      (vertexCoverToHamiltonianInstance I).HasHamiltonianCycle := by
  by_cases hedges : I.edges = []
  · simp [machineInstance, branch, vertexCoverToHamiltonianInstance, hedges]
  · by_cases htarget : I.targetSize = 0
    · simp [machineInstance, branch, vertexCoverToHamiltonianInstance, hedges,
        htarget]
    · simp only [machineInstance, branch, vertexCoverToHamiltonianInstance, hedges,
        htarget, if_false]
      exact Ordinary.hasHamiltonianCycle_iff I

theorem instance_wellFormed (I : VertexCoverInstance) :
    (machineInstance I).WellFormed := by
  by_cases hedges : I.edges = []
  · simp [machineInstance, branch, hedges,
      canonicalHamiltonianYesInstance_wellFormed]
  · by_cases htarget : I.targetSize = 0
    · simp [machineInstance, branch, hedges, htarget,
        canonicalHamiltonianNoInstance_wellFormed]
    · simp [machineInstance, branch, hedges, htarget,
        Ordinary.machineClrsInstance_wellFormed]

/-- Every selected target is encoded as a genuine HAM-CYCLE instance rather
than as a more general graph-plus-cardinality query. -/
theorem machineInstance_targetSize_eq_vertexCount (I : VertexCoverInstance) :
    (machineInstance I).targetSize = (machineInstance I).vertexCount := by
  by_cases hedges : I.edges = []
  · simp [machineInstance, branch, hedges,
      canonicalHamiltonianYesInstance]
  · by_cases htarget : I.targetSize = 0
    · simp [machineInstance, branch, hedges, htarget,
        canonicalHamiltonianNoInstance]
    · simp [machineInstance, branch, hedges, htarget,
        Ordinary.machineClrsInstance]

/-- Typed textbook correctness transferred to the exact machine edge order. -/
theorem correct {I : VertexCoverInstance} (hwellFormed : I.WellFormed) :
    I.HasVertexCover ↔ (machineInstance I).HasHamiltonianCycle := by
  rw [hasHamiltonianCycle_iff]
  exact vertexCoverToHamiltonianInstance_correct hwellFormed

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.TypedTotal
