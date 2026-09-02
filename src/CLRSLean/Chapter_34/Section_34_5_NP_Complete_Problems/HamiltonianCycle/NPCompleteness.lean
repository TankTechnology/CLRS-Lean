import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.NP
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Reduction

/-! # General HAM-CYCLE is NP-complete -/

namespace CLRS.Chapter34

/-- The fixed guarded edge-gadget machine is a polynomial-time many-one
reduction from the honest serialized VERTEX-COVER language to HAM-CYCLE. -/
theorem VERTEXCOVER_reducible_to_HAMCYCLE :
    PolyTimeReducible VERTEXCOVER HAMCYCLE := by
  refine ⟨Turing.HamiltonianCycle.ReductionMachine.RawTotal.machineVertexCoverToHamiltonianMap,
    ⟨Turing.HamiltonianCycle.ReductionMachine.computableInPolyTime⟩, ?_⟩
  intro input
  exact (Turing.HamiltonianCycle.ReductionMachine.RawTotal.machineVertexCoverToHamiltonianMap_mem_HAMCYCLE_iff
    input).symm

/-- The honest serialized HAM-CYCLE language is NP-hard. -/
theorem HAMCYCLE_npHard : NPHard HAMCYCLE :=
  NPHard.of_reducible VERTEXCOVER_npHard
    VERTEXCOVER_reducible_to_HAMCYCLE

/-- The honest serialized HAM-CYCLE language is NP-complete. -/
theorem HAMCYCLE_npComplete : NPComplete HAMCYCLE :=
  ⟨generalHAMCYCLE_polyTimeVerifiable, HAMCYCLE_npHard⟩

end CLRS.Chapter34
