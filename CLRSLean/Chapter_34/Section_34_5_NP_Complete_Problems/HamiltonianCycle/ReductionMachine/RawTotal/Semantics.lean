import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.RawTotal.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.TypedTotal.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.RawReduction

/-!
# VERTEX-COVER to HAM-CYCLE: guarded raw semantics
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.RawTotal

open HamiltonianCycleReduction
open VertexCover.ComplementMachine

theorem machineMap_of_pass_true {input : List VertexCoverSym}
    (hpass : RawWellFormed.rawWellFormedPass input = true) :
    machineVertexCoverToHamiltonianMap input =
      encodeHamiltonianCycleInstance
        (TypedTotal.machineInstance
          (SyntaxNormalizer.normalizedInstanceValue input)) := by
  simp [machineVertexCoverToHamiltonianMap, selectorData, guardBranch, hpass,
    BranchSelector.selectedOutput, normalizedTarget, TypedTotal.stream_encode]

theorem machineMap_of_pass_false {input : List VertexCoverSym}
    (hpass : RawWellFormed.rawWellFormedPass input = false) :
    machineVertexCoverToHamiltonianMap input =
      encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance := by
  simp [machineVertexCoverToHamiltonianMap, selectorData, guardBranch, hpass,
    BranchSelector.selectedOutput]

/-- Exact language semantics on parser failures, ill-formed decoded sources,
degenerate sources, and ordinary gadget sources. -/
theorem machineVertexCoverToHamiltonianMap_mem_HAMCYCLE_iff
    (input : List VertexCoverSym) :
    machineVertexCoverToHamiltonianMap input ∈
        (HAMCYCLE : Language HamiltonianCycleSym) ↔
      input ∈ (VERTEXCOVER : Language VertexCoverSym) := by
  cases hdecode : decodeVertexCoverInstance input with
  | none =>
      have hnormalized : SyntaxNormalizer.normalizedInstanceValue input =
          SyntaxNormalizer.malformedGraphSentinel :=
        SyntaxNormalizer.normalizedInstanceValue_of_decode_none hdecode
      have hpass : RawWellFormed.rawWellFormedPass input = false := by
        rw [RawWellFormed.rawWellFormedPass_eq_decide]
        simp [hnormalized,
          SyntaxNormalizer.malformedGraphSentinel_not_wellFormed]
      rw [machineMap_of_pass_false hpass]
      exact iff_of_false canonicalHamiltonianNoInstance_not_mem_HAMCYCLE
        (not_mem_generalVERTEXCOVER_of_decode_none hdecode)
  | some I =>
      have hnormalized : SyntaxNormalizer.normalizedInstanceValue input = I :=
        SyntaxNormalizer.normalizedInstanceValue_of_decode_some hdecode
      by_cases hI : I.WellFormed
      · have hpass : RawWellFormed.rawWellFormedPass input = true := by
          rw [RawWellFormed.rawWellFormedPass_eq_decide]
          simp [hnormalized, hI]
        rw [machineMap_of_pass_true hpass, hnormalized,
          encodeHamiltonianCycleInstance_mem_iff]
        rw [and_iff_right (TypedTotal.instance_wellFormed I)]
        rw [and_iff_right
          (TypedTotal.machineInstance_targetSize_eq_vertexCount I)]
        rw [← TypedTotal.correct hI]
        simp [GeneralVERTEXCOVER, hdecode, hI]
      · have hpass : RawWellFormed.rawWellFormedPass input = false := by
          rw [RawWellFormed.rawWellFormedPass_eq_decide]
          simp [hnormalized, hI]
        rw [machineMap_of_pass_false hpass]
        exact iff_of_false canonicalHamiltonianNoInstance_not_mem_HAMCYCLE (by
          simp [GeneralVERTEXCOVER, hdecode, hI])

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.RawTotal
