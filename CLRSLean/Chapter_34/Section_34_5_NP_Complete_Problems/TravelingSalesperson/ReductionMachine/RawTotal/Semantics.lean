import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawTotal.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.RawReduction.Semantics

/-! # Total raw HAM-CYCLE-to-TSP target semantics -/

namespace CLRS.Chapter34.Turing.TSPReduction.RawTotal

open VertexCover.ComplementMachine

/-- The machine-facing guarded formulation is extensionally the public raw
reduction on every input word. -/
theorem machineMap_eq_rawHamiltonianToTSP
    (input : List HamiltonianCycleSym) :
    machineMap input =
      CLRS.Chapter34.TSPReduction.rawHamiltonianToTSP input := by
  cases hdecode : decodeHamiltonianCycleInstance input with
  | none =>
      have hnormalized : SyntaxNormalizer.normalizedInstanceValue input =
          SyntaxNormalizer.malformedGraphSentinel :=
        SyntaxNormalizer.normalizedInstanceValue_of_decode_none hdecode
      have hflag : RawValidity.validPass input = false := by
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        have hvalid := (RawValidity.validPass_eq_true_iff input).1 htrue
        exact SyntaxNormalizer.malformedGraphSentinel_not_wellFormed
          (hnormalized ▸ hvalid.1)
      simp [machineMap, selectorData, RawSelector.selectedOutput, hflag,
        CLRS.Chapter34.TSPReduction.rawHamiltonianToTSP, hdecode]
  | some G =>
      have hnormalized : SyntaxNormalizer.normalizedInstanceValue input = G :=
        SyntaxNormalizer.normalizedInstanceValue_of_decode_some hdecode
      by_cases hvalid : G.WellFormed ∧ G.targetSize = G.vertexCount
      · have hflag : RawValidity.validPass input = true :=
          (RawValidity.validPass_eq_true_iff input).2 (by
            simpa [hnormalized] using hvalid)
        simp [machineMap, selectorData, RawSelector.selectedOutput, hflag,
          normalizedCandidate, hnormalized, Typed.stream_eq,
          CLRS.Chapter34.TSPReduction.rawHamiltonianToTSP, hdecode, hvalid]
      · have hflag : RawValidity.validPass input = false := by
          apply Bool.eq_false_of_not_eq_true
          intro htrue
          apply hvalid
          simpa [hnormalized] using
            (RawValidity.validPass_eq_true_iff input).1 htrue
        simp [machineMap, selectorData, RawSelector.selectedOutput, hflag,
          CLRS.Chapter34.TSPReduction.rawHamiltonianToTSP, hdecode, hvalid]

end CLRS.Chapter34.Turing.TSPReduction.RawTotal
