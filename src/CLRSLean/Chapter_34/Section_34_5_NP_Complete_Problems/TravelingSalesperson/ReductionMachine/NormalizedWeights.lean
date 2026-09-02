import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.WeightFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Answers

/-!
# HAM-CYCLE to TSP machine: normalized-pair weights

This stage deliberately reuses the complete-pair source and batched graph
lookup already verified for the VERTEX-COVER complement machine.  It computes
one canonical `1`/`2` TSP field for every normalized pair of source vertices.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction

open _root_.Turing

/-- Semantic textbook weights in the shared normalized-pair order. -/
def normalizedPairWeights (I : CliqueInstance) : List Nat :=
  (VertexCover.ComplementMachine.NonedgeFilter.candidatePairs I).map fun edge =>
    if edge ∈ I.edges then 1 else 2

/-- Canonical compact fields for all normalized-pair weights. -/
def normalizedWeightFields (I : CliqueInstance) : List TSPSym :=
  encodeTSPFields (normalizedPairWeights I)

theorem membershipBits_map_answerWeight (I : CliqueInstance) :
    (VertexCover.ComplementMachine.NonedgeFilter.membershipBits I).map
        WeightFields.answerWeight =
      normalizedPairWeights I := by
  simp only [VertexCover.ComplementMachine.NonedgeFilter.membershipBits,
    GeneralCliqueVerifier.BatchEdgeLookup.queryMembershipBits,
    VertexCover.ComplementMachine.NonedgeFilter.candidatePairs,
    normalizedPairWeights, List.map_map]
  apply List.map_congr_left
  intro edge hedge
  by_cases hmem : edge ∈ I.edges <;>
    simp [hmem, WeightFields.answerWeight]

theorem weightFields_membershipBits (I : CliqueInstance) :
    WeightFields.stream
        (VertexCover.ComplementMachine.NonedgeFilter.membershipBits I) =
      normalizedWeightFields I := by
  rw [WeightFields.stream, ← List.flatMap_map]
  simp only [membershipBits_map_answerWeight, normalizedWeightFields,
    encodeTSPFields]

/-- A fixed polynomial-time TM2 maps a canonical graph encoding to all
normalized textbook weight fields. -/
noncomputable def normalizedWeightFieldsComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id normalizedWeightFields := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    VertexCover.ComplementMachine.NonedgeFilter.membershipBitsComputableInPolyTime
    WeightFields.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, weightFields_membershipBits] using output }

end CLRS.Chapter34.Turing.TSPReduction
