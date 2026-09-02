import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.SymmetricWeightFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.NormalizedWeights

/-!
# HAM-CYCLE to TSP machine: both orientations of normalized weights
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction

open _root_.Turing

def symmetricWeightFields (I : CliqueInstance) : List TSPSym :=
  encodeTSPFields ((normalizedPairWeights I).flatMap
    fun weight => [weight, weight])

theorem symmetricWeightFields_membershipBits (I : CliqueInstance) :
    SymmetricWeightFields.stream
        (VertexCover.ComplementMachine.NonedgeFilter.membershipBits I) =
      symmetricWeightFields I := by
  rw [SymmetricWeightFields.stream_eq_encoded_duplicate_weights,
    membershipBits_map_answerWeight]
  rfl

noncomputable def symmetricWeightFieldsComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id symmetricWeightFields := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    VertexCover.ComplementMachine.NonedgeFilter.membershipBitsComputableInPolyTime
    SymmetricWeightFields.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, symmetricWeightFields_membershipBits] using
          output }

end CLRS.Chapter34.Turing.TSPReduction
