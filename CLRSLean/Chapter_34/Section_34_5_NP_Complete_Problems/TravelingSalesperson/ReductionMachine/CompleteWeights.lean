import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.Codec
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.DiagonalWeights
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.SymmetricWeights
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.WeightSemantics

/-! # Fixed generation of the complete HAM-CYCLE to TSP weight table -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction

open _root_.Turing
open PolyBuilder

def completeWeightFields (I : CliqueInstance) : List TSPSym :=
  diagonalWeightFields I ++ symmetricWeightFields I

theorem completeWeightFields_eq (I : CliqueInstance) :
    completeWeightFields I = encodeTSPFields
      (CLRS.Chapter34.TSPReduction.hamiltonianWeights I) := by
  rw [← completeHamiltonianWeights_eq]
  simp [completeWeightFields, diagonalWeightFields, symmetricWeightFields,
    completeHamiltonianWeights, encodeTSPFields, List.flatMap_append]

noncomputable def completeWeightFieldsComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id completeWeightFields := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeTSPSymPair decodeTSPSymPair decode_encodeTSPSymPair
    diagonalWeightFieldsComputableInPolyTime
    symmetricWeightFieldsComputableInPolyTime

end CLRS.Chapter34.Turing.TSPReduction
