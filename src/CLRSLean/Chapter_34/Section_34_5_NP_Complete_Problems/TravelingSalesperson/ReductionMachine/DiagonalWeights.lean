import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.DiagonalFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.RangeCertificate
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-! # Fixed generation of all diagonal HAM-CYCLE to TSP weights -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction

open _root_.Turing

def diagonalWeightFields (I : CliqueInstance) : List TSPSym :=
  encodeTSPFields (List.replicate I.vertexCount 2)

noncomputable def diagonalWeightFieldsComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id diagonalWeightFields := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    VertexCover.ComplementMachine.PairStream.RangeCertificate.computableInPolyTime
    DiagonalFields.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, DiagonalFields.fields,
          diagonalWeightFields] using output }

end CLRS.Chapter34.Turing.TSPReduction
