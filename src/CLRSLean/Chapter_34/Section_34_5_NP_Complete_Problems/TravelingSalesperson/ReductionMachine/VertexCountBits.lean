import CLRSLean.Chapter_34.BinaryNat.Machine
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.VertexTokens
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.RangeCertificate

/-! # Fixed binary compilation of the source graph vertex count -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction

open _root_.Turing

def vertexCountTokens (I : CliqueInstance) : List Bool :=
  List.replicate I.vertexCount false

def vertexCountBits (I : CliqueInstance) : List Bool :=
  encodeBinaryNat I.vertexCount

private noncomputable def vertexCountTokensComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id vertexCountTokens := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    VertexCover.ComplementMachine.PairStream.RangeCertificate.computableInPolyTime
    VertexTokens.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, VertexTokens.tokens,
          vertexCountTokens] using output }

noncomputable def vertexCountBitsComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id vertexCountBits := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    vertexCountTokensComputableInPolyTime
    BinaryNat.encoderComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun I => by
        have output := machine.outputsFun I
        simpa [Function.comp_def, vertexCountTokens, vertexCountBits] using
          output }

end CLRS.Chapter34.Turing.TSPReduction
