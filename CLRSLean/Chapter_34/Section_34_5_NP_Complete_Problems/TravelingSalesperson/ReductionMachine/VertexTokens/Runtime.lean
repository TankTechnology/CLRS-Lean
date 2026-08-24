import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.VertexTokens.Basic

/-! # Fixed vertex-token extractor -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.VertexTokens

open PolyBuilder
open _root_.Turing

private noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime id id stream := by
  change TM2ComputableInPolyTime id id
    (fun input : List CliqueSym => input.flatMap body.emit)
  exact boundedLoop_computableInPolyTime body

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueCertificate id tokens := by
  let raw := streamComputableInPolyTime
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun vertices => by
        have output := raw.outputsFun (encodeCliqueCertificate vertices)
        simpa [stream_encodeCliqueCertificate] using output }

end CLRS.Chapter34.Turing.TSPReduction.VertexTokens
