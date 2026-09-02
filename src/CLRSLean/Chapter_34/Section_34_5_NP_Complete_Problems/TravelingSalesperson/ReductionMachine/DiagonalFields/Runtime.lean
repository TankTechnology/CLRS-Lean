import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.DiagonalFields.Basic

/-! # Fixed polynomial-time diagonal TSP field formatter -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.DiagonalFields

open PolyBuilder
open _root_.Turing

private noncomputable def streamComputableInPolyTime :
    TM2ComputableInPolyTime id id stream := by
  change TM2ComputableInPolyTime id id
    (fun input : List CliqueSym => input.flatMap body.emit)
  exact boundedLoop_computableInPolyTime body

/-- A fixed machine maps a canonical typed vertex-list certificate to one
diagonal weight field per vertex. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueCertificate id fields := by
  let raw := streamComputableInPolyTime
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun vertices => by
        have output := raw.outputsFun (encodeCliqueCertificate vertices)
        simpa [stream_encodeCliqueCertificate] using output }

end CLRS.Chapter34.Turing.TSPReduction.DiagonalFields
