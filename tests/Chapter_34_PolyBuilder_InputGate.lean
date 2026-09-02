import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputGate

open CLRS Chapter34
open CLRS.Chapter34.Turing.PolyBuilder

#check inputGateStream
#check inputGateStream_eq
#check inputGateRevProgram
#check inputGateRev_outputs
#check inputGateRev_polyBound
#check inputGateStream_computableInPolyTime

example : inputGateStream 3 =
    [.inputMark, .endMark,
      .inputMark, .argMark, .endMark,
      .inputMark, .argMark, .argMark, .endMark] := by
  native_decide

#print axioms inputGateStream_computableInPolyTime
