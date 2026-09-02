import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CircuitPrefix

open CLRS Chapter34
open CLRS.Chapter34.Turing.PolyBuilder

#check circuitInputPrefix
#check circuitInputPrefixRevProgram
#check circuitInputPrefixRev_outputs
#check circuitInputPrefixRev_polyBound
#check circuitInputPrefix_computableInPolyTime

example : circuitInputPrefix 3 =
    [.argMark, .argMark, .argMark, .endMark,
      .inputMark, .endMark,
      .inputMark, .argMark, .endMark,
      .inputMark, .argMark, .argMark, .endMark] := by
  native_decide

#print axioms circuitInputPrefix_computableInPolyTime
