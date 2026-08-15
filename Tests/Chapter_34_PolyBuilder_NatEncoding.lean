import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding

namespace CLRS.Chapter34.Turing.PolyBuilder

#check lengthEncodingProgram
#check lengthEncodingSteps
#check lengthEncoding_run
#check lengthEncoding_outputs
#check lengthEncoding_polyBound
#check lengthEncoding_computableInPolyTime
#check circuitIndexStream
#check circuitIndexStream_eq_map
#check circuitIndexStream_computableInPolyTime

example : circuitIndexStream 3 =
    [.endMark, .argMark, .endMark,
      .argMark, .argMark, .endMark] := by
  native_decide

end CLRS.Chapter34.Turing.PolyBuilder
