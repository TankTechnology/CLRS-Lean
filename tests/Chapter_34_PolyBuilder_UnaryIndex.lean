import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex

namespace CLRS.Chapter34.Turing.PolyBuilder

#check unaryIndexCode
#check unaryIndexStream
#check unaryIndexRevProgram
#check unaryIndexRevSteps
#check unaryIndexRev_run
#check unaryIndexRev_outputs
#check unaryIndexRev_polyBound
#check unaryIndexRev_computableInPolyTime
#check unaryIndexStream_computableInPolyTime

example : unaryIndexStream 3 =
    [false, true, false, true, true, false] := by
  native_decide

end CLRS.Chapter34.Turing.PolyBuilder
