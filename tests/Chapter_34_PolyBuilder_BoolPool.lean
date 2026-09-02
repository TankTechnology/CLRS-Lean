import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPool

open CLRS Chapter34
open CLRS.Chapter34.Turing.PolyBuilder

#check boolPoolGateStream
#check appendBoolPoolProgram
#check appendBoolPool_outputs
#check appendBoolPool_polyBound
#check appendBoolPool_computableInPolyTime

example : appendBoolPool [.argMark, .endMark] =
    [.argMark, .endMark, .constFalseMark, .constTrueMark] := by
  native_decide

#print axioms appendBoolPool_computableInPolyTime
