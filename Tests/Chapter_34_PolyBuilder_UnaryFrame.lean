import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

open CLRS.Chapter34.Turing.PolyBuilder

#check UnaryFrameSym
#check encodeUnaryFrame
#check decodeUnaryFrame
#check decodeUnaryFrame_encode
#check encodeUnaryFrame_length
#check encodeUnaryFrame_injective

#print axioms decodeUnaryFrame_encode
#print axioms encodeUnaryFrame_length
#print axioms encodeUnaryFrame_injective

example : encodeUnaryFrame [2, 0, 1] =
    [.tick, .tick, .separator, .separator, .tick, .separator] := by
  decide

example : decodeUnaryFrame (encodeUnaryFrame [2, 0, 1]) =
    some [2, 0, 1] := by
  simp
