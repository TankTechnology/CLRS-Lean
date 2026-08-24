import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListPairEq

noncomputable section

open CLRS Chapter34
open _root_.Turing

example : TM2ComputableInPolyTime
    (fun input : List Bool × List Bool => pairEncoding input.1 input.2)
    TM2Comp.boolEncoding (fun input => decide (input.1 = input.2)) :=
  Turing.PolyBuilder.ListPairEq.computableInPolyTime Bool

#print axioms CLRS.Chapter34.Turing.PolyBuilder.ListPairEq.computableInPolyTime
