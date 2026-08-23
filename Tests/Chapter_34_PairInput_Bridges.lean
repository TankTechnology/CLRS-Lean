import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Runtime

/-!
# Regression test: reusable pair-input bridges
-/

open CLRS Chapter34
open CLRS.Chapter34.Turing.PolyBuilder

#check PairFirstProjection.computableInPolyTime
#check OptionPairLeft.computableInPolyTime

example : OptionPairLeft.format ([1, 2] : List Nat) =
    [some 1, some 2, none] := rfl
