import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

namespace CLRS.Chapter34.Turing.PolyBuilder

#check reverseProgram
#check reverseSteps
#check reverse_run
#check reverse_outputs
#check reverse_polyBound
#check reverse_computableInPolyTime

example : List.reverse ([true, false, false] : List Bool) =
    [false, false, true] := by
  native_decide

end CLRS.Chapter34.Turing.PolyBuilder
