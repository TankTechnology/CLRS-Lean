import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

inductive TestMode
  | left
  | right
deriving DecidableEq, Fintype

def testStatefulFlatMapSpec : StatefulFlatMapSpec TestMode Bool Bool where
  initial := .left
  action
    | .left, false => ([false, true], .right)
    | .left, true => ([], .right)
    | .right, false => ([true], .left)
    | .right, true => ([false], .left)
  finish
    | .left => [false]
    | .right => [true]

example :
    rewriteStatefulFlatMap testStatefulFlatMapSpec [false, true] =
      [false, true, false, false] := by
  native_decide

#check statefulFlatMapRev_builderOutputs
#check statefulFlatMapRev_computableInPolyTime
#check statefulFlatMap_computableInPolyTime

end CLRS.Chapter34.Turing.PolyBuilder
