import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryIndexFrames

namespace CLRS.Chapter34.Turing.PolyBuilder

#check unaryIndexFrameSymbol
#check exactPolynomialUnaryIndexFrames
#check exactPolynomialUnaryIndexFrames_eq_map
#check exactPolynomialUnaryIndexFrames_computableInPolyTime

#print axioms exactPolynomialUnaryIndexFrames_eq_map
#print axioms exactPolynomialUnaryIndexFrames_computableInPolyTime

example :
    decodeUnaryFrame
        (exactPolynomialUnaryIndexFrames
          (Polynomial.X + 1) [true, false]) =
      some [0, 1, 2] := by
  simp [exactPolynomialUnaryIndexFrames, Polynomial.eval_add,
    Polynomial.eval_X]
  decide

end CLRS.Chapter34.Turing.PolyBuilder
