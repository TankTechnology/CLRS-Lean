import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrameFamily

namespace CLRS.Chapter34.Turing.PolyBuilder

#check polynomialFamilyDegree
#check exactPolynomialUnaryFrames
#check exactPolynomialUnaryFrames_eq
#check exactPolynomialUnaryFrames_computableInPolyTime

#print axioms exactPolynomialAtDepthClock_length
#print axioms exactPolynomialUnaryFrameFamily_tagRow
#print axioms exactPolynomialUnaryFrames_eq
#print axioms exactPolynomialUnaryFrames_computableInPolyTime

example :
    decodeUnaryFrame
        (exactPolynomialUnaryFrames
          [Polynomial.X + 1, 2] [true, false]) =
      some [3, 2] := by
  simp [exactPolynomialUnaryFrames, Polynomial.eval_add, Polynomial.eval_X]

example :
    exactPolynomialUnaryFrames ([] : List (Polynomial Nat)) [true] = [] :=
  rfl

end CLRS.Chapter34.Turing.PolyBuilder
