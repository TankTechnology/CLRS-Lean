import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression

namespace CLRS.Chapter34.Turing.PolyBuilder

#check exactPolynomialAffineUnaryProgression
#check exactPolynomialAffineUnaryProgression_encode
#check exactPolynomialAffineUnaryProgressionFrameStream
#check exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime

#print axioms exactPolynomialAffineUnaryProgression_encode
#print axioms exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime

example :
    decodeUnaryFrame
        (exactPolynomialAffineUnaryProgressionFrameStream
          (Polynomial.X + 1) Polynomial.X (Polynomial.X + 2)
          [true, false]) =
      some [3, 5, 7, 9] := by
  simp [exactPolynomialAffineUnaryProgressionFrameStream,
    exactPolynomialAffineUnaryProgression, affineUnaryProgressionFrameStream,
    affineUnaryProgressionValues, affineUnaryProgressionValuesFrom,
    Polynomial.eval_add, Polynomial.eval_X]

end CLRS.Chapter34.Turing.PolyBuilder
