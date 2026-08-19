import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryTripleProgression

open Polynomial
open CLRS.Chapter34.Turing.PolyBuilder

#check exactPolynomialAffineUnaryTripleProgression
#check exactPolynomialAffineUnaryTripleProgression_encode
#check exactPolynomialAffineUnaryTripleProgressionFrameStream
#check exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime

#print axioms exactPolynomialAffineUnaryTripleProgression_encode
#print axioms exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime

example :
    exactPolynomialAffineUnaryTripleProgressionFrameStream
      (X + 1) (X + 2) (X + 3) 1 2 3 (X + 1)
      ([true, false] : List Bool) =
      encodeUnaryFrame [3, 4, 5, 4, 6, 8, 5, 8, 11] := by
  simp [exactPolynomialAffineUnaryTripleProgressionFrameStream,
    exactPolynomialAffineUnaryTripleProgression,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionRows,
    affineUnaryTripleProgressionRowsFrom,
    affineUnaryTripleRowValues, encodeUnaryFrame, List.append_assoc]
