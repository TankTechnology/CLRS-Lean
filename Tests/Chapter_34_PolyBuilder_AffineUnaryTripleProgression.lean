import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression

open CLRS.Chapter34.Turing.PolyBuilder

#check AffineUnaryTripleProgression
#check encodeAffineUnaryTripleProgression
#check affineUnaryTripleProgressionRows
#check affineUnaryTripleProgressionRows_eq_ofFn
#check affineUnaryTripleProgressionFrameStream
#check affineUnaryTripleProgressionRev_run
#check affineUnaryTripleProgressionFrameStream_computableInPolyTime

#print axioms affineUnaryTripleProgressionRev_run
#print axioms affineUnaryTripleProgressionFrameStream_computableInPolyTime

example :
    affineUnaryTripleProgressionRows
      { base₁ := 1, base₂ := 2, base₃ := 3
        step₁ := 2, step₂ := 3, step₃ := 4, count := 3 } =
      [(1, 2, 3), (3, 5, 7), (5, 8, 11)] := by
  decide
