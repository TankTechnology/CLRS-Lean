import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryProgression

namespace CLRS.Chapter34.Turing.PolyBuilder

#check AffineUnaryProgression
#check encodeAffineUnaryProgression
#check affineUnaryProgressionValues
#check affineUnaryProgressionValuesFrom_eq_ofFn
#check affineUnaryProgressionFrameStream
#check affineUnaryProgressionRev_run
#check affineUnaryProgressionRev_computableInPolyTime
#check affineUnaryProgressionFrameStream_computableInPolyTime

#print axioms affineUnaryProgressionRev_run
#print axioms affineUnaryProgressionFrameStream_computableInPolyTime

example :
    decodeUnaryFrame
        (affineUnaryProgressionFrameStream
          { base := 2, step := 3, count := 4 }) =
      some [2, 5, 8, 11] := by
  decide

end CLRS.Chapter34.Turing.PolyBuilder
