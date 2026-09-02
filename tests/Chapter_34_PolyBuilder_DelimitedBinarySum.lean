import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DelimitedBinarySum

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum

example :
    binaryNatValue
        (sumDelimited ([3, 5, 9].flatMap fun value =>
          (encodeBinaryNat value).map some ++ [none])) = 17 := by
  simpa using binaryNatValue_sumDelimited_encoded [3, 5, 9]

#print axioms binaryNatValue_sumDelimited_encoded
#print axioms computableInPolyTime

end CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum
