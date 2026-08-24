import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.Parser

/-! # Round trips for the compact SUBSET-SUM encoding -/

namespace CLRS.Chapter34

@[simp] theorem decode_encodeSubsetSumData (data : SubsetSumData) :
    decodeSubsetSumData (encodeSubsetSumData data) = some data := by
  simp [decodeSubsetSumData, encodeSubsetSumData]

@[simp] theorem decode_encodeSubsetSumCertificate (indices : List Nat) :
    decodeSubsetSumCertificate (encodeSubsetSumCertificate indices) =
      some indices := by
  exact decode_encodeTSPCertificate indices

end CLRS.Chapter34
