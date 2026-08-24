import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.RoundTrip
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Length

/-! # Physical lengths of serialized SUBSET-SUM records -/

namespace CLRS.Chapter34

@[simp] theorem encodeSubsetSumData_length (data : SubsetSumData) :
    (encodeSubsetSumData data).length =
      (encodeTSPFields (data.target :: data.values)).length + 2 := by
  simp [encodeSubsetSumData]

@[simp] theorem encodeSubsetSumCertificate_length (indices : List Nat) :
    (encodeSubsetSumCertificate indices).length =
      (encodeTSPFields indices).length + 2 := by
  exact encodeTSPCertificate_length indices

end CLRS.Chapter34
