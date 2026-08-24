import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.RoundTrip
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Canonicality

/-! # Canonicality of successful SUBSET-SUM decodes -/

namespace CLRS.Chapter34

theorem encodeSubsetSumData_eq_of_decode_eq_some
    (input : List SubsetSumSym) (data : SubsetSumData)
    (hdecode : decodeSubsetSumData input = some data) :
    encodeSubsetSumData data = input := by
  cases input with
  | nil => simp [decodeSubsetSumData] at hdecode
  | cons symbol payload =>
      cases symbol <;> try simp [decodeSubsetSumData] at hdecode
      case instanceMark =>
        generalize hfields : decodeTSPFields payload = result at hdecode
        cases result with
        | none => simp at hdecode
        | some fields =>
            cases fields with
            | nil => simp at hdecode
            | cons target values =>
                simp only [Option.some.injEq] at hdecode
                subst data
                have hcanonical :=
                  eq_encodeTSPFields_append_recordEnd_of_decode_eq_some
                    payload (target :: values) hfields
                simp [encodeSubsetSumData, hcanonical]

theorem encodeSubsetSumCertificate_eq_of_decode_eq_some
    (input : List SubsetSumSym) (indices : List Nat)
    (hdecode : decodeSubsetSumCertificate input = some indices) :
    encodeSubsetSumCertificate indices = input := by
  exact encodeTSPCertificate_eq_of_decode_eq_some input indices hdecode

end CLRS.Chapter34
