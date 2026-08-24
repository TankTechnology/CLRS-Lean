import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Parser

/-!
# Exact round trips for TSP records
-/

namespace CLRS.Chapter34

@[simp] theorem decode_encodeTSPData (data : TSPData) :
    decodeTSPData (encodeTSPData data) = some data := by
  simp [encodeTSPData, decodeTSPData, decodeTSPFields_encode]

@[simp] theorem decode_encodeTSPCertificate (vertices : List Nat) :
    decodeTSPCertificate (encodeTSPCertificate vertices) = some vertices := by
  simp [encodeTSPCertificate, decodeTSPCertificate,
    decodeTSPFields_encode]

theorem encodeTSPData_injective : Function.Injective encodeTSPData := by
  intro left right h
  have := congrArg decodeTSPData h
  simpa using this

theorem encodeTSPCertificate_injective :
    Function.Injective encodeTSPCertificate := by
  intro left right h
  have := congrArg decodeTSPCertificate h
  simpa using this

end CLRS.Chapter34
