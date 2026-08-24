import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.RoundTrip

/-!
# Physical lengths of serialized TSP records
-/

namespace CLRS.Chapter34

@[simp] theorem encodeTSPField_length (n : Nat) :
    (encodeTSPField n).length = (encodeBinaryNat n).length + 2 := by
  simp [encodeTSPField]

theorem encodeTSPFields_length (values : List Nat) :
    (encodeTSPFields values).length =
      (values.map (fun value => (encodeBinaryNat value).length + 2)).sum := by
  induction values with
  | nil => simp [encodeTSPFields]
  | cons value values ih =>
      simp [encodeTSPFields, encodeTSPField]
      omega

@[simp] theorem encodeTSPData_length (data : TSPData) :
    (encodeTSPData data).length =
      (encodeTSPFields
        (data.vertexCount :: data.budget :: data.weights)).length + 2 := by
  simp [encodeTSPData]

@[simp] theorem encodeTSPCertificate_length (vertices : List Nat) :
    (encodeTSPCertificate vertices).length =
      (encodeTSPFields vertices).length + 2 := by
  simp [encodeTSPCertificate]

end CLRS.Chapter34
