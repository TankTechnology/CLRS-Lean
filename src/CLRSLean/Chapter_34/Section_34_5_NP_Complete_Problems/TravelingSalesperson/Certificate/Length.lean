import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Certificate.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Canonicality
import Mathlib.Tactic

/-! # Quadratic decision-TSP certificate length -/

namespace CLRS.Chapter34

/-- Compact binary fields are no longer than the represented value plus the
two delimiters.  The deliberately loose additive constant also covers zero. -/
theorem encodeTSPField_length_le_of_lt {value bound : Nat}
    (hvalue : value < bound) :
    (encodeTSPField value).length ≤ bound + 2 := by
  have hsize : value.size ≤ value :=
    Nat.size_le.mpr value.lt_two_pow_self
  have hbinary := encodeBinaryNat_length_le value
  rw [encodeTSPField_length]
  omega

/-- A list of in-range vertex fields occupies at most one `bound + 2` block
per vertex. -/
theorem encodeTSPFields_length_le_of_lt {values : List Nat} {bound : Nat}
    (hbound : ∀ value ∈ values, value < bound) :
    (encodeTSPFields values).length ≤ values.length * (bound + 2) := by
  induction values with
  | nil => simp [encodeTSPFields]
  | cons value values ih =>
      have hhead := encodeTSPField_length_le_of_lt
        (hbound value (by simp))
      have htail : (encodeTSPFields values).length ≤
          values.length * (bound + 2) := by
        apply ih
        intro candidate hcandidate
        exact hbound candidate (by simp [hcandidate])
      change (encodeTSPField value ++ encodeTSPFields values).length ≤
        (values.length + 1) * (bound + 2)
      rw [List.length_append]
      nlinarith [Nat.add_le_add hhead htail]

/-- Every field contributes at least one physical symbol.  This weak lower
bound is enough because a well-formed TSP input contains a full `n × n`
matrix. -/
theorem encodeTSPFields_count_le_length (values : List Nat) :
    values.length ≤ (encodeTSPFields values).length := by
  induction values with
  | nil => simp [encodeTSPFields]
  | cons value values ih =>
      have hpositive := encodeBinaryNat_length_pos value
      change values.length + 1 ≤
        (encodeTSPField value ++ encodeTSPFields values).length
      rw [List.length_append, encodeTSPField_length]
      omega

/-- A successfully decoded well-formed instance physically dominates its
vertex count. -/
theorem tsp_vertexCount_le_input_length {input : List TSPSym} {data : TSPData}
    (hdecode : decodeTSPData input = some data)
    (hwellFormed : data.WellFormed)
    (hthree : 3 ≤ data.vertexCount) :
    data.vertexCount ≤ input.length := by
  have hcanonical := encodeTSPData_eq_of_decode_eq_some input data hdecode
  have hcount := encodeTSPFields_count_le_length
    (data.vertexCount :: data.budget :: data.weights)
  rw [← hcanonical]
  rw [encodeTSPData_length]
  have hmatrix : data.weights.length =
      data.vertexCount * data.vertexCount := hwellFormed.1
  simp only [List.length_cons, List.length_nil] at hcount
  nlinarith

theorem exists_bounded_tspCertificate_of_mem
    {input : List TSPSym} (hmem : input ∈ GeneralTSP) :
    ∃ certificate,
      certificate.length ≤ (input.length + 2) ^ 2 ∧
      tspVerifier certificate input = true := by
  rcases hmem with
    ⟨data, hdecode, hwellFormed, vertices, hthree, hnodup,
      hlength, hbound, hcost⟩
  change 3 ≤ data.vertexCount at hthree
  change vertices.length = data.vertexCount at hlength
  change ∀ v ∈ vertices, v < data.vertexCount at hbound
  refine ⟨encodeTSPCertificate vertices, ?_, ?_⟩
  · have hfields := encodeTSPFields_length_le_of_lt hbound
    have hinputBound := tsp_vertexCount_le_input_length
      hdecode hwellFormed hthree
    rw [encodeTSPCertificate_length]
    rw [hlength] at hfields
    nlinarith
  · exact (tspVerifier_eq_true_iff _ _).2
      ⟨data, vertices, hdecode, decode_encodeTSPCertificate vertices,
        hwellFormed, hthree, hnodup, hlength, hbound, hcost⟩

theorem mem_generalTSP_iff_exists_bounded_certificate
    (input : List TSPSym) :
    input ∈ GeneralTSP ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 2) ^ 2 ∧
        tspVerifier certificate input = true := by
  constructor
  · exact exists_bounded_tspCertificate_of_mem
  · rintro ⟨certificate, _, hverify⟩
    exact (mem_generalTSP_iff_exists_certificate input).2
      ⟨certificate, hverify⟩

end CLRS.Chapter34
