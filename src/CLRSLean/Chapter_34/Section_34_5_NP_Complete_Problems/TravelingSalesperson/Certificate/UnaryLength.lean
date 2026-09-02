import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Certificate.Length
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.Final.Semantics
import Mathlib.Tactic

/-! # Quadratic unary tour certificates for decision-TSP -/

namespace CLRS.Chapter34

open Turing.TSPVerifier

private theorem unary_payload_sum_le {vertices : List Nat} {bound : Nat}
    (hbound : ∀ vertex ∈ vertices, vertex < bound) :
    (vertices.map fun vertex => vertex + 2).sum ≤
      vertices.length * (bound + 1) := by
  induction vertices with
  | nil => simp
  | cons vertex vertices ih =>
      have hhead : vertex + 2 ≤ bound + 1 := by
        have := hbound vertex (by simp)
        omega
      have htail : (vertices.map fun value => value + 2).sum ≤
          vertices.length * (bound + 1) := by
        apply ih
        intro value hvalue
        exact hbound value (by simp [hvalue])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

/-- Every accepted TSP instance has a canonical unary tour certificate whose
physical length is quadratic in the compact instance length. -/
theorem exists_bounded_unaryTSPCertificate_of_mem
    {input : List TSPSym} (hmem : input ∈ GeneralTSP) :
    ∃ certificate,
      certificate.length ≤ (input.length + 1) ^ 2 ∧
      Final.concreteTSPVerifier (certificate, input) = true := by
  rcases hmem with
    ⟨data, hdecode, hwellFormed, vertices, hminimum, hnodup,
      hlength, hbound, hcost⟩
  change 3 ≤ data.vertexCount at hminimum
  change vertices.length = data.vertexCount at hlength
  change (∀ vertex ∈ vertices, vertex < data.vertexCount) at hbound
  change data.toInstance.tourCost vertices ≤ data.budget at hcost
  refine ⟨Turing.TSPVerifier.UnaryCertificate.encode vertices, ?_, ?_⟩
  · have hpayload := unary_payload_sum_le hbound
    have hvertexCount := tsp_vertexCount_le_input_length
      hdecode hwellFormed hminimum
    rw [Turing.TSPVerifier.UnaryCertificate.encode_length]
    rw [hlength] at hpayload
    nlinarith
  · have hcanonical := encodeTSPData_eq_of_decode_eq_some input data hdecode
    rw [← hcanonical]
    exact (Final.concreteTSPVerifier_encode_iff vertices data).2
      ⟨hwellFormed, hminimum, hnodup, hlength, hbound, hcost⟩

theorem mem_generalTSP_iff_exists_bounded_unary_certificate
    (input : List TSPSym) :
    input ∈ GeneralTSP ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 1) ^ 2 ∧
        Final.concreteTSPVerifier (certificate, input) = true := by
  constructor
  · exact exists_bounded_unaryTSPCertificate_of_mem
  · rintro ⟨certificate, _, haccept⟩
    rcases (Final.concreteTSPVerifier_eq_true_iff certificate input).1 haccept
      with ⟨data, vertices, hdecode, _, hwellFormed, htour⟩
    exact ⟨data, hdecode, hwellFormed, vertices, htour⟩

end CLRS.Chapter34
