import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Certificate.Basic

/-! # Exact decision-TSP certificate semantics -/

namespace CLRS.Chapter34

theorem tspVerifier_eq_true_iff
    (certificate input : List TSPSym) :
    tspVerifier certificate input = true ↔
      ∃ data vertices,
        decodeTSPData input = some data ∧
        decodeTSPCertificate certificate = some vertices ∧
        data.WellFormed ∧
        data.toInstance.ListRepresentsTour vertices := by
  generalize hinput : decodeTSPData input = instanceResult
  generalize hcertificate : decodeTSPCertificate certificate =
    certificateResult
  cases instanceResult <;> cases certificateResult <;>
    simp [tspVerifier, hinput, hcertificate]

theorem mem_generalTSP_iff_exists_certificate (input : List TSPSym) :
    input ∈ GeneralTSP ↔
      ∃ certificate, tspVerifier certificate input = true := by
  constructor
  · rintro ⟨data, hdecode, hwellFormed, vertices, hvertices⟩
    refine ⟨encodeTSPCertificate vertices, ?_⟩
    exact (tspVerifier_eq_true_iff _ _).2
      ⟨data, vertices, hdecode, decode_encodeTSPCertificate vertices,
        hwellFormed, hvertices⟩
  · rintro ⟨certificate, hverify⟩
    rcases (tspVerifier_eq_true_iff certificate input).1 hverify with
      ⟨data, vertices, hdecode, _, hwellFormed, hvertices⟩
    exact ⟨data, hdecode, hwellFormed, vertices, hvertices⟩

end CLRS.Chapter34
