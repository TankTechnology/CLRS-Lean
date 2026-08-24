import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Certificate.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Length

/-! # Quadratic HAM-CYCLE certificate length -/

namespace CLRS.Chapter34

theorem exists_bounded_hamiltonianCycleCertificate_of_mem
    {input : List HamiltonianCycleSym} (hmem : input ∈ GeneralHAMCYCLE) :
    ∃ certificate,
      certificate.length ≤ (input.length + 1) ^ 2 ∧
      hamiltonianCycleVerifier certificate input = true := by
  rcases hmem with ⟨I, hdecode, hI, htarget, vertices, hvertices⟩
  refine ⟨encodeHamiltonianCycleCertificate vertices, ?_, ?_⟩
  · have hrecords := flatMap_encodeCliqueVertex_length_le hvertices.2.2.2.1
    have hfields := decodeCliqueInstance_fields_le_length hdecode
    rw [encodeCliqueCertificate_length]
    nlinarith [hvertices.2.2.1]
  · exact (hamiltonianCycleVerifier_eq_true_iff _ _).2
      ⟨I, vertices, hdecode, decode_encodeCliqueCertificate vertices,
        hI, htarget, hvertices⟩

theorem mem_generalHAMCYCLE_iff_exists_bounded_certificate
    (input : List HamiltonianCycleSym) :
    input ∈ GeneralHAMCYCLE ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 1) ^ 2 ∧
        hamiltonianCycleVerifier certificate input = true := by
  constructor
  · exact exists_bounded_hamiltonianCycleCertificate_of_mem
  · rintro ⟨certificate, _, hverify⟩
    exact (mem_generalHAMCYCLE_iff_exists_certificate input).2
      ⟨certificate, hverify⟩

end CLRS.Chapter34
