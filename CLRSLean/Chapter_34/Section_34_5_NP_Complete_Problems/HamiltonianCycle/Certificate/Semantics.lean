import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Certificate.Basic

/-! # Exact HAM-CYCLE certificate semantics -/

namespace CLRS.Chapter34

theorem hamiltonianCycleVerifier_eq_true_iff
    (certificate input : List HamiltonianCycleSym) :
    hamiltonianCycleVerifier certificate input = true ↔
      ∃ I vertices,
        decodeHamiltonianCycleInstance input = some I ∧
        decodeHamiltonianCycleCertificate certificate = some vertices ∧
        I.WellFormed ∧ I.targetSize = I.vertexCount ∧
        I.ListRepresentsHamiltonianCycle vertices := by
  generalize hinput : decodeHamiltonianCycleInstance input = instanceResult
  generalize hcertificate : decodeHamiltonianCycleCertificate certificate =
    certificateResult
  cases instanceResult <;> cases certificateResult <;>
    simp [hamiltonianCycleVerifier, hinput, hcertificate]

theorem mem_generalHAMCYCLE_iff_exists_certificate
    (input : List HamiltonianCycleSym) :
    input ∈ GeneralHAMCYCLE ↔
      ∃ certificate, hamiltonianCycleVerifier certificate input = true := by
  constructor
  · rintro ⟨I, hdecode, hI, htarget, vertices, hvertices⟩
    refine ⟨encodeHamiltonianCycleCertificate vertices, ?_⟩
    exact (hamiltonianCycleVerifier_eq_true_iff _ _).2
      ⟨I, vertices, hdecode, decode_encodeCliqueCertificate vertices,
        hI, htarget, hvertices⟩
  · rintro ⟨certificate, hverify⟩
    rcases (hamiltonianCycleVerifier_eq_true_iff certificate input).1 hverify with
      ⟨I, vertices, hdecode, _, hI, htarget, hvertices⟩
    exact ⟨I, hdecode, hI, htarget, vertices, hvertices⟩

end CLRS.Chapter34
