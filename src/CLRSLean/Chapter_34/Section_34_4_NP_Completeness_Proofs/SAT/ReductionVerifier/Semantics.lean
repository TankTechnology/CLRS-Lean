import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.ReductionVerifier.Runtime

/-!
# Exact certificate semantics of the reduction-backed SAT verifier

The certificate polynomial composes the quadratic SAT-to-3-CNF output bound
with the cubic 3-CNF-to-CLIQUE bound and the quadratic CLIQUE certificate
bound.  No asymptotic side condition is hidden in the final language theorem.
-/

namespace CLRS.Chapter34

/-- Certificate-size polynomial for the reduction-backed SAT verifier. -/
noncomputable def satReductionCertificatePolynomial : Polynomial Nat :=
  ((64 : Polynomial Nat) *
      ((800 : Polynomial Nat) * (Polynomial.X + 1) ^ 2 + 1) ^ 3 + 1) ^ 2

@[simp] theorem satReductionCertificatePolynomial_eval (n : Nat) :
    satReductionCertificatePolynomial.eval n =
      (64 * (800 * (n + 1) ^ 2 + 1) ^ 3 + 1) ^ 2 := by
  simp [satReductionCertificatePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- Exact bounded-certificate characterization of raw SAT using one fixed
reduction-backed verifier. -/
theorem mem_SAT_iff_exists_reduction_certificate (input : List FormulaSym) :
    input ∈ SAT ↔
      ∃ certificate : List FormulaSym,
        certificate.length ≤
            satReductionCertificatePolynomial.eval input.length ∧
          satReductionVerifier certificate input = true := by
  constructor
  · intro hinput
    have hthree : satToThreeCNFMap input ∈ ThreeCNFSat :=
      (satToThreeCNFMap_mem_iff input).2 hinput
    rcases (mem_threeCNFSat_iff_exists_reduction_certificate
        (satToThreeCNFMap input)).1 hthree with
      ⟨certificate, hbound, haccept⟩
    refine ⟨cnfToFormulaCertificate certificate, ?_, ?_⟩
    · rw [threeCNFReductionCertificatePolynomial_eval] at hbound
      have hmap := satToThreeCNFMap_length_le input
      have hplus : (satToThreeCNFMap input).length + 1 ≤
          800 * (input.length + 1) ^ 2 + 1 :=
        Nat.add_le_add_right hmap 1
      have hcubed := Nat.pow_le_pow_left hplus 3
      have hscaled := Nat.mul_le_mul_left 64 hcubed
      have hadd := Nat.add_le_add_right hscaled 1
      have hsquared := Nat.pow_le_pow_left hadd 2
      calc
        (cnfToFormulaCertificate certificate).length =
            certificate.length := cnfToFormulaCertificate_length certificate
        _ ≤ (64 * ((satToThreeCNFMap input).length + 1) ^ 3 + 1) ^ 2 :=
          hbound
        _ ≤ (64 * (800 * (input.length + 1) ^ 2 + 1) ^ 3 + 1) ^ 2 :=
          hsquared
        _ = satReductionCertificatePolynomial.eval input.length := by
          symm
          exact satReductionCertificatePolynomial_eval input.length
    · simpa [satReductionVerifier] using haccept
  · rintro ⟨certificate, _hbound, haccept⟩
    have hthreeAccept :
        threeCNFReductionVerifier
            (formulaToCNFCertificate certificate)
            (satToThreeCNFMap input) = true := by
      simpa [satReductionVerifier] using haccept
    have hthree : satToThreeCNFMap input ∈ ThreeCNFSat :=
      threeCNFReductionVerifier_sound hthreeAccept
    exact (satToThreeCNFMap_mem_iff input).1 hthree

end CLRS.Chapter34
