import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.ReductionVerifier.Runtime

/-!
# Exact certificate semantics of the reduction-backed 3-CNF verifier

The polynomial combines the cubic size of the honest 3-CNF-to-CLIQUE
instance with the quadratic certificate bound of general CLIQUE.  The source
certificate codec preserves the canonical CLIQUE certificate length exactly.
-/

namespace CLRS.Chapter34

/-- Certificate-size polynomial for the reduction-backed verifier. -/
noncomputable def threeCNFReductionCertificatePolynomial : Polynomial Nat :=
  ((64 : Polynomial Nat) * (Polynomial.X + 1) ^ 3 + 1) ^ 2

@[simp] theorem threeCNFReductionCertificatePolynomial_eval (n : Nat) :
    threeCNFReductionCertificatePolynomial.eval n =
      (64 * (n + 1) ^ 3 + 1) ^ 2 := by
  simp [threeCNFReductionCertificatePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- Acceptance by the reduction-backed verifier is sound independently of
any certificate-size bound.  Keeping this lemma separate lets later
reductions reuse the semantic direction without manufacturing a redundant
bound. -/
theorem threeCNFReductionVerifier_sound {certificate input : List CNFSym}
    (haccept : threeCNFReductionVerifier certificate input = true) :
    input ∈ ThreeCNFSat := by
  have hcliqueAccept :
      cliqueVerifier (cnfToCliqueCertificate certificate)
          (threeCNFToGeneralCliqueMap input) = true := by
    simpa [threeCNFReductionVerifier] using haccept
  rcases (cliqueVerifier_eq_true_iff _ _).1 hcliqueAccept with
    ⟨I, vertices, hdecode, _hcertificate, hwellFormed, hvertices⟩
  have htarget : threeCNFToGeneralCliqueMap input ∈ GeneralCLIQUE :=
    ⟨I, hdecode, hwellFormed,
      I.hasClique_of_listRepresentsClique hvertices⟩
  exact (threeCNFToGeneralCliqueMap_mem_iff input).1 htarget

/-- Exact bounded-certificate characterization of raw 3-CNF-SAT using the
fixed reduction-backed verifier. -/
theorem mem_threeCNFSat_iff_exists_reduction_certificate
    (input : List CNFSym) :
    input ∈ ThreeCNFSat ↔
      ∃ certificate : List CNFSym,
        certificate.length ≤
            threeCNFReductionCertificatePolynomial.eval input.length ∧
          threeCNFReductionVerifier certificate input = true := by
  constructor
  · intro hinput
    have htarget : threeCNFToGeneralCliqueMap input ∈ GeneralCLIQUE :=
      (threeCNFToGeneralCliqueMap_mem_iff input).2 hinput
    rcases (mem_generalCLIQUE_iff _).1 htarget with
      ⟨I, hdecode, hwellFormed, hclique⟩
    rcases I.exists_listRepresentsClique_of_hasClique hclique with
      ⟨vertices, hvertices⟩
    let certificate := encodeCNFCliqueCertificate vertices
    refine ⟨certificate, ?_, ?_⟩
    · have hrecords := flatMap_encodeCliqueVertex_length_le
          (fun vertex hvertex => hvertices.2.2.1 vertex hvertex)
      have hfields := decodeCliqueInstance_fields_le_length hdecode
      have htargetCertificate :
          (encodeCliqueCertificate vertices).length ≤
            ((threeCNFToGeneralCliqueMap input).length + 1) ^ 2 := by
        rw [encodeCliqueCertificate_length]
        nlinarith [hrecords, hfields, hvertices.2.1]
      have htargetLength := threeCNFToGeneralCliqueMap_length input
      have hsquare :
          ((threeCNFToGeneralCliqueMap input).length + 1) ^ 2 ≤
            (64 * (input.length + 1) ^ 3 + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right htargetLength 1) 2
      calc
        certificate.length =
            (encodeCliqueCertificate vertices).length := by
          simp [certificate]
        _ ≤ ((threeCNFToGeneralCliqueMap input).length + 1) ^ 2 :=
          htargetCertificate
        _ ≤ (64 * (input.length + 1) ^ 3 + 1) ^ 2 := hsquare
        _ = threeCNFReductionCertificatePolynomial.eval input.length := by
          symm
          exact threeCNFReductionCertificatePolynomial_eval input.length
    · apply (cliqueVerifier_eq_true_iff _ _).2
      refine ⟨I, vertices, hdecode, ?_, hwellFormed, hvertices⟩
      simpa [threeCNFReductionVerifier, certificate] using
        decode_encodeCliqueCertificate vertices
  · rintro ⟨certificate, _hbound, haccept⟩
    exact threeCNFReductionVerifier_sound haccept

end CLRS.Chapter34
