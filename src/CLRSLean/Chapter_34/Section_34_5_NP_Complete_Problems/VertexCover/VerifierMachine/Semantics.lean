import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.VerifierMachine.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.BidirectionalSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Semantics

/-!
# Exact semantics of the complement-clique VERTEX-COVER verifier

The raw well-formedness guard recovers the original typed graph.  The reused
CLIQUE verifier then checks that the certificate represents a clique in the
deterministic complement, which is equivalent to a vertex cover in the source.
-/

namespace CLRS.Chapter34

open Turing.VertexCover

/-- Exact accepted-certificate characterization on arbitrary raw words. -/
theorem vertexCoverCliqueVerifier_eq_true_iff
    (certificate input : List VertexCoverSym) :
    vertexCoverCliqueVerifier certificate input = true ↔
      ∃ I vertices,
        decodeVertexCoverInstance input = some I ∧
        decodeVertexCoverCertificate certificate = some vertices ∧
        I.WellFormed ∧
        I.complementForVertexCover.ListRepresentsClique vertices := by
  constructor
  · intro hverify
    have hparts :
        ComplementMachine.RawWellFormed.rawWellFormedPass input = true ∧
          cliqueVerifier certificate
            (ComplementMachine.Total.normalizedComplement input) = true := by
      simpa [vertexCoverCliqueVerifier] using hverify
    have hnormalizedWellFormed :=
      (ComplementMachine.RawWellFormed.rawWellFormedPass_eq_true_iff input).1
        hparts.1
    rcases (cliqueVerifier_eq_true_iff certificate
      (ComplementMachine.Total.normalizedComplement input)).1 hparts.2 with
      ⟨J, vertices, hJ, hcertificate, _, hvertices⟩
    cases hdecode : decodeVertexCoverInstance input with
    | none =>
        have hnot :=
          ComplementMachine.SyntaxNormalizer.normalizedInstanceValue_not_wellFormed_of_decode_none
            hdecode
        exact False.elim (hnot hnormalizedWellFormed)
    | some I =>
        have hnormalized :
            ComplementMachine.SyntaxNormalizer.normalizedInstanceValue input = I :=
          ComplementMachine.SyntaxNormalizer.normalizedInstanceValue_of_decode_some
            hdecode
        have hJValue : J = I.complementForVertexCover := by
          have hdecoded :
              decodeCliqueInstance
                  (ComplementMachine.Total.normalizedComplement input) =
                some I.complementForVertexCover := by
            rw [ComplementMachine.Total.normalizedComplement, hnormalized]
            exact decode_encodeCliqueInstance I.complementForVertexCover
          exact Option.some.inj (hJ.symm.trans hdecoded)
        subst J
        rw [hnormalized] at hnormalizedWellFormed
        exact ⟨I, vertices, rfl, hcertificate,
          hnormalizedWellFormed, hvertices⟩
  · rintro ⟨I, vertices, hdecode, hcertificate, hI, hvertices⟩
    have hnormalized :
        ComplementMachine.SyntaxNormalizer.normalizedInstanceValue input = I :=
      ComplementMachine.SyntaxNormalizer.normalizedInstanceValue_of_decode_some
        hdecode
    have hraw :
        ComplementMachine.RawWellFormed.rawWellFormedPass input = true :=
      (ComplementMachine.RawWellFormed.rawWellFormedPass_eq_true_iff input).2
        (hnormalized.symm ▸ hI)
    have hclique : cliqueVerifier certificate
        (ComplementMachine.Total.normalizedComplement input) = true :=
      (cliqueVerifier_eq_true_iff _ _).2
        ⟨I.complementForVertexCover, vertices, by
          rw [ComplementMachine.Total.normalizedComplement, hnormalized]
          exact decode_encodeCliqueInstance I.complementForVertexCover,
          hcertificate, I.complementForVertexCover_wellFormed hI, hvertices⟩
    simpa [vertexCoverCliqueVerifier, hraw, hclique]

/-- VERTEX-COVER membership is exactly existence of a certificate accepted by
the fixed complement-clique verifier. -/
theorem mem_generalVERTEXCOVER_iff_exists_cliqueCertificate
    (input : List VertexCoverSym) :
    input ∈ GeneralVERTEXCOVER ↔
      ∃ certificate, vertexCoverCliqueVerifier certificate input = true := by
  constructor
  · rintro ⟨I, hdecode, hI, hcover⟩
    have hclique : I.complementForVertexCover.HasClique :=
      (I.hasVertexCover_iff_complement_hasClique hI).1 hcover
    rcases I.complementForVertexCover.exists_listRepresentsClique_of_hasClique
        hclique with
      ⟨vertices, hvertices⟩
    refine ⟨encodeCliqueCertificate vertices, ?_⟩
    exact (vertexCoverCliqueVerifier_eq_true_iff _ _).2
      ⟨I, vertices, hdecode, decode_encodeCliqueCertificate vertices,
        hI, hvertices⟩
  · rintro ⟨certificate, hverify⟩
    rcases (vertexCoverCliqueVerifier_eq_true_iff certificate input).1 hverify with
      ⟨I, vertices, hdecode, _, hI, hvertices⟩
    have hclique : I.complementForVertexCover.HasClique :=
      I.complementForVertexCover.hasClique_of_listRepresentsClique hvertices
    exact ⟨I, hdecode, hI,
      (I.hasVertexCover_iff_complement_hasClique hI).2 hclique⟩

end CLRS.Chapter34
