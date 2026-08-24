import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.VerifierMachine.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Length

/-!
# Certificate length for the complement-clique VERTEX-COVER verifier

Although the complemented graph can have cubic unary encoding length, its
certificate still lists at most the original vertex set and every listed
vertex is below the original unary vertex count.  The physical certificate is
therefore quadratic in the original VERTEX-COVER input, not degree six.
-/

namespace CLRS.Chapter34

/-- Every VERTEX-COVER yes-instance has an accepted complement-clique
certificate of quadratic physical length. -/
theorem exists_bounded_vertexCoverCliqueCertificate_of_mem
    {input : List VertexCoverSym} (hmem : input ∈ GeneralVERTEXCOVER) :
    ∃ certificate,
      certificate.length ≤ (input.length + 1) ^ 2 ∧
      vertexCoverCliqueVerifier certificate input = true := by
  rcases hmem with ⟨I, hdecode, hI, hcover⟩
  have hclique : I.complementForVertexCover.HasClique :=
    (I.hasVertexCover_iff_complement_hasClique hI).1 hcover
  rcases I.complementForVertexCover.exists_listRepresentsClique_of_hasClique
      hclique with
    ⟨vertices, hvertices⟩
  refine ⟨encodeCliqueCertificate vertices, ?_, ?_⟩
  · have hbound : ∀ v ∈ vertices, v < I.vertexCount := by
      intro v hv
      simpa [CliqueInstance.complementForVertexCover] using hvertices.2.2.1 v hv
    have hlength : vertices.length ≤ I.vertexCount := by
      rw [hvertices.2.1]
      simp [CliqueInstance.complementForVertexCover]
    have hrecords := flatMap_encodeCliqueVertex_length_le hbound
    have hfields := decodeCliqueInstance_fields_le_length hdecode
    rw [encodeCliqueCertificate_length]
    nlinarith
  · exact (vertexCoverCliqueVerifier_eq_true_iff _ _).2
      ⟨I, vertices, hdecode, decode_encodeCliqueCertificate vertices,
        hI, hvertices⟩

/-- Exact bounded-certificate characterization used by `PolyTimeVerifiable`. -/
theorem mem_generalVERTEXCOVER_iff_exists_bounded_cliqueCertificate
    (input : List VertexCoverSym) :
    input ∈ GeneralVERTEXCOVER ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 1) ^ 2 ∧
        vertexCoverCliqueVerifier certificate input = true := by
  constructor
  · exact exists_bounded_vertexCoverCliqueCertificate_of_mem
  · rintro ⟨certificate, _, hverify⟩
    exact (mem_generalVERTEXCOVER_iff_exists_cliqueCertificate input).2
      ⟨certificate, hverify⟩

end CLRS.Chapter34
