import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Certificate.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Length

/-!
# Polynomial certificate bound for VERTEX-COVER

The shared unary vertex-list codec and its general-CLIQUE length lemmas give a
quadratic physical certificate bound for VERTEX-COVER as well.
-/

namespace CLRS
namespace Chapter34

/-- Membership in general VERTEX-COVER supplies a canonical accepted
certificate of quadratic physical length. -/
theorem exists_bounded_vertexCoverCertificate_of_mem
    {input : List VertexCoverSym} (hmem : input ∈ GeneralVERTEXCOVER) :
    ∃ certificate,
      certificate.length ≤ (input.length + 1) ^ 2 ∧
      vertexCoverVerifier certificate input = true := by
  rcases hmem with ⟨I, hdecode, hwellFormed, hcover⟩
  rcases I.exists_listRepresentsVertexCover_of_hasVertexCover hcover with
    ⟨vertices, hvertices⟩
  refine ⟨encodeVertexCoverCertificate vertices, ?_, ?_⟩
  · rcases hvertices with ⟨_, hcard, hbound, _⟩
    have hrecords := flatMap_encodeCliqueVertex_length_le hbound
    have hfields := decodeCliqueInstance_fields_le_length hdecode
    rw [encodeCliqueCertificate_length]
    nlinarith
  · exact (vertexCoverVerifier_eq_true_iff _ _).2
      ⟨I, vertices, hdecode, decode_encodeCliqueCertificate vertices,
        hwellFormed, hvertices⟩

/-- Exact certificate characterization of general VERTEX-COVER, including the
quadratic certificate-size polynomial needed by `PolyTimeVerifiable`. -/
theorem mem_generalVERTEXCOVER_iff_exists_certificate
    (input : List VertexCoverSym) :
    input ∈ GeneralVERTEXCOVER ↔
      ∃ certificate,
        certificate.length ≤ (input.length + 1) ^ 2 ∧
        vertexCoverVerifier certificate input = true := by
  constructor
  · exact exists_bounded_vertexCoverCertificate_of_mem
  · rintro ⟨certificate, _, hverify⟩
    rcases (vertexCoverVerifier_eq_true_iff certificate input).1 hverify with
      ⟨I, vertices, hdecode, _, hwellFormed, hvertices⟩
    exact ⟨I, hdecode, hwellFormed,
      I.hasVertexCover_of_listRepresentsVertexCover hvertices⟩

end Chapter34
end CLRS
