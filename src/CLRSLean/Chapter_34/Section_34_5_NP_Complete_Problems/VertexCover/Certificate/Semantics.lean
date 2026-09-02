import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Certificate.Basic

/-!
# Exact semantics of VERTEX-COVER certificates

The Boolean checker is characterized on every raw input.  The duplicate-free
list predicate is then connected in both directions to the finite-set cover
semantics.
-/

namespace CLRS
namespace Chapter34

/-- Exact all-input truth theorem for the Boolean VERTEX-COVER checker. -/
theorem vertexCoverVerifier_eq_true_iff
    (certificate input : List VertexCoverSym) :
    vertexCoverVerifier certificate input = true ↔
      ∃ I vertices,
        decodeVertexCoverInstance input = some I ∧
        decodeVertexCoverCertificate certificate = some vertices ∧
        I.WellFormed ∧ I.ListRepresentsVertexCover vertices := by
  generalize hinput : decodeVertexCoverInstance input = instanceResult
  generalize hcertificate :
    decodeVertexCoverCertificate certificate = certificateResult
  cases instanceResult <;> cases certificateResult <;>
    simp [vertexCoverVerifier, hinput, hcertificate]

namespace CliqueInstance

/-- A duplicate-free list certificate induces the corresponding finite-set
vertex-cover witness. -/
theorem hasVertexCover_of_listRepresentsVertexCover {I : CliqueInstance}
    {vertices : List Nat} (h : I.ListRepresentsVertexCover vertices) :
    I.HasVertexCover := by
  rcases h with ⟨hnodup, hcard, hbound, hcover⟩
  refine ⟨vertices.toFinset, ?_, ?_, ?_⟩
  · simpa [List.toFinset_card_of_nodup hnodup] using hcard
  · intro v hv
    exact hbound v (List.mem_toFinset.mp hv)
  · intro e he
    rcases hcover e he with hleft | hright
    · exact Or.inl (List.mem_toFinset.mpr hleft)
    · exact Or.inr (List.mem_toFinset.mpr hright)

/-- Every finite-set vertex cover has a duplicate-free list certificate. -/
theorem exists_listRepresentsVertexCover_of_hasVertexCover
    {I : CliqueInstance} (h : I.HasVertexCover) :
    ∃ vertices, I.ListRepresentsVertexCover vertices := by
  rcases h with ⟨vertices, hcard, hbound, hcover⟩
  refine ⟨vertices.toList, vertices.nodup_toList, ?_, ?_, ?_⟩
  · simpa using hcard
  · intro v hv
    exact hbound v (Finset.mem_toList.mp hv)
  · intro e he
    rcases hcover e he with hleft | hright
    · exact Or.inl (Finset.mem_toList.mpr hleft)
    · exact Or.inr (Finset.mem_toList.mpr hright)

/-- List certificates and the mathematical vertex-cover predicate are
equivalent. -/
theorem hasVertexCover_iff_exists_listRepresentsVertexCover
    (I : CliqueInstance) :
    I.HasVertexCover ↔ ∃ vertices, I.ListRepresentsVertexCover vertices := by
  constructor
  · exact exists_listRepresentsVertexCover_of_hasVertexCover
  · rintro ⟨vertices, hvertices⟩
    exact hasVertexCover_of_listRepresentsVertexCover hvertices

end CliqueInstance

end Chapter34
end CLRS
