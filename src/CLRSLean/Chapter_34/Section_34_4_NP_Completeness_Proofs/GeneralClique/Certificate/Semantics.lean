import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Basic

/-!
# Exact semantics of general CLIQUE certificates

The Boolean checker is characterized on every raw input.  The list predicate
is then connected in both directions to the finite-set clique semantics.
-/

namespace CLRS
namespace Chapter34

/-- Exact all-input truth theorem for the Boolean CLIQUE checker. -/
theorem cliqueVerifier_eq_true_iff (certificate input : List CliqueSym) :
    cliqueVerifier certificate input = true ↔
      ∃ I vertices,
        decodeCliqueInstance input = some I ∧
        decodeCliqueCertificate certificate = some vertices ∧
        I.WellFormed ∧ I.ListRepresentsClique vertices := by
  generalize hinput : decodeCliqueInstance input = instanceResult
  generalize hcertificate : decodeCliqueCertificate certificate = certificateResult
  cases instanceResult <;> cases certificateResult <;>
    simp [cliqueVerifier, hinput, hcertificate]

namespace CliqueInstance

/-- A duplicate-free list certificate induces the corresponding finite-set
clique witness. -/
theorem hasClique_of_listRepresentsClique {I : CliqueInstance}
    {vertices : List Nat} (h : I.ListRepresentsClique vertices) : I.HasClique := by
  rcases h with ⟨hnodup, hcard, hbound, hadj⟩
  refine ⟨vertices.toFinset, ?_, ?_, ?_⟩
  · simpa [List.toFinset_card_of_nodup hnodup] using hcard
  · intro v hv
    exact hbound v (List.mem_toFinset.mp hv)
  · intro u hu v hv huv
    exact hadj u (List.mem_toFinset.mp hu) v (List.mem_toFinset.mp hv) huv

/-- Every finite-set clique has a duplicate-free list certificate. -/
theorem exists_listRepresentsClique_of_hasClique {I : CliqueInstance}
    (h : I.HasClique) : ∃ vertices, I.ListRepresentsClique vertices := by
  rcases h with ⟨vertices, hcard, hbound, hadj⟩
  refine ⟨vertices.toList, vertices.nodup_toList, ?_, ?_, ?_⟩
  · simpa using hcard
  · intro v hv
    exact hbound v (Finset.mem_toList.mp hv)
  · intro u hu v hv huv
    exact hadj u (Finset.mem_toList.mp hu) v (Finset.mem_toList.mp hv) huv

/-- List certificates and the mathematical clique predicate are equivalent. -/
theorem hasClique_iff_exists_listRepresentsClique (I : CliqueInstance) :
    I.HasClique ↔ ∃ vertices, I.ListRepresentsClique vertices := by
  constructor
  · exact exists_listRepresentsClique_of_hasClique
  · rintro ⟨vertices, hvertices⟩
    exact hasClique_of_listRepresentsClique hvertices

end CliqueInstance

end Chapter34
end CLRS
