import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.ReductionVerifier.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Completeness

/-!
# Standalone NP-completeness of raw 3-CNF-SAT

This packaging uses a concrete verifier obtained by composing the verified
3-CNF-to-general-CLIQUE reduction with the verified general-CLIQUE verifier.
The assignment checker remains available as a smaller semantic interface;
the theorem here supplies the fixed-machine witness required by `ClassNP`.
-/

namespace CLRS.Chapter34

/-- Raw 3-CNF-SAT has a concrete polynomial-time verifier and a polynomial
certificate bound. -/
theorem threeCNFSat_polyTimeVerifiable :
    PolyTimeVerifiable ThreeCNFSat := by
  refine ⟨threeCNFReductionVerifier,
    threeCNFReductionCertificatePolynomial, ?_, ?_⟩
  · exact ⟨Turing.ThreeCNFVerifier.reductionVerifierComputableInPolyTime⟩
  · exact mem_threeCNFSat_iff_exists_reduction_certificate

/-- Raw 3-CNF-SAT belongs to NP. -/
theorem threeCNFSat_mem_ClassNP : ThreeCNFSat ∈ ClassNP CNFSym :=
  (mem_ClassNP ThreeCNFSat).2 threeCNFSat_polyTimeVerifiable

/-- Raw 3-CNF-SAT is NP-complete. -/
theorem threeCNFSat_npComplete : NPComplete ThreeCNFSat :=
  ⟨threeCNFSat_polyTimeVerifiable, threeCNFSat_npHard⟩

end CLRS.Chapter34
