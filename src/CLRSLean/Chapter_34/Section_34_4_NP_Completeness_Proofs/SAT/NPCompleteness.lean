import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.ReductionVerifier.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Reduction

/-!
# Standalone NP-completeness of raw SAT

The fixed verifier reuses the already verified SAT-to-3-CNF and
3-CNF-to-CLIQUE machines.  The smaller assignment checker remains the direct
semantic certificate interface; this module supplies the machine witness
required by `ClassNP`.
-/

namespace CLRS.Chapter34

/-- Raw SAT has a concrete polynomial-time verifier and a polynomial
certificate bound. -/
theorem SAT_polyTimeVerifiable : PolyTimeVerifiable SAT := by
  refine ⟨satReductionVerifier, satReductionCertificatePolynomial, ?_, ?_⟩
  · exact ⟨Turing.SATVerifier.reductionVerifierComputableInPolyTime⟩
  · exact mem_SAT_iff_exists_reduction_certificate

/-- Raw SAT belongs to NP. -/
theorem SAT_mem_ClassNP : SAT ∈ ClassNP FormulaSym :=
  (mem_ClassNP SAT).2 SAT_polyTimeVerifiable

/-- Raw SAT is NP-complete. -/
theorem SAT_npComplete : NPComplete SAT :=
  ⟨SAT_polyTimeVerifiable, SAT_npHard⟩

end CLRS.Chapter34
