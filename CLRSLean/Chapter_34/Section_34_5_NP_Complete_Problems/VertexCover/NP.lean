import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.VerifierMachine
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-! # General VERTEX-COVER is in NP -/

namespace CLRS.Chapter34

/-- The honest serialized VERTEX-COVER language has a fixed polynomial-time
verifier and quadratically bounded certificates. -/
theorem generalVERTEXCOVER_polyTimeVerifiable :
    PolyTimeVerifiable GeneralVERTEXCOVER := by
  refine ⟨vertexCoverCliqueVerifier, (Polynomial.X + 1) ^ 2, ?_, ?_⟩
  · exact ⟨Turing.VertexCover.VerifierMachine.computableInPolyTime⟩
  · intro input
    simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] using
      mem_generalVERTEXCOVER_iff_exists_bounded_cliqueCertificate input

/-- Textbook VERTEX-COVER belongs to NP. -/
theorem VERTEXCOVER_mem_ClassNP : VERTEXCOVER ∈ ClassNP VertexCoverSym :=
  (mem_ClassNP VERTEXCOVER).2 generalVERTEXCOVER_polyTimeVerifiable

end CLRS.Chapter34
