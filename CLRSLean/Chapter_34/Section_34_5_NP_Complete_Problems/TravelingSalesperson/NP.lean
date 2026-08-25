import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Certificate.UnaryLength
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-! # General decision-TSP is in NP -/

namespace CLRS.Chapter34

/-- The honest serialized decision-TSP language has a fixed polynomial-time
verifier and quadratically bounded unary ordered-tour certificates. -/
theorem generalTSP_polyTimeVerifiable :
    PolyTimeVerifiable GeneralTSP := by
  refine ⟨fun certificate input =>
      Turing.TSPVerifier.Final.concreteTSPVerifier (certificate, input),
    (Polynomial.X + 1) ^ 2, ?_, ?_⟩
  · exact ⟨Turing.TSPVerifier.Final.computableInPolyTime⟩
  · intro input
    simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] using
      mem_generalTSP_iff_exists_bounded_unary_certificate input

/-- Textbook decision-TSP belongs to NP. -/
theorem TSP_mem_ClassNP : TSP ∈ ClassNP TSPSym :=
  (mem_ClassNP TSP).2 generalTSP_polyTimeVerifiable

end CLRS.Chapter34
