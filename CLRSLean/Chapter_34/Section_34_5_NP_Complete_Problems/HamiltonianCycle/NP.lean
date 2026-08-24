import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Certificate.Length
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-! # General HAM-CYCLE is in NP -/

namespace CLRS.Chapter34

/-- The honest serialized HAM-CYCLE language has a fixed polynomial-time
verifier and quadratically bounded ordered-cycle certificates. -/
theorem generalHAMCYCLE_polyTimeVerifiable :
    PolyTimeVerifiable GeneralHAMCYCLE := by
  refine ⟨hamiltonianCycleVerifier, (Polynomial.X + 1) ^ 2, ?_, ?_⟩
  · exact ⟨Turing.HamiltonianCycle.VerifierMachine.computableInPolyTime⟩
  · intro input
    constructor
    · intro hmem
      rcases (mem_generalHAMCYCLE_iff_exists_bounded_certificate input).1 hmem
        with ⟨certificate, hlength, hverify⟩
      refine ⟨certificate, ?_, hverify⟩
      simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] using
        hlength
    · rintro ⟨certificate, hlength, hverify⟩
      exact (mem_generalHAMCYCLE_iff_exists_bounded_certificate input).2
        ⟨certificate, by
          simpa [Polynomial.eval_add, Polynomial.eval_pow,
            Polynomial.eval_X] using hlength, hverify⟩

/-- Textbook HAM-CYCLE belongs to NP. -/
theorem HAMCYCLE_mem_ClassNP : HAMCYCLE ∈ ClassNP HamiltonianCycleSym :=
  (mem_ClassNP HAMCYCLE).2 generalHAMCYCLE_polyTimeVerifiable

end CLRS.Chapter34
