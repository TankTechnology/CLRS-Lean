import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.PolynomialRuntime

/-!
# General circuit satisfiability is in NP

The executable certificate semantics and the concrete polynomial-time TM2
witness are assembled here into the chapter-level membership theorem.
-/

namespace CLRS.Chapter34

/-- `GeneralCircuitSAT` has polynomial-size assignment certificates checked by
the concrete polynomial-time verifier machine. -/
theorem generalCircuitSAT_polyTimeVerifiable :
    PolyTimeVerifiable GeneralCircuitSAT := by
  refine ⟨generalCircuitVerifier, Polynomial.X, ?_, ?_⟩
  · exact ⟨Turing.GeneralCircuitVerifier.generalCircuitVerifierComputableInPolyTime⟩
  · intro input
    simpa using mem_generalCircuitSAT_iff_exists_certificate input

/-- Public textbook-facing name for polynomial verifiability of general
circuit satisfiability. -/
theorem generalCircuitSAT_verifiable :
    PolyTimeVerifiable GeneralCircuitSAT :=
  generalCircuitSAT_polyTimeVerifiable

/-- The honest serialized general-circuit satisfiability language belongs to
the complexity class `NP`. -/
theorem generalCircuitSAT_mem_ClassNP :
    GeneralCircuitSAT ∈ ClassNP CircuitSym :=
  (mem_ClassNP GeneralCircuitSAT).2 generalCircuitSAT_polyTimeVerifiable

end CLRS.Chapter34
