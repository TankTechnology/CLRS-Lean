import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Length
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-!
# General CLIQUE is in NP

The certificate language is the honest raw graph-plus-`k` encoding.  Its
verifier is a fixed concrete TM2 and its accepted certificates have the
quadratic bound `(n + 1)^2`.
-/

namespace CLRS.Chapter34

/-- The honest general CLIQUE language has a concrete polynomial-time
verifier with quadratically bounded certificates. -/
theorem generalCLIQUE_polyTimeVerifiable :
    PolyTimeVerifiable GeneralCLIQUE := by
  refine ⟨cliqueVerifier, (Polynomial.X + 1) ^ 2, ?_, ?_⟩
  · exact ⟨Turing.GeneralCliqueVerifier.cliqueVerifierComputableInPolyTime⟩
  · intro input
    simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] using
      mem_generalCLIQUE_iff_exists_certificate input

/-- Textbook general CLIQUE belongs to NP. -/
theorem generalCLIQUE_mem_ClassNP : GeneralCLIQUE ∈ ClassNP CliqueSym :=
  (mem_ClassNP GeneralCLIQUE).2 generalCLIQUE_polyTimeVerifiable

end CLRS.Chapter34
