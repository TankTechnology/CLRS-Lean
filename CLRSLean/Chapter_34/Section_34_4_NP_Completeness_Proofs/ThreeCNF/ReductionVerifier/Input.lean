import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.ReductionVerifier.CertificateCodec
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PolynomialRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine

/-!
# Reduction-backed 3-CNF verifier input

The raw 3-CNF certificate is translated symbol by symbol.  The raw formula is
sent through the already verified 3-CNF-to-general-CLIQUE reduction.  Pairing
the two streams gives exactly the input expected by the concrete CLIQUE
verifier.
-/

namespace CLRS.Chapter34

/-- A total 3-CNF verifier obtained by reusing the honest general-CLIQUE
verifier after the concrete textbook reduction. -/
def threeCNFReductionVerifier (certificate input : List CNFSym) : Bool :=
  cliqueVerifier (cnfToCliqueCertificate certificate)
    (threeCNFToGeneralCliqueMap input)

namespace Turing.ThreeCNFVerifier

/-- Semantic input of the reduction-backed verifier. -/
abbrev RawInput := List CNFSym × List CNFSym

/-- Physical input encoding required by `PolyTimeVerifiable`. -/
def rawEncoding (input : RawInput) : List (Option CNFSym) :=
  pairEncoding input.1 input.2

/-- Certificate/instance pair passed to the existing CLIQUE verifier. -/
def reducedCliqueInput (input : RawInput) : List CliqueSym × List CliqueSym :=
  (cnfToCliqueCertificate input.1,
    threeCNFToGeneralCliqueMap input.2)

end Turing.ThreeCNFVerifier
end CLRS.Chapter34
