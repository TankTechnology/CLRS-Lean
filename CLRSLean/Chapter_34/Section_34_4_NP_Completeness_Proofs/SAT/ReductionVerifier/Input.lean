import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.ReductionVerifier.ReductionMap

/-! # Reduction-backed SAT verifier input -/

namespace CLRS.Chapter34

/-- A total SAT verifier obtained by composing the concrete SAT-to-3-CNF map
with the fixed reduction-backed 3-CNF verifier. -/
def satReductionVerifier (certificate input : List FormulaSym) : Bool :=
  threeCNFReductionVerifier (formulaToCNFCertificate certificate)
    (satToThreeCNFMap input)

namespace Turing.SATVerifier

abbrev RawInput := List FormulaSym × List FormulaSym

def rawEncoding (input : RawInput) : List (Option FormulaSym) :=
  pairEncoding input.1 input.2

def reducedThreeCNFInput (input : RawInput) : List CNFSym × List CNFSym :=
  (formulaToCNFCertificate input.1, satToThreeCNFMap input.2)

end Turing.SATVerifier
end CLRS.Chapter34
