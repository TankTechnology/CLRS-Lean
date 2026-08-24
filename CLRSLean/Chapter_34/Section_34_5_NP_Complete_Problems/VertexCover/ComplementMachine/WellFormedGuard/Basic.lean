import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Basic

/-!
# Graph well-formedness guard: Boolean specification
-/

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.WellFormedGuard

open GeneralCliqueVerifier

/-- Reuse the CLIQUE verifier's target and per-edge passes, omitting every
certificate-specific condition. -/
def wellFormedPass (certificate input : List CliqueSym) : Bool :=
  TargetBound.targetBoundPass certificate input &&
    BaseChecks.graphChecks certificate input

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.WellFormedGuard
