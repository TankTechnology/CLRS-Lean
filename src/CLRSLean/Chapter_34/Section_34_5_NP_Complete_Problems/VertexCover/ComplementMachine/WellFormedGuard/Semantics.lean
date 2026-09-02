import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.WellFormedGuard.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Semantics

/-!
# Graph well-formedness guard: canonical semantics
-/

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.WellFormedGuard

open GeneralCliqueVerifier

/-- On a canonical graph encoding, the three reused machine passes are exactly
the shared typed graph well-formedness predicate. -/
theorem wellFormedPass_encode_iff (certificate : List CliqueSym)
    (I : CliqueInstance) :
    wellFormedPass certificate (encodeCliqueInstance I) = true ↔
      I.WellFormed := by
  simp only [wellFormedPass, BaseChecks.graphChecks, Bool.and_eq_true,
    TargetBound.targetBoundPass_encode_iff,
    EdgeOrder.edgeOrderPass_encode_iff,
    EndpointBound.endpointBoundPass_encode_iff,
    CliqueInstance.WellFormed]
  constructor
  · rintro ⟨htarget, horder, hendpoint⟩
    exact ⟨htarget, fun edge hedge =>
      ⟨horder edge hedge, hendpoint edge hedge⟩⟩
  · rintro ⟨htarget, hedges⟩
    exact ⟨htarget, (fun edge hedge => (hedges edge hedge).1),
      fun edge hedge => (hedges edge hedge).2⟩

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.WellFormedGuard
