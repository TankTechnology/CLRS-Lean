import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairChecks

/-!
# General CLIQUE verifier: complete edge-bound bridge

The two concrete passes jointly implement the normalization and endpoint-range
conjunct of instance well-formedness.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- Concrete Boolean factorization of all per-edge encoding bounds. -/
def concreteEdgeBoundsPass (certificate input : List CliqueSym) : Bool :=
  EdgeOrder.edgeOrderPass certificate input &&
    EndpointBound.endpointBoundPass certificate input

/-- On canonical instances, the two concrete passes are exactly the typed
{name}`edgeBoundsBool` scan. -/
theorem concreteEdgeBoundsPass_encode_eq (certificate : List CliqueSym)
    (I : CliqueInstance) :
    concreteEdgeBoundsPass certificate (encodeCliqueInstance I) =
      edgeBoundsBool I.vertexCount I.edges := by
  apply Bool.eq_iff_iff.mpr
  simp only [concreteEdgeBoundsPass, Bool.and_eq_true,
    EdgeOrder.edgeOrderPass_encode_iff,
    EndpointBound.endpointBoundPass_encode_iff,
    edgeBoundsBool_eq_true_iff]
  constructor
  · rintro ⟨horder, hrange⟩ edge hedge
    exact ⟨horder edge hedge, hrange edge hedge⟩
  · intro hbounds
    exact ⟨fun edge hedge => (hbounds edge hedge).1,
      fun edge hedge => (hbounds edge hedge).2⟩

/-- Acceptance form of the complete per-edge condition. -/
theorem concreteEdgeBoundsPass_encode_iff (certificate : List CliqueSym)
    (I : CliqueInstance) :
    concreteEdgeBoundsPass certificate (encodeCliqueInstance I) = true ↔
      ∀ edge ∈ I.edges,
        edge.1 < edge.2 ∧ edge.2 < I.vertexCount := by
  rw [concreteEdgeBoundsPass_encode_eq]
  exact edgeBoundsBool_eq_true_iff I.vertexCount I.edges

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
