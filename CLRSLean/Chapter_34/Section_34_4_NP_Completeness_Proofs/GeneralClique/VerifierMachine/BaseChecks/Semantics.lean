import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.CertificateRange.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EndpointBound.Canonical

/-!
# General CLIQUE verifier: semantics of the concrete base-check machine

This identifies exactly which textbook conditions are already decided by the
composed machine.  It also makes the remaining proof boundary explicit:
duplicate-free graph edges and certificate pairwise adjacency.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BaseChecks

/-- The typed conditions covered by the six completed concrete passes. -/
def BaseConditions (I : CliqueInstance) (vertices : List Nat) : Prop :=
  vertices.length = I.targetSize ∧
    I.targetSize ≤ I.vertexCount ∧
    (∀ vertex ∈ vertices, vertex < I.vertexCount) ∧
    ∀ edge ∈ I.edges,
      edge.1 < edge.2 ∧ edge.2 < I.vertexCount

/-- On canonical encodings, the concrete base machine accepts exactly the
typed conditions in `BaseConditions`. -/
theorem baseChecks_encode_iff (I : CliqueInstance) (vertices : List Nat) :
    baseChecks (encodeCliqueCertificate vertices)
        (encodeCliqueInstance I) = true ↔
      BaseConditions I vertices := by
  have hsyntax :
      SyntaxPass.syntaxPass (encodeCliqueCertificate vertices)
          (encodeCliqueInstance I) = true :=
    (SyntaxPass.syntaxPass_eq_true_iff _ _).2
      ⟨⟨vertices, decode_encodeCliqueCertificate vertices⟩,
        ⟨I, decode_encodeCliqueInstance I⟩⟩
  simp only [baseChecks, typedBaseChecks, certificateChecks,
    cardinalityAndTarget, graphChecks, Bool.and_eq_true, hsyntax,
    true_and, Cardinality.cardinalityPass_encode_iff,
    TargetBound.targetBoundPass_encode_iff,
    CertificateRange.certificateRangePass_encode_iff,
    EdgeOrder.edgeOrderPass_encode_iff,
    EndpointBound.endpointBoundPass_encode_iff, BaseConditions]
  constructor
  · rintro ⟨⟨⟨hlength, htarget⟩, hrange⟩, horder, hbound⟩
    exact ⟨hlength, htarget, hrange, fun ⟨left, right⟩ hedge =>
      ⟨horder (left, right) hedge, hbound (left, right) hedge⟩⟩
  · rintro ⟨hlength, htarget, hrange, hedges⟩
    exact ⟨⟨⟨hlength, htarget⟩, hrange⟩,
      (fun edge hedge => (hedges edge hedge).1),
      fun edge hedge => (hedges edge hedge).2⟩

/-- The complete typed verifier differs from the completed base checks by
exactly edge uniqueness and pairwise certificate adjacency.  Certificate
uniqueness follows from irreflexive adjacency and therefore needs no separate
machine. -/
theorem baseConditions_complete_iff (I : CliqueInstance)
    (vertices : List Nat) :
    BaseConditions I vertices ∧ I.edges.Nodup ∧
        vertices.Pairwise I.Adj ↔
      I.WellFormed ∧ I.ListRepresentsClique vertices := by
  simp only [BaseConditions, CliqueInstance.WellFormed,
    CliqueInstance.ListRepresentsClique]
  constructor
  · rintro ⟨⟨hlength, htarget, hrange, hedges⟩, hnodupEdges, hpairs⟩
    have hnodupVertices : vertices.Nodup := by
      letI : Std.Irrefl I.Adj := ⟨I.not_adj_self⟩
      exact hpairs.nodup
    refine ⟨⟨htarget, hnodupEdges, hedges⟩,
      hnodupVertices, hlength, hrange, ?_⟩
    exact (pairwise_adj_iff_all_distinct I hnodupVertices).mp hpairs
  · rintro ⟨⟨htarget, hnodupEdges, hedges⟩,
      hnodupVertices, hlength, hrange, hall⟩
    exact ⟨⟨hlength, htarget, hrange, hedges⟩, hnodupEdges,
      (pairwise_adj_iff_all_distinct I hnodupVertices).mpr hall⟩

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BaseChecks
