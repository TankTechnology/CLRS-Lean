import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Semantics

/-!
# General CLIQUE verifier: duplicate-check elimination

The adjacency relation is irreflexive.  Consequently, the later-pair
adjacency pass already rejects every repeated certificate vertex.  This lets
the concrete verifier reuse the adjacency controller instead of building a
second quadratic duplicate scanner for certificates.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- Pairwise graph adjacency forces a certificate list to be duplicate-free. -/
theorem nodup_of_pairwise_adj (I : CliqueInstance) {vertices : List Nat}
    (hpairs : vertices.Pairwise I.Adj) : vertices.Nodup := by
  induction vertices with
  | nil => simp
  | cons vertex rest ih =>
      rw [List.pairwise_cons] at hpairs
      rw [List.nodup_cons]
      refine ⟨?_, ih hpairs.2⟩
      intro hmem
      exact I.not_adj_self vertex (hpairs.1 vertex hmem)

/-- The executable pairwise pass subsumes the separate certificate duplicate
pass. -/
theorem pairwiseAdjacencyBool_implies_nodup
    (I : CliqueInstance) {vertices : List Nat}
    (hpairs : pairwiseAdjacencyBool I vertices = true) :
    natListNodupBool vertices = true := by
  rw [natListNodupBool_eq_true_iff]
  exact nodup_of_pairwise_adj I
    ((pairwiseAdjacencyBool_eq_true_iff I vertices).mp hpairs)

/-- Certificate-side checks with duplicate detection delegated to the
pairwise adjacency pass. -/
def vertexAndPairChecksWithoutNodup
    (I : CliqueInstance) (vertices : List Nat) : Bool :=
  decide (vertices.length = I.targetSize) &&
    verticesWithinBool I.vertexCount vertices &&
    pairwiseAdjacencyBool I vertices

/-- Removing the explicit certificate-Nodup Boolean does not change the
combined verifier result. -/
theorem vertexChecks_pairwise_eq_withoutNodup
    (I : CliqueInstance) (vertices : List Nat) :
    (vertexChecks I vertices && pairwiseAdjacencyBool I vertices) =
      vertexAndPairChecksWithoutNodup I vertices := by
  cases hpairs : pairwiseAdjacencyBool I vertices with
  | false =>
      simp [vertexAndPairChecksWithoutNodup, hpairs]
  | true =>
      have hnodup : natListNodupBool vertices = true :=
        pairwiseAdjacencyBool_implies_nodup I hpairs
      simp [vertexChecks, vertexAndPairChecksWithoutNodup, hpairs, hnodup]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
