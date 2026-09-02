import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CycleAdjacency.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.Semantics

/-!
# HAM-CYCLE verifier: cycle adjacency semantics
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CycleAdjacency

private theorem queriesInEdgesBool_nil (I : CliqueInstance) :
    GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I [] = true := by
  rfl

private theorem queriesInEdgesBool_cons (I : CliqueInstance)
    (query : Nat × Nat) (queries : List (Nat × Nat)) :
    GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I
        (query :: queries) =
      (decide (query ∈ I.edges) &&
        GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I queries) := by
  rfl

private theorem queriesInEdgesBool_append (I : CliqueInstance)
    (left right : List (Nat × Nat)) :
    GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I
        (left ++ right) =
      (GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I left &&
        GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I right) := by
  simp [GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool]

private theorem pathQueries_eq_pathAdjacent (I : CliqueInstance)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2)
    (previous : Nat) (vertices : List Nat) :
    GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I
        ((CyclePairs.pathPairsFrom previous vertices).map
          GeneralCliqueVerifier.QueryNormalizer.normalizeQuery) =
      decide (I.PathAdjacent (previous :: vertices)) := by
  induction vertices generalizing previous with
  | nil =>
      simp [CyclePairs.pathPairsFrom, queriesInEdgesBool_nil,
        CliqueInstance.PathAdjacent]
  | cons current vertices ih =>
      rw [CyclePairs.pathPairsFrom, List.map_cons, queriesInEdgesBool_cons]
      rw [ih current]
      rw [GeneralCliqueVerifier.AdjacencyPipeline.normalizeQuery_mem_eq_adjacencyBool
        I hstrict previous current]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        GeneralCliqueVerifier.adjacencyBool_eq_true_iff,
        CliqueInstance.PathAdjacent]

/-- On a nonempty candidate list, the normalized generated query family is
true exactly when all path and closing edges form a cycle in the graph. -/
theorem generatedCycleQueries_eq_cycleAdjacent (I : CliqueInstance)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2)
    (vertices : List Nat) (hnonempty : vertices ≠ []) :
    GeneralCliqueVerifier.BatchEdgeLookup.queriesInEdgesBool I
        ((CyclePairs.cyclePairs vertices).map
          GeneralCliqueVerifier.QueryNormalizer.normalizeQuery) =
      decide (I.CycleAdjacent vertices) := by
  cases vertices with
  | nil => contradiction
  | cons first rest =>
      rw [CyclePairs.cyclePairs, List.map_append,
        queriesInEdgesBool_append]
      rw [pathQueries_eq_pathAdjacent I hstrict first rest]
      simp only [List.map_singleton]
      rw [queriesInEdgesBool_cons, queriesInEdgesBool_nil, Bool.and_true]
      rw [GeneralCliqueVerifier.AdjacencyPipeline.normalizeQuery_mem_eq_adjacencyBool
        I hstrict (CliqueInstance.lastFrom first rest) first]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        GeneralCliqueVerifier.adjacencyBool_eq_true_iff,
        CliqueInstance.CycleAdjacent]

/-- On canonically decodable strict raw inputs, the total fixed machine's
Boolean agrees exactly with the textbook cycle-adjacency predicate. -/
theorem rawCycleAdjacencyCheck_eq_cycleAdjacent
    (certificate input : List CliqueSym) (I : CliqueInstance)
    (vertices : List Nat)
    (hcertificate : decodeCliqueCertificate certificate = some vertices)
    (hinput : decodeCliqueInstance input = some I)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2)
    (hnonempty : vertices ≠ []) :
    rawCycleAdjacencyCheck (certificate, input) =
      decide (I.CycleAdjacent vertices) := by
  have hcertificateValue :
      GeneralCliqueVerifier.Canonicalizer.certificateValue certificate =
        vertices := by
    simp [GeneralCliqueVerifier.Canonicalizer.certificateValue, hcertificate]
  have hinstanceValue :
      GeneralCliqueVerifier.Canonicalizer.instanceValue input = I := by
    simp [GeneralCliqueVerifier.Canonicalizer.instanceValue, hinput]
  simp only [rawCycleAdjacencyCheck, rawQueries, rawCyclePairs, rawVertices,
    rawInstance, GeneralCliqueVerifier.AdjacencyPipeline.rawVertices,
    GeneralCliqueVerifier.AdjacencyPipeline.rawInstance,
    hcertificateValue, hinstanceValue]
  exact generatedCycleQueries_eq_cycleAdjacent I hstrict vertices hnonempty

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CycleAdjacency
