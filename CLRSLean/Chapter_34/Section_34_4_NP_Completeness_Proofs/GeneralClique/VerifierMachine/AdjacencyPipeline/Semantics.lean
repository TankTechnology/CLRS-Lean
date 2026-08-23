import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairwiseQueries
import Mathlib.Tactic

/-!
# General CLIQUE verifier: generated-query semantics

The concrete pair generator enumerates positions, not distinct vertex values.
Consequently a repeated certificate vertex produces a self-query; strict graph
encodings reject that query.  This is exactly the irreflexive behavior needed
for the textbook pairwise clique condition.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.AdjacencyPipeline

open PairGenerator

/-- Structural property shared by every synthetic certificate occurrence. -/
def SyntheticEntry (entry : IndexedOccurrence × Nat) : Prop :=
  entry.1.positionIndex = 0 ∧ entry.1.literal = .pos 0

/-- Strictly normalized stored edges contain no self-loop. -/
theorem not_mem_self_of_strict_edges (I : CliqueInstance)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2) (vertex : Nat) :
    (vertex, vertex) ∉ I.edges := by
  intro hmem
  have hlt := hstrict (vertex, vertex) hmem
  omega

/-- Direct normalization followed by membership agrees with symmetric
adjacency whenever the stored edge list is strict. -/
theorem normalizeQuery_mem_eq_adjacencyBool (I : CliqueInstance)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2) (u v : Nat) :
    decide (QueryNormalizer.normalizeQuery (u, v) ∈ I.edges) =
      adjacencyBool I u v := by
  by_cases huv : u < v
  · simp [QueryNormalizer.normalizeQuery, adjacencyBool, huv,
      Nat.le_of_lt huv]
  · by_cases hvu : v < u
    · have hnle : ¬ u ≤ v := by omega
      simp [QueryNormalizer.normalizeQuery, adjacencyBool, huv, hvu, hnle]
    · have heq : u = v := by omega
      subst v
      have hself := not_mem_self_of_strict_edges I hstrict u
      simp [QueryNormalizer.normalizeQuery, adjacencyBool, hself]

theorem normalizeQuery_mem_iff_adj (I : CliqueInstance)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2) (u v : Nat) :
    QueryNormalizer.normalizeQuery (u, v) ∈ I.edges ↔ I.Adj u v := by
  have heq := normalizeQuery_mem_eq_adjacencyBool I hstrict u v
  apply Bool.eq_iff_iff.mp at heq
  simpa only [decide_eq_true_eq, adjacencyBool_eq_true_iff] using heq

/-- Boolean adjacency is symmetric. -/
theorem adjacencyBool_comm (I : CliqueInstance) (u v : Nat) :
    adjacencyBool I u v = adjacencyBool I v u := by
  apply Bool.eq_iff_iff.mpr
  simp only [adjacencyBool_eq_true_iff]
  exact I.adj_comm u v

/-- Two synthetic rows with distinct positional indices always generate their
underlying vertex pair. -/
theorem compatibleOccurrencePair_synthetic
    (current prior : IndexedOccurrence × Nat)
    (hcurrent : SyntheticEntry current) (hprior : SyntheticEntry prior)
    (hne : prior.1.clauseIndex ≠ current.1.clauseIndex) :
    compatibleOccurrencePair current prior = [(prior.2, current.2)] := by
  rcases current with ⟨⟨currentClause, currentPosition, currentLiteral⟩,
    currentVertex⟩
  rcases prior with ⟨⟨priorClause, priorPosition, priorLiteral⟩,
    priorVertex⟩
  simp only [SyntheticEntry] at hcurrent hprior
  rcases hcurrent with ⟨rfl, rfl⟩
  rcases hprior with ⟨rfl, rfl⟩
  simp [compatibleOccurrencePair,
    TMClique.indexedOccurrencesCompatibleCode,
    TMClique.occurrenceRowsCompatibleCode,
    TMClique.occurrencePolarityFlag, TMClique.occurrenceVariableCode, hne]

/-- Under the same positional hypotheses, one outer iteration emits every
prior/current vertex pair exactly once. -/
theorem compatibleOccurrencePairs_synthetic
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat))
    (hcurrent : SyntheticEntry current)
    (hpriors : ∀ prior ∈ priors, SyntheticEntry prior)
    (hne : ∀ prior ∈ priors,
      prior.1.clauseIndex ≠ current.1.clauseIndex) :
    compatibleOccurrencePairs current priors =
      priors.map fun prior => (prior.2, current.2) := by
  induction priors with
  | nil => rfl
  | cons prior priors ih =>
      simp only [compatibleOccurrencePairs, List.flatMap_cons, List.map_cons]
      rw [compatibleOccurrencePair_synthetic current prior hcurrent
        (hpriors prior (by simp)) (hne prior (by simp))]
      simp only [List.singleton_append, List.cons.injEq, true_and]
      exact ih (fun candidate hcandidate =>
        hpriors candidate (by simp [hcandidate]))
        (fun candidate hcandidate => hne candidate (by simp [hcandidate]))

/-- All generated queries decide pairwise adjacency for a synthetic row list
whose positional indices are duplicate-free. -/
theorem generatedQueries_eq_pairwise (I : CliqueInstance)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2)
    (entries : List (IndexedOccurrence × Nat))
    (hsynthetic : ∀ entry ∈ entries, SyntheticEntry entry)
    (hnodup : (entries.map fun entry => entry.1.clauseIndex).Nodup) :
    BatchEdgeLookup.queriesInEdgesBool I
        ((compatibleOccurrencePairIterations entries).map
          QueryNormalizer.normalizeQuery) =
      pairwiseAdjacencyBool I (entries.map Prod.snd) := by
  induction entries with
  | nil => simp [compatibleOccurrencePairIterations,
      BatchEdgeLookup.queriesInEdgesBool, pairwiseAdjacencyBool]
  | cons current priors ih =>
      have hcurrent : SyntheticEntry current :=
        hsynthetic current (by simp)
      have hpriors : ∀ prior ∈ priors, SyntheticEntry prior := by
        intro prior hprior
        exact hsynthetic prior (by simp [hprior])
      have hnodupTail :
          (priors.map fun entry => entry.1.clauseIndex).Nodup := by
        simpa using hnodup.tail
      have hcurrentNotMem : current.1.clauseIndex ∉
          priors.map fun entry => entry.1.clauseIndex := by
        simpa using hnodup.notMem
      have hne : ∀ prior ∈ priors,
          prior.1.clauseIndex ≠ current.1.clauseIndex := by
        intro prior hprior heq
        apply hcurrentNotMem
        exact List.mem_map.mpr ⟨prior, hprior, heq⟩
      have hiteration := compatibleOccurrencePairs_synthetic current
        priors.reverse hcurrent
        (fun prior hprior => hpriors prior (by simpa using hprior))
        (fun prior hprior => hne prior (by simpa using hprior))
      rw [compatibleOccurrencePairIterations, List.map_append,
        BatchEdgeLookup.queriesInEdgesBool, List.all_append]
      change (BatchEdgeLookup.queriesInEdgesBool I
          ((compatibleOccurrencePairIterations priors).map
            QueryNormalizer.normalizeQuery) && _) = _
      rw [ih hpriors hnodupTail, hiteration, List.map_map, List.all_map,
        List.all_reverse]
      simp only [pairwiseAdjacencyBool, List.map_cons]
      rw [Bool.and_comm (pairwiseAdjacencyBool I (priors.map Prod.snd))]
      congr 1
      rw [List.all_map]
      apply List.all_congr rfl
      intro prior
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, adjacencyBool_eq_true_iff]
      exact (normalizeQuery_mem_iff_adj I hstrict prior.2 current.2).trans
        (I.adj_comm prior.2 current.2)

private theorem entriesFrom_map_snd (position : Nat)
    (vertices : List Nat) :
    (certificatePairEntriesFrom position vertices).map Prod.snd = vertices := by
  induction vertices generalizing position with
  | nil => rfl
  | cons vertex vertices ih =>
      simp [certificatePairEntriesFrom, ih]

private theorem entriesFrom_map_clause (position : Nat)
    (vertices : List Nat) :
    (certificatePairEntriesFrom position vertices).map
        (fun entry => entry.1.clauseIndex) =
      List.range' position vertices.length := by
  induction vertices generalizing position with
  | nil => simp
  | cons vertex vertices ih =>
      simp only [certificatePairEntriesFrom, List.map_cons,
        certificatePairOccurrence, List.length_cons]
      rw [ih, List.range'_succ]

private theorem entriesFrom_synthetic (position : Nat)
    (vertices : List Nat) :
    ∀ entry ∈ certificatePairEntriesFrom position vertices,
      SyntheticEntry entry := by
  intro entry hentry
  induction vertices generalizing position with
  | nil => simp at hentry
  | cons vertex vertices ih =>
      simp only [certificatePairEntriesFrom, List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp [SyntheticEntry, certificatePairOccurrence]
      · exact ih (position + 1) hentry

/-- The concrete generated query family has exactly the pairwise-adjacency
Boolean semantics on every strict graph instance. -/
theorem generatedCertificateQueries_eq_pairwise (I : CliqueInstance)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2)
    (vertices : List Nat) :
    BatchEdgeLookup.queriesInEdgesBool I
        (QueryNormalizer.normalizedCertificatePairs vertices) =
      pairwiseAdjacencyBool I vertices := by
  have hgenerated := generatedQueries_eq_pairwise I hstrict
    (certificatePairEntries vertices).reverse
  have hsynthetic : ∀ entry ∈ (certificatePairEntries vertices).reverse,
      SyntheticEntry entry := by
    intro entry hentry
    apply entriesFrom_synthetic 0 vertices entry
    simpa [certificatePairEntries] using hentry
  have hnodup :
      ((certificatePairEntries vertices).reverse.map
        fun entry => entry.1.clauseIndex).Nodup := by
    rw [List.map_reverse, certificatePairEntries]
    rw [entriesFrom_map_clause]
    exact (List.nodup_reverse).2
      (List.nodup_range' (s := 0) (n := vertices.length))
  specialize hgenerated hsynthetic hnodup
  have hvertices :
      (certificatePairEntries vertices).reverse.map Prod.snd =
        vertices.reverse := by
    rw [List.map_reverse, certificatePairEntries, entriesFrom_map_snd]
  rw [hvertices] at hgenerated
  change BatchEdgeLookup.queriesInEdgesBool I
      ((compatibleOccurrencePairIterations
        (certificatePairEntries vertices).reverse).map
          QueryNormalizer.normalizeQuery) =
    pairwiseAdjacencyBool I vertices
  rw [hgenerated]
  apply Bool.eq_iff_iff.mpr
  simp only [pairwiseAdjacencyBool_eq_true_iff, List.pairwise_reverse]
  constructor
  · intro hpairs
    exact hpairs.imp fun {_ _} huv => (I.adj_comm _ _).mpr huv
  · intro hpairs
    exact hpairs.imp fun {_ _} huv => (I.adj_comm _ _).mp huv

/-- On canonically decodable raw inputs satisfying strict edge order, the
total raw adjacency machine agrees with the typed textbook check. -/
theorem rawAdjacencyCheck_eq_pairwise
    (certificate input : List CliqueSym) (I : CliqueInstance)
    (vertices : List Nat)
    (hcertificate : decodeCliqueCertificate certificate = some vertices)
    (hinput : decodeCliqueInstance input = some I)
    (hstrict : ∀ edge ∈ I.edges, edge.1 < edge.2) :
    rawAdjacencyCheck (certificate, input) =
      pairwiseAdjacencyBool I vertices := by
  have hcertificateValue : Canonicalizer.certificateValue certificate =
      vertices := by simp [Canonicalizer.certificateValue, hcertificate]
  have hinstanceValue : Canonicalizer.instanceValue input = I := by
    simp [Canonicalizer.instanceValue, hinput]
  simp only [rawAdjacencyCheck, rawQueries, rawVertices, rawInstance,
    hcertificateValue, hinstanceValue]
  exact generatedCertificateQueries_eq_pairwise I hstrict vertices

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.AdjacencyPipeline
