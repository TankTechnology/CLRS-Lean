import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Runtime

/-!
# General CLIQUE verifier: normalized certificate-pair queries

This semantic bridge turns the nested symmetric adjacency scan into two
machine-friendly obligations: distinctness of every later pair, and membership
of every normalized query in the stored edge list.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- Normalize two distinct endpoints to the graph's strict lower/upper order.
Equal endpoints have no valid normalized edge. -/
def normalizeCertificatePair (u v : Nat) : Option (Nat × Nat) :=
  if u < v then some (u, v)
  else if v < u then some (v, u)
  else none

/-- Normalized pairs between one head vertex and every later certificate
vertex; equal endpoints are omitted and separately rejected. -/
def normalizedLaterPairs (u : Nat) (vertices : List Nat) : List (Nat × Nat) :=
  vertices.filterMap (normalizeCertificatePair u)

/-- Row-major list of every normalized unordered certificate pair. -/
def normalizedCertificatePairs : List Nat → List (Nat × Nat)
  | [] => []
  | vertex :: rest =>
      normalizedLaterPairs vertex rest ++ normalizedCertificatePairs rest

/-- Every head/later pair must be distinct before omitted equal pairs can be
soundly replaced by normalized edge queries. -/
def certificatePairsDistinctBool : List Nat → Bool
  | [] => true
  | vertex :: rest =>
      rest.all (fun other => decide (vertex ≠ other)) &&
        certificatePairsDistinctBool rest

/-- Executable membership scan over the normalized certificate queries. -/
def normalizedQueriesInEdgesBool (I : CliqueInstance)
    (vertices : List Nat) : Bool :=
  (normalizedCertificatePairs vertices).all
    (fun edge => decide (edge ∈ I.edges))

/-- One normalized query is present exactly when the original endpoints are
adjacent in the symmetric graph view. -/
theorem normalizeCertificatePair_mem_eq_adjacencyBool
    (I : CliqueInstance) (u v : Nat) :
    (match normalizeCertificatePair u v with
      | some edge => decide (edge ∈ I.edges)
      | none => false) = adjacencyBool I u v := by
  by_cases huv : u < v
  · simp [normalizeCertificatePair, adjacencyBool, huv]
  · by_cases hvu : v < u
    · simp [normalizeCertificatePair, adjacencyBool, huv, hvu]
    · simp [normalizeCertificatePair, adjacencyBool, huv, hvu]

/-- The explicit pair-distinctness scan is list nodup. -/
theorem certificatePairsDistinctBool_eq_true_iff (vertices : List Nat) :
    certificatePairsDistinctBool vertices = true ↔ vertices.Nodup := by
  induction vertices with
  | nil => simp [certificatePairsDistinctBool]
  | cons vertex rest ih =>
      have hnot : (∀ x ∈ rest, vertex ≠ x) ↔ vertex ∉ rest := by
        constructor
        · intro hall hmem
          exact hall vertex hmem rfl
        · intro hnot x hx heq
          subst x
          exact hnot hx
      simp only [certificatePairsDistinctBool, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq, ih, List.nodup_cons]
      exact and_congr hnot Iff.rfl

private theorem later_membership_eq (I : CliqueInstance) (u : Nat)
    (vertices : List Nat) :
    (vertices.all fun v => adjacencyBool I u v) =
      ((vertices.all fun v => decide (u ≠ v)) &&
        (normalizedLaterPairs u vertices).all
          (fun edge => decide (edge ∈ I.edges))) := by
  induction vertices with
  | nil => simp [normalizedLaterPairs]
  | cons vertex rest ih =>
      simp only [List.all_cons]
      rw [ih]
      by_cases heq : u = vertex
      · subst vertex
        simp [normalizedLaterPairs, normalizeCertificatePair,
          adjacencyBool]
      · by_cases huv : u < vertex
        · simp [normalizedLaterPairs, normalizeCertificatePair, adjacencyBool,
            heq, huv, Bool.and_left_comm]
        · have hvu : vertex < u := by omega
          simp [normalizedLaterPairs, normalizeCertificatePair, adjacencyBool,
            heq, huv, hvu, Bool.and_left_comm]

/-- The original nested pairwise adjacency Boolean is exactly a distinctness
check followed by normalized edge-list membership. -/
theorem pairwiseAdjacencyBool_eq_normalized_queries
    (I : CliqueInstance) (vertices : List Nat) :
    pairwiseAdjacencyBool I vertices =
      (certificatePairsDistinctBool vertices &&
        normalizedQueriesInEdgesBool I vertices) := by
  induction vertices with
  | nil => simp [pairwiseAdjacencyBool, certificatePairsDistinctBool,
      normalizedQueriesInEdgesBool, normalizedCertificatePairs]
  | cons vertex rest ih =>
      rw [pairwiseAdjacencyBool, later_membership_eq, ih]
      simp [certificatePairsDistinctBool, normalizedQueriesInEdgesBool,
        normalizedCertificatePairs, List.all_append, Bool.and_assoc,
        Bool.and_comm, Bool.and_left_comm]

/-- At most one normalized query is emitted per unordered position pair. -/
theorem normalizedCertificatePairs_length_le (vertices : List Nat) :
    (normalizedCertificatePairs vertices).length ≤ vertices.length ^ 2 := by
  induction vertices with
  | nil => simp [normalizedCertificatePairs]
  | cons vertex rest ih =>
      have hlater : (normalizedLaterPairs vertex rest).length ≤ rest.length := by
        clear ih
        unfold normalizedLaterPairs
        induction rest with
        | nil => simp
        | cons other rest innerIH =>
            simp only [List.filterMap_cons, List.length_cons]
            cases hpair : normalizeCertificatePair vertex other with
            | none =>
                simp
                omega
            | some pair =>
                simp
                omega
      simp only [normalizedCertificatePairs, List.length_append,
        List.length_cons]
      nlinarith

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
