import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.VertexChecks

/-!
# General CLIQUE verifier: graph and pair checks

This module gives explicit Boolean scans for instance well-formedness and for
all unordered pairs in a certificate.  Their exact propositions are the graph
side of `cliqueVerifier`.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- Executable duplicate check for clients that require a canonical edge-list
serialization.  Textbook CLIQUE semantics itself is insensitive to repeated
edge records. -/
def edgeListNodupBool : List (Nat × Nat) → Bool
  | [] => true
  | edge :: rest => decide (edge ∉ rest) && edgeListNodupBool rest

/-- Exact semantics of the edge duplicate scan. -/
@[simp] theorem edgeListNodupBool_eq_true_iff (edges : List (Nat × Nat)) :
    edgeListNodupBool edges = true ↔ edges.Nodup := by
  induction edges with
  | nil => simp [edgeListNodupBool]
  | cons edge rest ih =>
      simp [edgeListNodupBool, ih, List.nodup_cons]

/-- Check normalization and endpoint range for every stored edge. -/
def edgeBoundsBool (vertexCount : Nat) (edges : List (Nat × Nat)) : Bool :=
  edges.all fun edge =>
    decide (edge.1 < edge.2) && decide (edge.2 < vertexCount)

/-- Exact semantics of the edge normalization/range pass. -/
@[simp] theorem edgeBoundsBool_eq_true_iff
    (vertexCount : Nat) (edges : List (Nat × Nat)) :
    edgeBoundsBool vertexCount edges = true ↔
      ∀ edge ∈ edges, edge.1 < edge.2 ∧ edge.2 < vertexCount := by
  simp [edgeBoundsBool]

/-- Boolean factorization of the complete instance well-formedness check. -/
def instanceWellFormedBool (I : CliqueInstance) : Bool :=
  decide (I.targetSize ≤ I.vertexCount) &&
    edgeBoundsBool I.vertexCount I.edges

/-- The factored graph scan is exactly `CliqueInstance.WellFormed`. -/
theorem instanceWellFormedBool_eq_true_iff (I : CliqueInstance) :
    instanceWellFormedBool I = true ↔ I.WellFormed := by
  simp [instanceWellFormedBool, CliqueInstance.WellFormed]

/-- Symmetric lookup of one unordered pair in the normalized edge list. -/
def adjacencyBool (I : CliqueInstance) (u v : Nat) : Bool :=
  if u < v then decide ((u, v) ∈ I.edges)
  else if v < u then decide ((v, u) ∈ I.edges)
  else false

/-- Exact semantics of one Boolean adjacency lookup. -/
@[simp] theorem adjacencyBool_eq_true_iff (I : CliqueInstance) (u v : Nat) :
    adjacencyBool I u v = true ↔ I.Adj u v := by
  by_cases huv : u < v
  · simp [adjacencyBool, CliqueInstance.Adj, huv]
  · by_cases hvu : v < u
    · simp [adjacencyBool, CliqueInstance.Adj, huv, hvu]
    · simp [adjacencyBool, CliqueInstance.Adj, huv, hvu]

/-- Check each head vertex against every later vertex, then recurse. -/
def pairwiseAdjacencyBool (I : CliqueInstance) : List Nat → Bool
  | [] => true
  | vertex :: rest =>
      rest.all (adjacencyBool I vertex) && pairwiseAdjacencyBool I rest

/-- The nested Boolean pair scan is exactly list pairwiseness. -/
@[simp] theorem pairwiseAdjacencyBool_eq_true_iff
    (I : CliqueInstance) (vertices : List Nat) :
    pairwiseAdjacencyBool I vertices = true ↔ vertices.Pairwise I.Adj := by
  induction vertices with
  | nil => simp [pairwiseAdjacencyBool]
  | cons vertex rest ih =>
      simp [pairwiseAdjacencyBool, ih]

/-- On a duplicate-free certificate, checking later occurrences is equivalent
to the textbook quantification over every two distinct selected vertices. -/
theorem pairwise_adj_iff_all_distinct (I : CliqueInstance)
    {vertices : List Nat} (hnodup : vertices.Nodup) :
    vertices.Pairwise I.Adj ↔
      ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v → I.Adj u v := by
  letI : Std.Symm I.Adj :=
    ⟨fun u v huv => (I.adj_comm u v).mp huv⟩
  constructor
  · intro hpairs
    exact hpairs.forall
  · intro hall
    induction vertices with
    | nil => simp
    | cons vertex rest ih =>
        rw [List.pairwise_cons]
        constructor
        · intro other hother
          exact hall vertex (by simp) other (by simp [hother])
            (by
              intro heq
              subst other
              exact hnodup.notMem hother)
        · exact ih hnodup.tail (by
            intro u hu v hv huv
            exact hall u (by simp [hu]) v (by simp [hv]) huv)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
