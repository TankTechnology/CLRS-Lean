import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.ParseSemantics

/-!
# General CLIQUE verifier: certificate vertex checks

This module factors the non-adjacency part of the typed certificate predicate
into explicit Boolean scans.  The definitions mirror the bounded passes used
by the concrete verifier: duplicate detection, exact cardinality, and unary
range checks.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

/-- Executable duplicate check, written as a head-against-tail scan followed
by the recursive suffix check. -/
def natListNodupBool : List Nat → Bool
  | [] => true
  | vertex :: rest => decide (vertex ∉ rest) && natListNodupBool rest

/-- Exact semantics of the executable duplicate scan. -/
@[simp] theorem natListNodupBool_eq_true_iff (vertices : List Nat) :
    natListNodupBool vertices = true ↔ vertices.Nodup := by
  induction vertices with
  | nil => simp [natListNodupBool]
  | cons vertex rest ih =>
      simp [natListNodupBool, ih, List.nodup_cons]

/-- Check that every selected vertex is below the encoded vertex count. -/
def verticesWithinBool (vertexCount : Nat) (vertices : List Nat) : Bool :=
  vertices.all fun vertex => decide (vertex < vertexCount)

/-- Exact semantics of the certificate range pass. -/
@[simp] theorem verticesWithinBool_eq_true_iff
    (vertexCount : Nat) (vertices : List Nat) :
    verticesWithinBool vertexCount vertices = true ↔
      ∀ vertex ∈ vertices, vertex < vertexCount := by
  simp [verticesWithinBool]

/-- The certificate conditions independent of graph adjacency. -/
def VertexSideConditions (I : CliqueInstance) (vertices : List Nat) : Prop :=
  vertices.Nodup ∧
    vertices.length = I.targetSize ∧
    ∀ vertex ∈ vertices, vertex < I.vertexCount

/-- Boolean implementation of duplicate, cardinality, and range checks. -/
def vertexChecks (I : CliqueInstance) (vertices : List Nat) : Bool :=
  natListNodupBool vertices &&
    decide (vertices.length = I.targetSize) &&
    verticesWithinBool I.vertexCount vertices

/-- The three explicit Boolean passes are exactly the corresponding typed
certificate conditions. -/
theorem vertexChecks_eq_true_iff (I : CliqueInstance) (vertices : List Nat) :
    vertexChecks I vertices = true ↔ VertexSideConditions I vertices := by
  simp [vertexChecks, VertexSideConditions, and_assoc]

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
