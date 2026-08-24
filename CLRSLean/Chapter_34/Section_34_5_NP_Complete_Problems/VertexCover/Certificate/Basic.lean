import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Language

/-!
# VERTEX-COVER certificate checker

Certificates reuse the honest general-CLIQUE list-of-vertices encoding.  The
typed predicate records exactly the finite checks required by the textbook
VERTEX-COVER verifier.
-/

namespace CLRS
namespace Chapter34

namespace CliqueInstance

/-- A duplicate-free vertex list represents a cover of size at most the
instance target. -/
def ListRepresentsVertexCover (I : CliqueInstance) (vertices : List Nat) : Prop :=
  vertices.Nodup ∧
    vertices.length ≤ I.targetSize ∧
    (∀ v ∈ vertices, v < I.vertexCount) ∧
    ∀ e ∈ I.edges, e.1 ∈ vertices ∨ e.2 ∈ vertices

/-- The finite list certificate predicate is decidable. -/
instance decidableListRepresentsVertexCover
    (I : CliqueInstance) (vertices : List Nat) :
    Decidable (I.ListRepresentsVertexCover vertices) := by
  unfold ListRepresentsVertexCover
  infer_instance

end CliqueInstance

/-- Total Boolean verifier for a raw certificate and raw VERTEX-COVER
instance. -/
def vertexCoverVerifier
    (certificate input : List VertexCoverSym) : Bool :=
  match decodeVertexCoverInstance input,
      decodeVertexCoverCertificate certificate with
  | some I, some vertices =>
      decide (I.WellFormed ∧ I.ListRepresentsVertexCover vertices)
  | _, _ => false

end Chapter34
end CLRS
