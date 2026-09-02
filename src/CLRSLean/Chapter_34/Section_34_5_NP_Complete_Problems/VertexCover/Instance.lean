import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding

/-!
# VERTEX-COVER instances on the shared graph-plus-k representation

The textbook CLIQUE and VERTEX-COVER decision problems consume the same raw
kind of instance: a finite undirected graph and a natural-number target.  This
module therefore reuses the honest general-CLIQUE representation and gives it
VERTEX-COVER-facing aliases and semantics.

Main definitions:

- `VertexCoverInstance`: the shared graph-plus-target instance type.
- `CliqueInstance.IsVertexCover`: a bounded finite set meeting every edge.
- `CliqueInstance.HasVertexCover`: existence of a cover of size at most the
  encoded target.

Current gaps:

- The complement reduction is proved in the following modules.
- Raw language, verifier, and concrete polynomial-time reduction remain later
  closure layers.
-/

namespace CLRS
namespace Chapter34

/-! ## Shared representation aliases -/

/-- VERTEX-COVER uses the same honest graph-plus-target instance structure as
general CLIQUE. -/
abbrev VertexCoverInstance := CliqueInstance

/-- VERTEX-COVER uses the existing unambiguous graph-plus-target alphabet. -/
abbrev VertexCoverSym := CliqueSym

/-- VERTEX-COVER-facing name for the shared graph-instance encoder. -/
abbrev encodeVertexCoverInstance := encodeCliqueInstance

/-- VERTEX-COVER-facing name for the shared complete graph-instance parser. -/
abbrev decodeVertexCoverInstance := decodeCliqueInstance

/-- VERTEX-COVER-facing name for the shared list-of-vertices certificate
encoder. -/
abbrev encodeVertexCoverCertificate := encodeCliqueCertificate

/-- VERTEX-COVER-facing name for the shared complete certificate parser. -/
abbrev decodeVertexCoverCertificate := decodeCliqueCertificate

namespace CliqueInstance

/-! ## Typed cover semantics -/

/-- A finite set is a vertex cover when all of its vertices are in range and
it contains at least one endpoint of every stored graph edge. -/
def IsVertexCover (I : CliqueInstance) (vertices : Finset Nat) : Prop :=
  (∀ v ∈ vertices, v < I.vertexCount) ∧
    ∀ e ∈ I.edges, e.1 ∈ vertices ∨ e.2 ∈ vertices

/-- A graph-plus-`k` instance is a VERTEX-COVER yes-instance when it has a
vertex cover containing at most `k` vertices. -/
def HasVertexCover (I : CliqueInstance) : Prop :=
  ∃ vertices : Finset Nat,
    vertices.card ≤ I.targetSize ∧ I.IsVertexCover vertices

/-- Every vertex in a typed cover lies below the instance vertex count. -/
theorem vertex_lt_of_isVertexCover {I : CliqueInstance} {vertices : Finset Nat}
    (hcover : I.IsVertexCover vertices) {v : Nat} (hv : v ∈ vertices) :
    v < I.vertexCount :=
  hcover.1 v hv

/-- Every stored edge has an endpoint in a typed cover. -/
theorem edge_covered_of_isVertexCover {I : CliqueInstance}
    {vertices : Finset Nat} (hcover : I.IsVertexCover vertices)
    {e : Nat × Nat} (he : e ∈ I.edges) :
    e.1 ∈ vertices ∨ e.2 ∈ vertices :=
  hcover.2 e he

end CliqueInstance

end Chapter34
end CLRS
