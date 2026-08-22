import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Instance

/-!
# General CLIQUE encoding primitives

The instance and certificate grammars use disjoint leading markers and unary
natural numbers.  Every structural role has its own alphabet constructor.
-/

namespace CLRS
namespace Chapter34

/-- The unambiguous alphabet shared by general CLIQUE instances and their
certificates. -/
inductive CliqueSym
  | instanceMark
  | certificateMark
  | tick
  | fieldSep
  | edgeMark
  | vertexMark
  | pairSep
  | recordEnd
  deriving DecidableEq, Repr

/-- Prepend a unary natural number to a fixed suffix. -/
def prependCliqueTicks : Nat → List CliqueSym → List CliqueSym
  | 0, suffix => suffix
  | count + 1, suffix => .tick :: prependCliqueTicks count suffix

/-- Unary-prefix construction commutes with extending its suffix. -/
theorem prependCliqueTicks_append (count : Nat) (suffix tail : List CliqueSym) :
    prependCliqueTicks count suffix ++ tail =
      prependCliqueTicks count (suffix ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, ih]

/-- Encode one normalized edge record with unary endpoints. -/
def encodeCliqueEdge (edge : Nat × Nat) : List CliqueSym :=
  .edgeMark :: prependCliqueTicks edge.1
    (.pairSep :: prependCliqueTicks edge.2 [.recordEnd])

/-- Encode a graph-plus-{lit}`k` instance in the canonical instance grammar. -/
def encodeCliqueInstance (I : CliqueInstance) : List CliqueSym :=
  .instanceMark :: prependCliqueTicks I.vertexCount
    (.fieldSep :: prependCliqueTicks I.targetSize
      (.fieldSep :: I.edges.flatMap encodeCliqueEdge))

/-- Encode one selected vertex record. -/
def encodeCliqueVertex (vertex : Nat) : List CliqueSym :=
  .vertexMark :: prependCliqueTicks vertex [.recordEnd]

/-- Encode a list of selected vertices in the certificate grammar. -/
def encodeCliqueCertificate (vertices : List Nat) : List CliqueSym :=
  .certificateMark :: vertices.flatMap encodeCliqueVertex

/-- Prepending unary ticks adds exactly the represented natural number. -/
@[simp] theorem prependCliqueTicks_length (count : Nat) (suffix : List CliqueSym) :
    (prependCliqueTicks count suffix).length = count + suffix.length := by
  induction count with
  | zero => simp [prependCliqueTicks]
  | succ count ih =>
      simp only [prependCliqueTicks, List.length_cons, ih]
      omega

/-- The encoded length of one edge record. -/
@[simp] theorem encodeCliqueEdge_length (edge : Nat × Nat) :
    (encodeCliqueEdge edge).length = edge.1 + edge.2 + 3 := by
  simp [encodeCliqueEdge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The encoded length of one certificate vertex record. -/
@[simp] theorem encodeCliqueVertex_length (vertex : Nat) :
    (encodeCliqueVertex vertex).length = vertex + 2 := by
  simp [encodeCliqueVertex]

end Chapter34
end CLRS
