import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Parser

/-!
# Round trips for the general CLIQUE codecs

The canonical encoders are left inverses of the complete parsers for arbitrary
instance structures and arbitrary certificate vertex lists.
-/

namespace CLRS
namespace Chapter34

private theorem consumeCliqueTicks_replicate_fieldSep (count : Nat)
    (rest : List CliqueSym) :
    consumeCliqueTicks (prependCliqueTicks count (.fieldSep :: rest)) =
      (count, .fieldSep :: rest) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, consumeCliqueTicks, ih]

private theorem decodeCliqueEdgeLeft_ticks (left count : Nat)
    (rest : List CliqueSym) :
    decodeCliqueEdgeLeft left
        (prependCliqueTicks count (.pairSep :: rest)) =
      decodeCliqueEdgeRight (left + count) 0 rest := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, decodeCliqueEdgeLeft, ih, Nat.add_assoc,
        Nat.add_comm 1 count]

private theorem decodeCliqueEdgeRight_ticks (left right count : Nat)
    (rest : List CliqueSym) :
    decodeCliqueEdgeRight left right
        (prependCliqueTicks count (.recordEnd :: rest)) =
      match decodeCliqueEdges rest with
      | some edges => some ((left, right + count) :: edges)
      | none => none := by
  induction count generalizing right with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, decodeCliqueEdgeRight, ih, Nat.add_assoc,
        Nat.add_comm 1 count]

private theorem decodeCliqueEdges_encode (edges : List (Nat × Nat)) :
    decodeCliqueEdges (edges.flatMap encodeCliqueEdge) = some edges := by
  induction edges with
  | nil => simp [decodeCliqueEdges]
  | cons edge edges ih =>
      rcases edge with ⟨left, right⟩
      rw [List.flatMap_cons]
      simp only [encodeCliqueEdge, List.cons_append,
        prependCliqueTicks_append, decodeCliqueEdges]
      rw [decodeCliqueEdgeLeft_ticks]
      rw [decodeCliqueEdgeRight_ticks]
      simp only [List.nil_append, Nat.zero_add]
      rw [ih]

/-- Decoding a canonical instance encoding recovers the original structure. -/
theorem decode_encodeCliqueInstance (I : CliqueInstance) :
    decodeCliqueInstance (encodeCliqueInstance I) = some I := by
  simp only [encodeCliqueInstance, decodeCliqueInstance,
    consumeCliqueTicks_replicate_fieldSep, decodeCliqueEdges_encode]

private theorem decodeCliqueVertex_ticks (vertex count : Nat)
    (rest : List CliqueSym) :
    decodeCliqueVertex vertex
        (prependCliqueTicks count (.recordEnd :: rest)) =
      match decodeCliqueVertices rest with
      | some vertices => some ((vertex + count) :: vertices)
      | none => none := by
  induction count generalizing vertex with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, decodeCliqueVertex, ih, Nat.add_assoc,
        Nat.add_comm 1 count]

private theorem decodeCliqueVertices_encode (vertices : List Nat) :
    decodeCliqueVertices (vertices.flatMap encodeCliqueVertex) = some vertices := by
  induction vertices with
  | nil => simp [decodeCliqueVertices]
  | cons vertex vertices ih =>
      rw [List.flatMap_cons]
      simp only [encodeCliqueVertex, List.cons_append,
        prependCliqueTicks_append, decodeCliqueVertices]
      rw [decodeCliqueVertex_ticks]
      simp only [List.nil_append, Nat.zero_add]
      rw [ih]

/-- Decoding a canonical certificate encoding recovers the vertex list. -/
theorem decode_encodeCliqueCertificate (vertices : List Nat) :
    decodeCliqueCertificate (encodeCliqueCertificate vertices) = some vertices := by
  simp [encodeCliqueCertificate, decodeCliqueCertificate,
    decodeCliqueVertices_encode]

end Chapter34
end CLRS
