import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.RoundTrip
import Mathlib.Tactic

/-!
# Canonicality of successful general CLIQUE decodes

The existing round-trip file proves {lit}`decode (encode x) = some x`.  Here we
prove the converse: every successfully decoded raw string is exactly the
canonical encoding of its decoded value.  This is the bridge needed to apply
concrete verifier passes to arbitrary language inputs.
-/

namespace CLRS.Chapter34

private theorem prependCliqueTicks_tick (count : Nat)
    (rest : List CliqueSym) :
    prependCliqueTicks count (.tick :: rest) =
      prependCliqueTicks (count + 1) rest := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, ih]

/-- Counting the maximal leading tick block reconstructs the original list. -/
theorem prepend_consumeCliqueTicks (input : List CliqueSym) :
    prependCliqueTicks (consumeCliqueTicks input).1
        (consumeCliqueTicks input).2 = input := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      cases symbol <;> try rfl
      case tick =>
        simp only [consumeCliqueTicks]
        generalize hresult : consumeCliqueTicks input = result
        rcases result with ⟨count, rest⟩
        rw [hresult] at ih
        simpa [prependCliqueTicks] using congrArg (List.cons .tick) ih

private def EdgeLeftCanonical (left : Nat) (input : List CliqueSym) : Prop :=
  ∀ edges, decodeCliqueEdgeLeft left input = some edges →
    ∃ edge restEdges,
      edges = edge :: restEdges ∧
      prependCliqueTicks left input =
        prependCliqueTicks edge.1
          (.pairSep :: prependCliqueTicks edge.2
            (.recordEnd :: restEdges.flatMap encodeCliqueEdge))

private def EdgeRightCanonical (left right : Nat)
    (input : List CliqueSym) : Prop :=
  ∀ edges, decodeCliqueEdgeRight left right input = some edges →
    ∃ finalRight restEdges,
      edges = (left, finalRight) :: restEdges ∧
      prependCliqueTicks right input =
        prependCliqueTicks finalRight
          (.recordEnd :: restEdges.flatMap encodeCliqueEdge)

/-- A successful edge-list parse consumes exactly the canonical serialization
of the returned edge list. -/
theorem eq_flatMap_encodeCliqueEdge_of_decodeCliqueEdges_eq_some
    (input : List CliqueSym) (edges : List (Nat × Nat))
    (hdecode : decodeCliqueEdges input = some edges) :
    input = edges.flatMap encodeCliqueEdge := by
  let edgesMotive := fun input : List CliqueSym =>
    ∀ edges, decodeCliqueEdges input = some edges →
      input = edges.flatMap encodeCliqueEdge
  let leftMotive := fun left input => EdgeLeftCanonical left input
  let rightMotive := fun left right input =>
    EdgeRightCanonical left right input
  have hall : edgesMotive input := by
    refine decodeCliqueEdges.induct edgesMotive leftMotive rightMotive
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ input
    · dsimp [edgesMotive]
      intro result h
      simp [decodeCliqueEdges] at h
      subst result
      rfl
    · intro current hleft
      dsimp [edgesMotive, leftMotive, EdgeLeftCanonical] at hleft ⊢
      intro result h
      simp only [decodeCliqueEdges] at h
      rcases hleft result h with ⟨edge, rest, rfl, hencoded⟩
      have hencoded' : current =
          prependCliqueTicks edge.1
            (.pairSep :: prependCliqueTicks edge.2
              (.recordEnd :: rest.flatMap encodeCliqueEdge)) := by
        simpa [prependCliqueTicks] using hencoded
      simpa [List.flatMap_cons, encodeCliqueEdge,
        prependCliqueTicks_append] using
          congrArg (List.cons .edgeMark) hencoded'
    · intro current hempty hedge
      dsimp [edgesMotive]
      intro result h
      cases current with
      | nil => exact (hempty rfl).elim
      | cons symbol rest => cases symbol <;> simp_all [decodeCliqueEdges]
    · intro left rest ih
      dsimp [leftMotive, EdgeLeftCanonical] at ih ⊢
      intro result h
      simp only [decodeCliqueEdgeLeft] at h
      rcases ih result h with ⟨edge, tail, rfl, hencoded⟩
      refine ⟨edge, tail, rfl, ?_⟩
      rw [prependCliqueTicks_tick]
      exact hencoded
    · intro left rest ih
      dsimp [leftMotive, rightMotive, EdgeLeftCanonical,
        EdgeRightCanonical] at ih ⊢
      intro result h
      simp only [decodeCliqueEdgeLeft] at h
      rcases ih result h with ⟨right, tail, rfl, hencoded⟩
      refine ⟨(left, right), tail, rfl, ?_⟩
      exact congrArg (prependCliqueTicks left)
        (congrArg (List.cons .pairSep) hencoded)
    · intro current left htick hsep
      dsimp [leftMotive, EdgeLeftCanonical]
      intro result h
      cases current with
      | nil => simp [decodeCliqueEdgeLeft] at h
      | cons symbol rest =>
          cases symbol <;> simp_all [decodeCliqueEdgeLeft]
    · intro left right rest ih
      dsimp [rightMotive, EdgeRightCanonical] at ih ⊢
      intro result h
      simp only [decodeCliqueEdgeRight] at h
      rcases ih result h with ⟨finalRight, tail, rfl, hencoded⟩
      refine ⟨finalRight, tail, rfl, ?_⟩
      rw [prependCliqueTicks_tick]
      exact hencoded
    · intro left right rest parsed hparsed ih
      dsimp [rightMotive, EdgeRightCanonical]
      intro result h
      simp only [decodeCliqueEdgeRight, hparsed] at h
      cases h
      refine ⟨right, parsed, rfl, ?_⟩
      have hrest := ih parsed hparsed
      exact congrArg (prependCliqueTicks right)
        (congrArg (List.cons .recordEnd) hrest)
    · intro left right rest hnone ih
      dsimp [rightMotive, EdgeRightCanonical]
      intro result h
      simp [decodeCliqueEdgeRight, hnone] at h
    · intro current left right htick hend
      dsimp [rightMotive, EdgeRightCanonical]
      intro result h
      cases current with
      | nil => simp [decodeCliqueEdgeRight] at h
      | cons symbol rest =>
          cases symbol <;> simp_all [decodeCliqueEdgeRight]
  exact hall edges hdecode

private def VertexCanonical (vertex : Nat) (input : List CliqueSym) : Prop :=
  ∀ vertices, decodeCliqueVertex vertex input = some vertices →
    ∃ first restVertices,
      vertices = first :: restVertices ∧
      prependCliqueTicks vertex input =
        prependCliqueTicks first
          (.recordEnd :: restVertices.flatMap encodeCliqueVertex)

/-- A successful vertex-list parse consumes exactly the canonical certificate
payload of the returned list. -/
theorem eq_flatMap_encodeCliqueVertex_of_decodeCliqueVertices_eq_some
    (input : List CliqueSym) (vertices : List Nat)
    (hdecode : decodeCliqueVertices input = some vertices) :
    input = vertices.flatMap encodeCliqueVertex := by
  let verticesMotive := fun input : List CliqueSym =>
    ∀ vertices, decodeCliqueVertices input = some vertices →
      input = vertices.flatMap encodeCliqueVertex
  let vertexMotive := fun vertex input => VertexCanonical vertex input
  have hall : verticesMotive input := by
    refine decodeCliqueVertices.induct verticesMotive vertexMotive
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ input
    · dsimp [verticesMotive]
      intro result h
      simp [decodeCliqueVertices] at h
      subst result
      rfl
    · intro current hvertex
      dsimp [verticesMotive, vertexMotive, VertexCanonical] at hvertex ⊢
      intro result h
      simp only [decodeCliqueVertices] at h
      rcases hvertex result h with ⟨first, rest, rfl, hencoded⟩
      have hencoded' : current =
          prependCliqueTicks first
            (.recordEnd :: rest.flatMap encodeCliqueVertex) := by
        simpa [prependCliqueTicks] using hencoded
      simpa [List.flatMap_cons, encodeCliqueVertex,
        prependCliqueTicks_append] using
          congrArg (List.cons .vertexMark) hencoded'
    · intro current hempty hvertex
      dsimp [verticesMotive]
      intro result h
      cases current with
      | nil => exact (hempty rfl).elim
      | cons symbol rest => cases symbol <;> simp_all [decodeCliqueVertices]
    · intro vertex rest ih
      dsimp [vertexMotive, VertexCanonical] at ih ⊢
      intro result h
      simp only [decodeCliqueVertex] at h
      rcases ih result h with ⟨first, tail, rfl, hencoded⟩
      refine ⟨first, tail, rfl, ?_⟩
      rw [prependCliqueTicks_tick]
      exact hencoded
    · intro vertex rest parsed hparsed ih
      dsimp [vertexMotive, VertexCanonical]
      intro result h
      simp only [decodeCliqueVertex, hparsed] at h
      cases h
      refine ⟨vertex, parsed, rfl, ?_⟩
      have hrest := ih parsed hparsed
      exact congrArg (prependCliqueTicks vertex)
        (congrArg (List.cons .recordEnd) hrest)
    · intro vertex rest hnone ih
      dsimp [vertexMotive, VertexCanonical]
      intro result h
      simp [decodeCliqueVertex, hnone] at h
    · intro current vertex htick hend
      dsimp [vertexMotive, VertexCanonical]
      intro result h
      cases current with
      | nil => simp [decodeCliqueVertex] at h
      | cons symbol rest => cases symbol <;> simp_all [decodeCliqueVertex]
  exact hall vertices hdecode

/-- Every successfully decoded raw instance is already its canonical encoding. -/
theorem encodeCliqueInstance_eq_of_decode_eq_some
    (input : List CliqueSym) (I : CliqueInstance)
    (hdecode : decodeCliqueInstance input = some I) :
    encodeCliqueInstance I = input := by
  cases input with
  | nil => simp [decodeCliqueInstance] at hdecode
  | cons symbol fields =>
      cases symbol <;> try simp [decodeCliqueInstance] at hdecode
      case instanceMark =>
        generalize hvertices : consumeCliqueTicks fields = vertexField at hdecode
        rcases vertexField with ⟨vertexCount, vertexRest⟩
        cases vertexRest with
        | nil => simp at hdecode
        | cons first afterVertices =>
          cases first <;> try simp at hdecode
          case fieldSep =>
            generalize htarget : consumeCliqueTicks afterVertices =
              targetField at hdecode
            rcases targetField with ⟨targetSize, targetRest⟩
            cases targetRest with
            | nil => simp at hdecode
            | cons second edgeInput =>
              cases second <;> try simp at hdecode
              case fieldSep =>
                generalize hedges : decodeCliqueEdges edgeInput =
                  edgeResult at hdecode
                cases edgeResult with
                | none => simp at hdecode
                | some edges =>
                  simp only [Option.some.injEq] at hdecode
                  subst I
                  have hverticesEncoded := prepend_consumeCliqueTicks fields
                  rw [hvertices] at hverticesEncoded
                  have htargetEncoded :=
                    prepend_consumeCliqueTicks afterVertices
                  rw [htarget] at htargetEncoded
                  have hedgesEncoded :=
                    eq_flatMap_encodeCliqueEdge_of_decodeCliqueEdges_eq_some
                      edgeInput edges hedges
                  simp only [encodeCliqueInstance]
                  rw [← hedgesEncoded, htargetEncoded, hverticesEncoded]

/-- Every successfully decoded raw certificate is already its canonical
encoding. -/
theorem encodeCliqueCertificate_eq_of_decode_eq_some
    (input : List CliqueSym) (vertices : List Nat)
    (hdecode : decodeCliqueCertificate input = some vertices) :
    encodeCliqueCertificate vertices = input := by
  cases input with
  | nil => simp [decodeCliqueCertificate] at hdecode
  | cons symbol payload =>
      cases symbol <;> try simp [decodeCliqueCertificate] at hdecode
      case certificateMark =>
        have hpayload :=
          eq_flatMap_encodeCliqueVertex_of_decodeCliqueVertices_eq_some
            payload vertices hdecode
        simp [encodeCliqueCertificate, hpayload]

end CLRS.Chapter34
