import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Basic

/-!
# Complete parsers for general CLIQUE

Both parsers consume the complete input.  Instance tokens cannot appear in a
certificate and certificate tokens cannot appear in an instance.
-/

namespace CLRS
namespace Chapter34

/-- Count the leading unary ticks and return the unconsumed suffix. -/
def consumeCliqueTicks : List CliqueSym → Nat × List CliqueSym
  | .tick :: rest =>
      let result := consumeCliqueTicks rest
      (result.1 + 1, result.2)
  | input => (0, input)

mutual
  /-- Parse a complete sequence of edge records. -/
  def decodeCliqueEdges : List CliqueSym → Option (List (Nat × Nat))
    | [] => some []
    | .edgeMark :: input => decodeCliqueEdgeLeft 0 input
    | _ => none

  /-- Parse the unary left endpoint of the leading edge record. -/
  def decodeCliqueEdgeLeft (left : Nat) :
      List CliqueSym → Option (List (Nat × Nat))
    | .tick :: rest => decodeCliqueEdgeLeft (left + 1) rest
    | .pairSep :: rest => decodeCliqueEdgeRight left 0 rest
    | _ => none

  /-- Parse the unary right endpoint, finish the record, and continue. -/
  def decodeCliqueEdgeRight (left right : Nat) :
      List CliqueSym → Option (List (Nat × Nat))
    | .tick :: rest => decodeCliqueEdgeRight left (right + 1) rest
    | .recordEnd :: rest =>
        match decodeCliqueEdges rest with
        | some edges => some ((left, right) :: edges)
        | none => none
    | _ => none
end

/-- Parse a complete canonical graph-plus-{lit}`k` instance. -/
def decodeCliqueInstance : List CliqueSym → Option CliqueInstance
  | .instanceMark :: input =>
      let vertexField := consumeCliqueTicks input
      match vertexField.2 with
      | .fieldSep :: afterVertices =>
          let targetField := consumeCliqueTicks afterVertices
          match targetField.2 with
          | .fieldSep :: edgeInput =>
              match decodeCliqueEdges edgeInput with
              | some edges => some
                  { vertexCount := vertexField.1
                    targetSize := targetField.1
                    edges := edges }
              | none => none
          | _ => none
      | _ => none
  | _ => none

mutual
  /-- Parse a complete sequence of certificate vertex records. -/
  def decodeCliqueVertices : List CliqueSym → Option (List Nat)
    | [] => some []
    | .vertexMark :: input => decodeCliqueVertex 0 input
    | _ => none

  /-- Parse one unary certificate vertex, then continue with the next record. -/
  def decodeCliqueVertex (vertex : Nat) : List CliqueSym → Option (List Nat)
    | .tick :: rest => decodeCliqueVertex (vertex + 1) rest
    | .recordEnd :: rest =>
        match decodeCliqueVertices rest with
        | some vertices => some (vertex :: vertices)
        | none => none
    | _ => none
end

/-- Parse a complete canonical CLIQUE certificate. -/
def decodeCliqueCertificate : List CliqueSym → Option (List Nat)
  | .certificateMark :: input => decodeCliqueVertices input
  | _ => none

end Chapter34
end CLRS
