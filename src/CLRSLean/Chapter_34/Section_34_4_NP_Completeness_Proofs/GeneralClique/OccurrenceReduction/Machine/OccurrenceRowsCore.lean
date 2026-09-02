import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Occurrences
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Indexed occurrence rows: semantics and core controller

Each literal occurrence becomes one marked unary row with fields for its
numeric vertex, clause, polarity, and positive variable-code length.  The
last field uses the literal encoding's existing `index + 1` convention.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Numeric polarity bit used by the row encoding. -/
def occurrencePolarityCode : Literal → Nat
  | .pos _ => 0
  | .neg _ => 1

/-- Positive unary variable code already present in the canonical CNF
encoding. -/
def occurrenceVariableCode : Literal → Nat
  | .pos index | .neg index => index + 1

/-- Four numeric fields of one indexed occurrence row. -/
def indexedOccurrenceRowValues (vertex : Nat)
    (occurrence : IndexedOccurrence) : List Nat :=
  [vertex, occurrence.clauseIndex, occurrencePolarityCode occurrence.literal,
    occurrenceVariableCode occurrence.literal]

/-- Marked rows for one clause, starting at the supplied global vertex. -/
def encodeIndexedClauseRowsFrom : Nat → Nat → Clause → List UnaryFrameSym
  | _, _, [] => []
  | vertex, clauseIndex, literal :: clause =>
      encodeUnaryFrame
          (indexedOccurrenceRowValues vertex
            { clauseIndex, positionIndex := 0, literal }) ++
        [.frameEnd] ++
        encodeIndexedClauseRowsFrom (vertex + 1) clauseIndex clause

/-- Marked rows for a formula suffix, starting at supplied vertex and clause
indices. -/
def encodeIndexedOccurrenceRowsFrom : Nat → Nat → CNF → List UnaryFrameSym
  | _, _, [] => []
  | vertex, clauseIndex, clause :: formula =>
      encodeIndexedClauseRowsFrom vertex clauseIndex clause ++
        encodeIndexedOccurrenceRowsFrom (vertex + clause.length)
          (clauseIndex + 1) formula

/-- Canonical marked rows for all literal positions of a formula. -/
def encodeIndexedOccurrenceRows (formula : CNF) : List UnaryFrameSym :=
  encodeIndexedOccurrenceRowsFrom 0 0 formula

/-- Indexed rows determined by an arbitrary raw CNF word. -/
def canonicalIndexedOccurrenceRows (input : List CNFSym) :
    List UnaryFrameSym :=
  encodeIndexedOccurrenceRows (decodeCNF input)

/-- Exact raw-input meaning of the indexed occurrence-row stream. -/
theorem canonicalIndexedOccurrenceRows_eq (input : List CNFSym) :
    canonicalIndexedOccurrenceRows input =
      encodeIndexedOccurrenceRows (decodeCNF input) := rfl

/-- Finite phases of the reverse-output occurrence-row controller. -/
inductive OccurrenceRowsLabel
  | scan (startedClause : Bool)
  | copyVertex | saveVertex | pushVertexTick | pushVertexSep
  | restoreVertex | restoreVertexInc
  | copyClause | saveClause | pushClauseTick | pushClauseSep
  | restoreClause | restoreClauseInc
  | readPolarity | pushNegativeTick | pushPolaritySep | readVariableMark
  | variableRun | pushVariableTick
  | saveBoundary (symbol : GraphSym) | restoreBoundary
  | pushVariableSep | pushRowEnd | advanceVertex
  | advanceClause
  | clearVertex | clearClause
  | halt | invalid
deriving DecidableEq, Fintype

/-- Reverse-output parser for canonical occurrence descriptors.  Counter one
stores the vertex ordinal, counter two the clause ordinal, and counter three
temporarily saves either ordinal while it is copied to the output. -/
def occurrenceRowsRevProgram : Program GraphSym UnaryFrameSym where
  Label := OccurrenceRowsLabel
  main := .scan false
  op
    | .scan started => .popInput .clearVertex fun
        | .clauseMark => if started then .advanceClause else .scan true
        | .vertexMark => .copyVertex
        | _ => .invalid
    | .copyVertex => .dec₁ .pushVertexSep .saveVertex
    | .saveVertex => .inc₃ .pushVertexTick
    | .pushVertexTick => .pushOutput .tick .copyVertex
    | .pushVertexSep => .pushOutput .separator .restoreVertex
    | .restoreVertex => .dec₃ .copyClause .restoreVertexInc
    | .restoreVertexInc => .inc₁ .restoreVertex
    | .copyClause => .dec₂ .pushClauseSep .saveClause
    | .saveClause => .inc₃ .pushClauseTick
    | .pushClauseTick => .pushOutput .tick .copyClause
    | .pushClauseSep => .pushOutput .separator .restoreClause
    | .restoreClause => .dec₃ .readPolarity .restoreClauseInc
    | .restoreClauseInc => .inc₂ .restoreClause
    | .readPolarity => .popInput .invalid fun
        | .posMark => .pushPolaritySep
        | .negMark => .pushNegativeTick
        | _ => .invalid
    | .pushNegativeTick => .pushOutput .tick .pushPolaritySep
    | .pushPolaritySep => .pushOutput .separator .readVariableMark
    | .readVariableMark => .popInput .invalid fun
        | .varMark => .variableRun
        | _ => .invalid
    | .variableRun => .popInput .pushVariableSep fun symbol =>
        if symbol = .endMark then .pushVariableTick else .saveBoundary symbol
    | .pushVariableTick => .pushOutput .tick .variableRun
    | .saveBoundary symbol => .pushWork₁ symbol .restoreBoundary
    | .restoreBoundary => .moveWork₁Input .pushVariableSep
        (fun _ => .pushVariableSep)
    | .pushVariableSep => .pushOutput .separator .pushRowEnd
    | .pushRowEnd => .pushOutput .frameEnd .advanceVertex
    | .advanceVertex => .inc₁ (.scan true)
    | .advanceClause => .inc₂ (.scan true)
    | .clearVertex => .dec₁ .clearClause .clearVertex
    | .clearClause => .dec₂ .halt .clearClause
    | .halt => .halt
    | .invalid => .halt

/-- Proof-facing occurrence-row configuration. -/
def occurrenceRowsCfg (label : OccurrenceRowsLabel)
    (buffer : Option GraphSym) (test : Bool)
    (input : List GraphSym) (output : List UnaryFrameSym)
    (work : List GraphSym) (vertex clause saved : Nat) :
    BuilderCfg occurrenceRowsRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := work
  work₂ := []
  counter₁ := List.replicate vertex ()
  counter₂ := List.replicate clause ()
  counter₃ := List.replicate saved ()

end TMClique
end Turing
end Chapter34
end CLRS
