import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRows

/-!
# Formatting triangular pair rows: core controller

The input is the canonical growing-prefix family for a runtime occurrence
count.  Counter one stores the current row ordinal.  Each unary lower endpoint
is copied to an edge record, after which the row counter is copied to the
upper-endpoint field through counter two and restored.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Complete normalized-pair edge encoding for a given vertex count. -/
def completePairEdgeStream (count : Nat) : List CliqueSym :=
  (List.range count).flatMap fun upper =>
    (List.range upper).flatMap fun lower =>
      encodeCliqueEdge (lower, upper)

/-- The recursive stream agrees with the occurrence reduction's canonical
normalized-pair enumeration. -/
theorem completePairEdgeStream_eq_normalizedPairs (count : Nat) :
    completePairEdgeStream count =
      (normalizedPairs count).flatMap encodeCliqueEdge := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [completePairEdgeStream, List.range_succ,
        List.flatMap_append]
      simp only [List.flatMap_singleton]
      change completePairEdgeStream count ++
          (List.range count).flatMap (fun lower =>
            encodeCliqueEdge (lower, count)) = _
      rw [ih, normalizedPairs, List.flatMap_append]
      simp [List.flatMap_map]

/-- Canonical triangular row input for a runtime vertex count. -/
def pairRowsFormatInput (count : Nat) : List UnaryFrameSym :=
  unaryFrameAffinePrefixRowsStream { base := 0, count }

/-- Candidate edge stream determined by the decoded occurrence count. -/
def canonicalCompletePairEdgeStream (input : List CNFSym) : List CliqueSym :=
  completePairEdgeStream (cnfLiteralCount (decodeCNF input))

/-- Finite phases of the triangular-row formatter. -/
inductive PairRowsFormatLabel
  | scan
  | pushEdgeMarkTick | pushFirstLowerTick
  | copyLower | pushLowerTick
  | pushEdgeMarkZero | pushPairSep
  | emitUpper | saveUpper | pushUpperTick
  | restoreUpper | restoreUpperInc
  | finishEdge
  | advanceRow
  | clearRow
  | halt | invalid
deriving DecidableEq, Fintype

/-- Reverse-output formatter.  A final verified reversal restores forward
record order and the order of symbols inside each record. -/
def pairRowsFormatRevProgram : Program UnaryFrameSym CliqueSym where
  Label := PairRowsFormatLabel
  main := .scan
  op
    | .scan => .popInput .clearRow fun
        | .tick => .pushEdgeMarkTick
        | .separator => .pushEdgeMarkZero
        | .frameEnd => .advanceRow
    | .pushEdgeMarkTick => .pushOutput .edgeMark .pushFirstLowerTick
    | .pushFirstLowerTick => .pushOutput .tick .copyLower
    | .copyLower => .popInput .invalid fun
        | .tick => .pushLowerTick
        | .separator => .pushPairSep
        | .frameEnd => .invalid
    | .pushLowerTick => .pushOutput .tick .copyLower
    | .pushEdgeMarkZero => .pushOutput .edgeMark .pushPairSep
    | .pushPairSep => .pushOutput .pairSep .emitUpper
    | .emitUpper => .dec₁ .restoreUpper .saveUpper
    | .saveUpper => .inc₂ .pushUpperTick
    | .pushUpperTick => .pushOutput .tick .emitUpper
    | .restoreUpper => .dec₂ .finishEdge .restoreUpperInc
    | .restoreUpperInc => .inc₁ .restoreUpper
    | .finishEdge => .pushOutput .recordEnd .scan
    | .advanceRow => .inc₁ .scan
    | .clearRow => .dec₁ .halt .clearRow
    | .halt => .halt
    | .invalid => .halt

/-- Proof-facing formatter configuration. -/
def pairRowsFormatCfg (label : PairRowsFormatLabel)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (row saved : Nat) : BuilderCfg pairRowsFormatRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := List.replicate row ()
  counter₂ := List.replicate saved ()
  counter₃ := []

end TMClique
end Turing
end Chapter34
end CLRS
