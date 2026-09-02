import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Occurrence-row compatibility filter: core controller

The controller stores all indexed occurrence rows, removes the greatest
remaining vertex as the current right endpoint, and compares it with every
smaller vertex.  Clause and variable equality are checked by reversible unary
counter scans.  A tagged restoration pass retains the rows for the next outer
iteration; a second pass emits compatible edges in canonical pair order.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Canonical serialized edge suffix of the occurrence graph. -/
def encodeOccurrenceCliqueEdges (formula : CNF) : List CliqueSym :=
  (occurrenceCliqueEdges formula).flatMap encodeCliqueEdge

/-- Boolean compatibility decision accumulated by the finite controller. -/
def occurrenceRowsCompatibleCode (clauseEqual polarityDifferent
    variableEqual : Bool) : Bool :=
  !clauseEqual && !(polarityDifferent && variableEqual)

/-- The finite phases of the compatibility-edge controller. -/
inductive CompatibilityEdgesLabel
  | load | loadPush (symbol : UnaryFrameSym) | flushRow
  | outer | currentVertex | currentVertexInc
  | currentClause | currentClauseInc
  | currentPolarity | currentNegativeEnd
  | currentVariable (polarity : Bool)
  | currentVariableInc (polarity : Bool) | currentEnd (polarity : Bool)
  | priorStart (currentPolarity : Bool)
  | priorVertex (currentPolarity : Bool)
  | priorClause (currentPolarity tooLong : Bool)
  | priorClauseDec (currentPolarity : Bool)
  | priorClauseMoveExcess (currentPolarity : Bool)
  | priorClauseDropSeparator (currentPolarity tooLong : Bool)
  | priorClauseProbe (currentPolarity : Bool)
  | priorClauseRestoreProbe (currentPolarity : Bool)
  | priorClauseDrain (currentPolarity clauseEqual : Bool)
  | priorClauseDrainInc (currentPolarity clauseEqual : Bool)
  | priorClausePushSeparator (currentPolarity clauseEqual : Bool)
  | priorPolarity (currentPolarity clauseEqual : Bool)
  | priorNegativeEnd (currentPolarity clauseEqual : Bool)
  | priorVariable (currentPolarity clauseEqual priorPolarity tooLong : Bool)
  | priorVariableDec (currentPolarity clauseEqual priorPolarity : Bool)
  | priorVariableMoveExcess
      (currentPolarity clauseEqual priorPolarity : Bool)
  | priorVariableDropSeparator
      (currentPolarity clauseEqual priorPolarity tooLong : Bool)
  | priorVariableProbe (currentPolarity clauseEqual priorPolarity : Bool)
  | priorVariableRestoreProbe
      (currentPolarity clauseEqual priorPolarity : Bool)
  | priorVariableDrain
      (currentPolarity clauseEqual priorPolarity variableEqual : Bool)
  | priorVariableDrainInc
      (currentPolarity clauseEqual priorPolarity variableEqual : Bool)
  | priorVariablePushSeparator
      (currentPolarity clauseEqual priorPolarity variableEqual : Bool)
  | priorEnd
      (currentPolarity clauseEqual priorPolarity variableEqual : Bool)
  | pushTagValue (currentPolarity compatible : Bool)
  | pushTagMarker (currentPolarity : Bool)
  | clearCurrentClause | clearCurrentVariable
  | taggedRestoreStart | taggedRestoreFlag
  | taggedRestoreSaveFlag (compatible : Bool)
  | taggedRestoreFrameEnd | taggedRestoreVariableSeparator
  | taggedRestoreVariable
  | taggedRestorePolarity | taggedRestoreClause
  | taggedRestoreVertex
  | taggedRestorePushVertexTick
  | emitStart | emitVertex | emitVertexInc
  | emitClause | emitPolarity | emitVariable | emitFrameEnd | emitTag
  | pushEdgeEnd | copyUpper | saveUpper | pushUpperTick
  | restoreUpper | restoreUpperInc | pushPairSeparator
  | copyLower | saveLower | pushLowerTick
  | restoreLower | restoreLowerInc | pushEdgeMark
  | clearLower | restoreRows | clearCurrentVertex
  | halt | invalid
deriving DecidableEq

private def compatibilityBoolLabels1
    (constructor : Bool → CompatibilityEdgesLabel) :
    List CompatibilityEdgesLabel :=
  [constructor false, constructor true]

private def compatibilityBoolLabels2
    (constructor : Bool → Bool → CompatibilityEdgesLabel) :
    List CompatibilityEdgesLabel :=
  [false, true].flatMap fun first =>
    [constructor first false, constructor first true]

private def compatibilityBoolLabels3
    (constructor : Bool → Bool → Bool → CompatibilityEdgesLabel) :
    List CompatibilityEdgesLabel :=
  [false, true].flatMap fun first =>
    [false, true].flatMap fun second =>
      [constructor first second false, constructor first second true]

private def compatibilityBoolLabels4
    (constructor : Bool → Bool → Bool → Bool → CompatibilityEdgesLabel) :
    List CompatibilityEdgesLabel :=
  [false, true].flatMap fun first =>
    [false, true].flatMap fun second =>
      [false, true].flatMap fun third =>
        [constructor first second third false,
          constructor first second third true]

private def compatibilityEdgesLabelList : List CompatibilityEdgesLabel :=
  [.load, .loadPush .tick, .loadPush .separator, .loadPush .frameEnd,
    .flushRow, .outer, .currentVertex, .currentVertexInc,
    .currentClause, .currentClauseInc, .currentPolarity,
    .currentNegativeEnd, .clearCurrentClause, .clearCurrentVariable,
    .taggedRestoreStart, .taggedRestoreFlag, .taggedRestoreFrameEnd,
    .taggedRestoreVariableSeparator, .taggedRestoreVariable,
    .taggedRestorePolarity, .taggedRestoreClause,
    .taggedRestoreVertex, .taggedRestorePushVertexTick,
    .emitStart, .emitVertex, .emitVertexInc, .emitClause, .emitPolarity,
    .emitVariable, .emitFrameEnd, .emitTag, .pushEdgeEnd, .copyUpper,
    .saveUpper, .pushUpperTick, .restoreUpper, .restoreUpperInc,
    .pushPairSeparator, .copyLower, .saveLower, .pushLowerTick,
    .restoreLower, .restoreLowerInc, .pushEdgeMark, .clearLower,
    .restoreRows, .clearCurrentVertex, .halt, .invalid] ++
  compatibilityBoolLabels1 .currentVariable ++
  compatibilityBoolLabels1 .currentVariableInc ++
  compatibilityBoolLabels1 .currentEnd ++
  compatibilityBoolLabels1 .priorStart ++
  compatibilityBoolLabels1 .priorVertex ++
  compatibilityBoolLabels2 .priorClause ++
  compatibilityBoolLabels1 .priorClauseDec ++
  compatibilityBoolLabels1 .priorClauseMoveExcess ++
  compatibilityBoolLabels2 .priorClauseDropSeparator ++
  compatibilityBoolLabels1 .priorClauseProbe ++
  compatibilityBoolLabels1 .priorClauseRestoreProbe ++
  compatibilityBoolLabels2 .priorClauseDrain ++
  compatibilityBoolLabels2 .priorClauseDrainInc ++
  compatibilityBoolLabels2 .priorClausePushSeparator ++
  compatibilityBoolLabels2 .priorPolarity ++
  compatibilityBoolLabels2 .priorNegativeEnd ++
  compatibilityBoolLabels4 .priorVariable ++
  compatibilityBoolLabels3 .priorVariableDec ++
  compatibilityBoolLabels3 .priorVariableMoveExcess ++
  compatibilityBoolLabels4 .priorVariableDropSeparator ++
  compatibilityBoolLabels3 .priorVariableProbe ++
  compatibilityBoolLabels3 .priorVariableRestoreProbe ++
  compatibilityBoolLabels4 .priorVariableDrain ++
  compatibilityBoolLabels4 .priorVariableDrainInc ++
  compatibilityBoolLabels4 .priorVariablePushSeparator ++
  compatibilityBoolLabels4 .priorEnd ++
  compatibilityBoolLabels2 .pushTagValue ++
  compatibilityBoolLabels1 .pushTagMarker ++
  compatibilityBoolLabels1 .taggedRestoreSaveFlag

instance : Fintype CompatibilityEdgesLabel :=
  Fintype.ofList compatibilityEdgesLabelList (by
    intro label
    cases label <;>
      simp [compatibilityEdgesLabelList, compatibilityBoolLabels1,
        compatibilityBoolLabels2, compatibilityBoolLabels3,
        compatibilityBoolLabels4] <;>
      aesop (add safe cases Bool) (add safe cases UnaryFrameSym))

/-- Fixed row comparison and compatible-edge emission program.  Counter one
stores the current upper endpoint, counter two the current clause (and later
the lower endpoint), and counter three the current variable (and later a
temporary unary copy). -/
def compatibilityEdgesProgram : Program UnaryFrameSym CliqueSym where
  Label := CompatibilityEdgesLabel
  main := .load
  op
    | .load => .popInput .outer fun symbol => .loadPush symbol
    | .loadPush symbol => .pushWork₂ symbol <|
        if symbol = .frameEnd then .flushRow else .load
    | .flushRow => .moveWork₂Work₁ .load fun _ => .flushRow

    | .outer => .popWork₁ .halt fun
        | .tick => .currentVertexInc
        | .separator => .currentClause
        | .frameEnd => .invalid
    | .currentVertex => .popWork₁ .invalid fun
        | .tick => .currentVertexInc
        | .separator => .currentClause
        | .frameEnd => .invalid
    | .currentVertexInc => .inc₁ .currentVertex
    | .currentClause => .popWork₁ .invalid fun
        | .tick => .currentClauseInc
        | .separator => .currentPolarity
        | .frameEnd => .invalid
    | .currentClauseInc => .inc₂ .currentClause
    | .currentPolarity => .popWork₁ .invalid fun
        | .tick => .currentNegativeEnd
        | .separator => .currentVariable false
        | .frameEnd => .invalid
    | .currentNegativeEnd => .popWork₁ .invalid fun
        | .separator => .currentVariable true
        | _ => .invalid
    | .currentVariable polarity => .popWork₁ .invalid fun
        | .tick => .currentVariableInc polarity
        | .separator => .currentEnd polarity
        | .frameEnd => .invalid
    | .currentVariableInc polarity => .inc₃ (.currentVariable polarity)
    | .currentEnd polarity => .popWork₁ .invalid fun
        | .frameEnd => .priorStart polarity
        | _ => .invalid

    | .priorStart currentPolarity =>
        .moveWork₁Work₂ .clearCurrentClause fun
          | .tick => .priorVertex currentPolarity
          | .separator => .priorClause currentPolarity false
          | .frameEnd => .invalid
    | .priorVertex currentPolarity =>
        .moveWork₁Work₂ .invalid fun
          | .tick => .priorVertex currentPolarity
          | .separator => .priorClause currentPolarity false
          | .frameEnd => .invalid
    | .priorClause currentPolarity tooLong =>
        .moveWork₁Input .invalid fun
          | .tick => if tooLong then
              .priorClauseMoveExcess currentPolarity
            else .priorClauseDec currentPolarity
          | .separator =>
              .priorClauseDropSeparator currentPolarity tooLong
          | .frameEnd => .invalid
    | .priorClauseDec currentPolarity =>
        .dec₂ (.priorClauseMoveExcess currentPolarity)
          (.priorClause currentPolarity false)
    | .priorClauseMoveExcess currentPolarity =>
        .moveInputWork₂ .invalid fun _ =>
          .priorClause currentPolarity true
    | .priorClauseDropSeparator currentPolarity tooLong =>
        .popInput .invalid fun _ =>
          if tooLong then .priorClauseDrain currentPolarity false
          else .priorClauseProbe currentPolarity
    | .priorClauseProbe currentPolarity =>
        .dec₂ (.priorClauseDrain currentPolarity true)
          (.priorClauseRestoreProbe currentPolarity)
    | .priorClauseRestoreProbe currentPolarity =>
        .inc₂ (.priorClauseDrain currentPolarity false)
    | .priorClauseDrain currentPolarity clauseEqual =>
        .moveInputWork₂ (.priorClausePushSeparator currentPolarity clauseEqual)
          fun _ => .priorClauseDrainInc currentPolarity clauseEqual
    | .priorClauseDrainInc currentPolarity clauseEqual =>
        .inc₂ (.priorClauseDrain currentPolarity clauseEqual)
    | .priorClausePushSeparator currentPolarity clauseEqual =>
        .pushWork₂ .separator (.priorPolarity currentPolarity clauseEqual)

    | .priorPolarity currentPolarity clauseEqual =>
        .moveWork₁Work₂ .invalid fun
          | .separator =>
              .priorVariable currentPolarity clauseEqual false false
          | .tick => .priorNegativeEnd currentPolarity clauseEqual
          | .frameEnd => .invalid
    | .priorNegativeEnd currentPolarity clauseEqual =>
        .moveWork₁Work₂ .invalid fun
          | .separator =>
              .priorVariable currentPolarity clauseEqual true false
          | _ => .invalid

    | .priorVariable currentPolarity clauseEqual priorPolarity tooLong =>
        .moveWork₁Input .invalid fun
          | .tick => if tooLong then
              .priorVariableMoveExcess currentPolarity clauseEqual priorPolarity
            else .priorVariableDec currentPolarity clauseEqual priorPolarity
          | .separator =>
              .priorVariableDropSeparator currentPolarity clauseEqual
                priorPolarity tooLong
          | .frameEnd => .invalid
    | .priorVariableDec currentPolarity clauseEqual priorPolarity =>
        .dec₃
          (.priorVariableMoveExcess currentPolarity clauseEqual priorPolarity)
          (.priorVariable currentPolarity clauseEqual priorPolarity false)
    | .priorVariableMoveExcess currentPolarity clauseEqual priorPolarity =>
        .moveInputWork₂ .invalid fun _ =>
          .priorVariable currentPolarity clauseEqual priorPolarity true
    | .priorVariableDropSeparator currentPolarity clauseEqual
        priorPolarity tooLong =>
        .popInput .invalid fun _ =>
          if tooLong then
            .priorVariableDrain currentPolarity clauseEqual priorPolarity false
          else .priorVariableProbe currentPolarity clauseEqual priorPolarity
    | .priorVariableProbe currentPolarity clauseEqual priorPolarity =>
        .dec₃
          (.priorVariableDrain currentPolarity clauseEqual priorPolarity true)
          (.priorVariableRestoreProbe currentPolarity clauseEqual priorPolarity)
    | .priorVariableRestoreProbe currentPolarity clauseEqual priorPolarity =>
        .inc₃
          (.priorVariableDrain currentPolarity clauseEqual priorPolarity false)
    | .priorVariableDrain currentPolarity clauseEqual priorPolarity
        variableEqual =>
        .moveInputWork₂
          (.priorVariablePushSeparator currentPolarity clauseEqual
            priorPolarity variableEqual)
          fun _ => .priorVariableDrainInc currentPolarity clauseEqual
            priorPolarity variableEqual
    | .priorVariableDrainInc currentPolarity clauseEqual priorPolarity
        variableEqual =>
        .inc₃ (.priorVariableDrain currentPolarity clauseEqual
          priorPolarity variableEqual)
    | .priorVariablePushSeparator currentPolarity clauseEqual priorPolarity
        variableEqual =>
        .pushWork₂ .separator
          (.priorEnd currentPolarity clauseEqual priorPolarity variableEqual)
    | .priorEnd currentPolarity clauseEqual priorPolarity variableEqual =>
        .moveWork₁Work₂ .invalid fun
          | .frameEnd =>
              .pushTagValue currentPolarity
                (occurrenceRowsCompatibleCode clauseEqual
                  (priorPolarity != currentPolarity) variableEqual)
          | _ => .invalid
    | .pushTagValue currentPolarity compatible =>
        .pushWork₂ (if compatible then .tick else .frameEnd)
          (.pushTagMarker currentPolarity)
    | .pushTagMarker currentPolarity =>
        .pushWork₂ .separator (.priorStart currentPolarity)

    | .clearCurrentClause =>
        .dec₂ .clearCurrentVariable .clearCurrentClause
    | .clearCurrentVariable =>
        .dec₃ .taggedRestoreStart .clearCurrentVariable

    | .taggedRestoreStart => .popWork₂ .emitStart fun
        | .separator => .taggedRestoreFlag
        | _ => .invalid
    | .taggedRestoreFlag => .popWork₂ .invalid fun
        | .tick => .taggedRestoreSaveFlag true
        | .frameEnd => .taggedRestoreSaveFlag false
        | .separator => .invalid
    | .taggedRestoreSaveFlag compatible =>
        .pushWork₁ (if compatible then .tick else .separator)
          .taggedRestoreFrameEnd
    | .taggedRestoreFrameEnd => .moveWork₂Work₁ .invalid fun
        | .frameEnd => .taggedRestoreVariableSeparator
        | _ => .invalid
    | .taggedRestoreVariableSeparator => .moveWork₂Work₁ .invalid fun
        | .separator => .taggedRestoreVariable
        | _ => .invalid
    | .taggedRestoreVariable => .moveWork₂Work₁ .invalid fun
        | .separator => .taggedRestorePolarity
        | _ => .taggedRestoreVariable
    | .taggedRestorePolarity => .moveWork₂Work₁ .invalid fun
        | .separator => .taggedRestoreClause
        | _ => .taggedRestorePolarity
    | .taggedRestoreClause => .moveWork₂Work₁ .invalid fun
        | .separator => .taggedRestoreVertex
        | _ => .taggedRestoreClause
    | .taggedRestoreVertex => .popWork₂ .emitStart fun
        | .tick => .taggedRestorePushVertexTick
        | .separator => .taggedRestoreFlag
        | .frameEnd => .invalid
    | .taggedRestorePushVertexTick =>
        .pushWork₁ .tick .taggedRestoreVertex

    | .emitStart => .moveWork₁Work₂ .restoreRows fun
        | .tick => .emitVertexInc
        | .separator => .emitClause
        | .frameEnd => .invalid
    | .emitVertex => .moveWork₁Work₂ .invalid fun
        | .tick => .emitVertexInc
        | .separator => .emitClause
        | .frameEnd => .invalid
    | .emitVertexInc => .inc₂ .emitVertex
    | .emitClause => .moveWork₁Work₂ .invalid fun
        | .separator => .emitPolarity
        | _ => .emitClause
    | .emitPolarity => .moveWork₁Work₂ .invalid fun
        | .separator => .emitVariable
        | _ => .emitPolarity
    | .emitVariable => .moveWork₁Work₂ .invalid fun
        | .separator => .emitFrameEnd
        | _ => .emitVariable
    | .emitFrameEnd => .moveWork₁Work₂ .invalid fun
        | .frameEnd => .emitTag
        | _ => .invalid
    | .emitTag => .popWork₁ .invalid fun
        | .tick => .pushEdgeEnd
        | .separator => .clearLower
        | .frameEnd => .invalid

    | .pushEdgeEnd => .pushOutput .recordEnd .copyUpper
    | .copyUpper => .dec₁ .restoreUpper .saveUpper
    | .saveUpper => .inc₃ .pushUpperTick
    | .pushUpperTick => .pushOutput .tick .copyUpper
    | .restoreUpper => .dec₃ .pushPairSeparator .restoreUpperInc
    | .restoreUpperInc => .inc₁ .restoreUpper
    | .pushPairSeparator => .pushOutput .pairSep .copyLower
    | .copyLower => .dec₂ .restoreLower .saveLower
    | .saveLower => .inc₃ .pushLowerTick
    | .pushLowerTick => .pushOutput .tick .copyLower
    | .restoreLower => .dec₃ .pushEdgeMark .restoreLowerInc
    | .restoreLowerInc => .inc₂ .restoreLower
    | .pushEdgeMark => .pushOutput .edgeMark .clearLower
    | .clearLower => .dec₂ .emitStart .clearLower
    | .restoreRows => .moveWork₂Work₁ .clearCurrentVertex fun _ => .restoreRows
    | .clearCurrentVertex => .dec₁ .outer .clearCurrentVertex
    | .halt => .halt
    | .invalid => .halt

/-- Proof-facing controller configuration. -/
def compatibilityEdgesCfg (label : CompatibilityEdgesLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (work₁ work₂ : List UnaryFrameSym)
    (upper clause variableCount : Nat) :
    BuilderCfg compatibilityEdgesProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := List.replicate upper ()
  counter₂ := List.replicate clause ()
  counter₃ := List.replicate variableCount ()

end TMClique
end Turing
end Chapter34
end CLRS
