import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesRestoreRows
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: scan one flagged row

The emission pass parses one forward row into the lower-endpoint counter,
moves its complete physical encoding to work two, consumes its compatibility
flag, and selects either edge emission or lower-counter cleanup.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private theorem replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    List.replicate count .tick ++ .tick :: tail =
      List.replicate (count + 1) .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

private theorem separator_replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    (.separator :: List.replicate count .tick) ++ .tick :: tail =
      (.separator :: List.replicate (count + 1) .tick) ++ tail := by
  simp only [List.cons_append, replicate_tick_append_tick]

private def compatibilityEmitVertexLabel (atStart : Bool) :
    CompatibilityEdgesLabel :=
  if atStart then .emitStart else .emitVertex

private def compatibilityEdges_emitVertexRun
    (atStart : Bool) (count lower : Nat)
    (tail work₂ input : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (compatibilityEmitVertexLabel atStart)
        buffer₁ buffer₂ test input output
        (List.replicate count .tick ++ .separator :: tail) work₂
        upper lower 0)
      (some (compatibilityEdgesCfg .emitClause (some .separator)
        buffer₂ test input output tail
        (.separator :: List.replicate count .tick ++ work₂)
        upper (lower + count) 0)) (2 * count + 1) := by
  induction count generalizing atStart buffer₁ buffer₂ lower work₂ with
  | zero =>
      cases atStart <;>
        exact ⟨⟨1, by
          simp [flip, compatibilityEmitVertexLabel, step,
            compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
  | succ count ih =>
      let afterIncrement := compatibilityEdgesCfg .emitVertex (some .tick)
        buffer₂ test input output
        (List.replicate count .tick ++ .separator :: tail) (.tick :: work₂)
        upper (lower + 1) 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (compatibilityEmitVertexLabel atStart)
            buffer₁ buffer₂ test input output
            (List.replicate (count + 1) .tick ++ .separator :: tail) work₂
            upper lower 0) (some afterIncrement) 2 := by
        cases atStart <;>
          exact ⟨⟨2, by
            simp [Function.iterate_succ_apply, flip, afterIncrement,
              compatibilityEmitVertexLabel,
              List.replicate_succ, step, compatibilityEdgesProgram,
              compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (atStart := false) (buffer₁ := some .tick)
        (buffer₂ := buffer₂) (lower := lower + 1)
        (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count + 1) _ afterIncrement _ first rest
      convert full using 1 <;> try omega
      simp only [separator_replicate_tick_append_tick, Nat.add_comm,
        Nat.add_left_comm]

private inductive CompatibilityEmitField
  | clause | polarity | variable
  deriving DecidableEq

private def compatibilityEmitFieldLabel :
    CompatibilityEmitField → CompatibilityEdgesLabel
  | .clause => .emitClause
  | .polarity => .emitPolarity
  | .variable => .emitVariable

private def compatibilityEmitFieldNext :
    CompatibilityEmitField → CompatibilityEdgesLabel
  | .clause => .emitPolarity
  | .polarity => .emitVariable
  | .variable => .emitFrameEnd

private def compatibilityEdges_emitFieldRun
    (field : CompatibilityEmitField) (count : Nat)
    (tail work₂ input : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper lower : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (compatibilityEmitFieldLabel field)
        buffer₁ buffer₂ test input output
        (List.replicate count .tick ++ .separator :: tail) work₂
        upper lower 0)
      (some (compatibilityEdgesCfg (compatibilityEmitFieldNext field)
        (some .separator) buffer₂ test input output tail
        (.separator :: List.replicate count .tick ++ work₂)
        upper lower 0)) (count + 1) := by
  induction count generalizing buffer₁ buffer₂ work₂ with
  | zero =>
      cases field <;>
        exact ⟨⟨1, by
          simp [flip, compatibilityEmitFieldLabel, compatibilityEmitFieldNext,
            step, compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesCfg (compatibilityEmitFieldLabel field)
        (some .tick) buffer₂ test input output
        (List.replicate count .tick ++ .separator :: tail) (.tick :: work₂)
        upper lower 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (compatibilityEmitFieldLabel field)
            buffer₁ buffer₂ test input output
            (List.replicate (count + 1) .tick ++ .separator :: tail) work₂
            upper lower 0) (some after) 1 := by
        cases field <;>
          exact ⟨⟨1, by
            simp [flip, after, compatibilityEmitFieldLabel,
              List.replicate_succ, step, compatibilityEdgesProgram,
              compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some .tick) (buffer₂ := buffer₂)
        (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (count + 1) _ after _ first rest
      simpa only [separator_replicate_tick_append_tick, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Exact budget for scanning and dispatching one flagged row. -/
def compatibilityEdgesEmitFlaggedRowSteps
    (prior : IndexedOccurrence × Nat) : Nat :=
  2 * prior.2 + prior.1.clauseIndex +
    occurrencePolarityCode prior.1.literal +
    occurrenceVariableCode prior.1.literal + 6

/-- One forward flagged row is parsed and dispatched to the exact branch
selected by its compatibility bit. -/
def compatibilityEdges_emitFlaggedRowRun
    (prior : IndexedOccurrence × Nat) (compatible : Bool)
    (tail work₂ input : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .emitStart buffer₁ buffer₂ test input output
        (encodeIndexedOccurrenceEntry prior ++
          [if compatible then .tick else .separator] ++ tail)
        work₂ upper 0 0)
      (some (compatibilityEdgesCfg
        (if compatible then .pushEdgeEnd else .clearLower)
        (some (if compatible then .tick else .separator))
        buffer₂ test input output tail
        ((encodeIndexedOccurrenceEntry prior).reverse ++ work₂)
        upper prior.2 0))
      (compatibilityEdgesEmitFlaggedRowSteps prior) := by
  rcases prior with ⟨priorOccurrence, priorVertex⟩
  rcases priorOccurrence with ⟨priorClause, priorPosition, priorLiteral⟩
  let afterVertex := encodeUnaryFrameBlock priorClause ++
    encodeUnaryFrameBlock (occurrencePolarityCode priorLiteral) ++
    encodeUnaryFrameBlock (occurrenceVariableCode priorLiteral) ++
    [.frameEnd, if compatible then .tick else .separator] ++ tail
  have vertexRun := compatibilityEdges_emitVertexRun true priorVertex 0
    afterVertex work₂ input output buffer₁ buffer₂ test upper
  let afterClause := encodeUnaryFrameBlock
      (occurrencePolarityCode priorLiteral) ++
    encodeUnaryFrameBlock (occurrenceVariableCode priorLiteral) ++
    [.frameEnd, if compatible then .tick else .separator] ++ tail
  let vertexWork₂ := .separator :: List.replicate priorVertex .tick ++ work₂
  have clauseRun := compatibilityEdges_emitFieldRun .clause priorClause
    afterClause vertexWork₂ input output (some .separator) buffer₂
    test upper priorVertex
  let afterPolarity := encodeUnaryFrameBlock
      (occurrenceVariableCode priorLiteral) ++
    [.frameEnd, if compatible then .tick else .separator] ++ tail
  let clauseWork₂ := .separator :: List.replicate priorClause .tick ++
    vertexWork₂
  have polarityRun := compatibilityEdges_emitFieldRun .polarity
    (occurrencePolarityCode priorLiteral) afterPolarity clauseWork₂ input
    output (some .separator) buffer₂ test upper priorVertex
  let afterVariable :=
    [.frameEnd, if compatible then .tick else .separator] ++ tail
  let polarityWork₂ := .separator ::
    List.replicate (occurrencePolarityCode priorLiteral) .tick ++ clauseWork₂
  have variableRun := compatibilityEdges_emitFieldRun .variable
    (occurrenceVariableCode priorLiteral) afterVariable polarityWork₂ input
    output (some .separator) buffer₂ test upper priorVertex
  let variableWork₂ := .separator ::
    List.replicate (occurrenceVariableCode priorLiteral) .tick ++ polarityWork₂
  have endRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .emitFrameEnd (some .separator) buffer₂
        test input output (.frameEnd ::
          (if compatible then .tick else .separator) :: tail)
        variableWork₂ upper priorVertex 0)
      (some (compatibilityEdgesCfg .emitTag (some .frameEnd) buffer₂
        test input output
        ((if compatible then .tick else .separator) :: tail)
        (.frameEnd :: variableWork₂) upper priorVertex 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  have tagRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .emitTag (some .frameEnd) buffer₂ test
        input output ((if compatible then .tick else .separator) :: tail)
        (.frameEnd :: variableWork₂) upper priorVertex 0)
      (some (compatibilityEdgesCfg
        (if compatible then .pushEdgeEnd else .clearLower)
        (some (if compatible then .tick else .separator)) buffer₂
        test input output tail (.frameEnd :: variableWork₂)
        upper priorVertex 0)) 1 := by
    cases compatible <;>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * priorVertex + 1) (priorClause + 1) _ _ _ vertexRun (by
      simpa [afterVertex, afterClause, vertexWork₂,
        compatibilityEmitFieldLabel, compatibilityEmitFieldNext,
        encodeUnaryFrameBlock, List.append_assoc] using clauseRun)
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (occurrencePolarityCode priorLiteral + 1) _ _ _ first (by
      simpa [afterClause, afterPolarity, clauseWork₂, vertexWork₂,
        compatibilityEmitFieldLabel, compatibilityEmitFieldNext,
        encodeUnaryFrameBlock, List.append_assoc] using polarityRun)
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (occurrenceVariableCode priorLiteral + 1) _ _ _ second (by
      simpa [afterPolarity, afterVariable, polarityWork₂, clauseWork₂,
        vertexWork₂,
        compatibilityEmitFieldLabel, compatibilityEmitFieldNext,
        encodeUnaryFrameBlock, List.append_assoc] using variableRun)
  let fourth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ third (by
      simpa [afterVariable, variableWork₂, polarityWork₂, clauseWork₂,
        vertexWork₂, List.append_assoc] using endRun)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ fourth (by
      simpa [variableWork₂, polarityWork₂, clauseWork₂, vertexWork₂,
        List.append_assoc] using tagRun)
  convert full using 1 <;>
    simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
      encodeUnaryFrame, encodeUnaryFrameBlock, afterVertex,
      compatibilityEdgesEmitFlaggedRowSteps,
      List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  all_goals first | rfl | omega

end TMClique
end Turing
end Chapter34
end CLRS
