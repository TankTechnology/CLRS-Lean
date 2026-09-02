import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCompare
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: one prior-row scan

This file composes vertex copying, both restored unary comparisons, polarity
parsing, and compatibility tagging for one prior occurrence row.
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

/-- Copy the remaining vertex ticks and its separator to work two. -/
private def compatibilityEdges_priorVertex_eval
    (currentPolarity : Bool) (count : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCode : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorVertex currentPolarity)
        buffer₁ buffer₂ test [] output
        (List.replicate count .tick ++ .separator :: tail) work₂
        upper clause variableCode)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (some .separator) buffer₂ test [] output tail
        (.separator :: List.replicate count .tick ++ work₂)
        upper clause variableCode)) (count + 1) := by
  induction count generalizing buffer₁ work₂ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesCfg (.priorVertex currentPolarity)
        (some .tick) buffer₂ test [] output
        (List.replicate count .tick ++ .separator :: tail)
        (.tick :: work₂) upper clause variableCode
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.priorVertex currentPolarity)
            buffer₁ buffer₂ test [] output
            (List.replicate (count + 1) .tick ++ .separator :: tail) work₂
            upper clause variableCode) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, List.replicate_succ, step,
            compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (buffer₁ := some .tick) (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (count + 1) _ after _ first rest
      simpa only [separator_replicate_tick_append_tick, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Copy the complete prior vertex block, starting at `priorStart`. -/
private def compatibilityEdges_priorStartVertex_eval
    (currentPolarity : Bool) (vertex : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCode : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorStart currentPolarity)
        buffer₁ buffer₂ test [] output
        (List.replicate vertex .tick ++ .separator :: tail) work₂
        upper clause variableCode)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (some .separator) buffer₂ test [] output tail
        (.separator :: List.replicate vertex .tick ++ work₂)
        upper clause variableCode)) (vertex + 1) := by
  cases vertex with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ vertex =>
      let after := compatibilityEdgesCfg (.priorVertex currentPolarity)
        (some .tick) buffer₂ test [] output
        (List.replicate vertex .tick ++ .separator :: tail)
        (.tick :: work₂) upper clause variableCode
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.priorStart currentPolarity)
            buffer₁ buffer₂ test [] output
            (List.replicate (vertex + 1) .tick ++ .separator :: tail) work₂
            upper clause variableCode) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, List.replicate_succ, step,
            compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
      have rest := compatibilityEdges_priorVertex_eval currentPolarity vertex
        tail (.tick :: work₂) output (some .tick) buffer₂ test
        upper clause variableCode
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (vertex + 1) _ after _ first rest
      simpa only [separator_replicate_tick_append_tick, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Copy and decode the prior polarity field. -/
private def compatibilityEdges_priorPolarityRun
    (currentPolarity clauseEqual : Bool) (literal : Literal)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCode : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorPolarity currentPolarity clauseEqual)
        buffer₁ buffer₂ test [] output
        (encodeUnaryFrameBlock (occurrencePolarityCode literal) ++ tail) work₂
        upper clause variableCode)
      (some (compatibilityEdgesVariableCfg
        (.priorVariable currentPolarity clauseEqual
          (occurrencePolarityFlag literal) false)
        (some .separator) buffer₂ test [] output tail
        ((encodeUnaryFrameBlock (occurrencePolarityCode literal)).reverse ++
          work₂) upper variableCode clause))
      ((occurrencePolarityFlag literal).toNat + 1) := by
  cases literal with
  | pos variableIndex =>
      exact ⟨⟨1, by
        simp [flip, occurrencePolarityCode, occurrencePolarityFlag,
          encodeUnaryFrameBlock, step, compatibilityEdgesProgram,
          compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩,
        le_rfl⟩
  | neg variableIndex =>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, occurrencePolarityCode,
          occurrencePolarityFlag, encodeUnaryFrameBlock, step,
          compatibilityEdgesProgram, compatibilityEdgesVariableCfg,
          compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩

/-- Boolean attached to a restored prior row. -/
def indexedOccurrencesCompatibleCode
    (current prior : IndexedOccurrence × Nat) : Bool :=
  occurrenceRowsCompatibleCode
    (decide (prior.1.clauseIndex = current.1.clauseIndex))
    (occurrencePolarityFlag prior.1.literal !=
      occurrencePolarityFlag current.1.literal)
    (decide (occurrenceVariableCode prior.1.literal =
      occurrenceVariableCode current.1.literal))

/-- Physical tag stored above a reversed prior row. -/
def encodeCompatibilityTag (compatible : Bool) : List UnaryFrameSym :=
  [.separator, if compatible then .tick else .frameEnd]

/-- Uniform budget for parsing, comparing, and tagging one prior row. -/
def compatibilityEdgesPriorRowSteps
    (current prior : IndexedOccurrence × Nat) : Nat :=
  prior.2 + 1 +
    compatibilityEdgesComparisonSteps prior.1.clauseIndex
      current.1.clauseIndex +
    (occurrencePolarityFlag prior.1.literal).toNat + 1 +
    compatibilityEdgesComparisonSteps
      (occurrenceVariableCode prior.1.literal)
      (occurrenceVariableCode current.1.literal) + 3

/-- One prior row is copied in reverse physical order and tagged by the exact
occurrence compatibility predicate; all current-row counters are restored. -/
def compatibilityEdges_priorRowRun
    (current prior : IndexedOccurrence × Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg
        (.priorStart (occurrencePolarityFlag current.1.literal))
        buffer₁ buffer₂ test [] output
        (encodeIndexedOccurrenceEntry prior ++ tail) work₂ current.2
        current.1.clauseIndex (occurrenceVariableCode current.1.literal))
      (some (compatibilityEdgesCfg
        (.priorStart (occurrencePolarityFlag current.1.literal))
        (some .frameEnd) none
        (decide (occurrenceVariableCode prior.1.literal <
          occurrenceVariableCode current.1.literal))
        [] output tail
        (encodeCompatibilityTag
            (indexedOccurrencesCompatibleCode current prior) ++
          (encodeIndexedOccurrenceEntry prior).reverse ++ work₂)
        current.2 current.1.clauseIndex
        (occurrenceVariableCode current.1.literal)))
      (compatibilityEdgesPriorRowSteps current prior) := by
  rcases current with ⟨currentOccurrence, currentVertex⟩
  rcases currentOccurrence with
    ⟨currentClause, currentPosition, currentLiteral⟩
  rcases prior with ⟨priorOccurrence, priorVertex⟩
  rcases priorOccurrence with ⟨priorClause, priorPosition, priorLiteral⟩
  let afterVertex := encodeUnaryFrameBlock priorClause ++
    encodeUnaryFrameBlock (occurrencePolarityCode priorLiteral) ++
    encodeUnaryFrameBlock (occurrenceVariableCode priorLiteral) ++
    [.frameEnd] ++ tail
  have vertexRun := compatibilityEdges_priorStartVertex_eval
    (occurrencePolarityFlag currentLiteral) priorVertex afterVertex work₂ output
    buffer₁ buffer₂ test currentVertex currentClause
    (occurrenceVariableCode currentLiteral)
  let afterClause := encodeUnaryFrameBlock
      (occurrencePolarityCode priorLiteral) ++
    encodeUnaryFrameBlock (occurrenceVariableCode priorLiteral) ++
    [.frameEnd] ++ tail
  let vertexWork₂ := .separator :: List.replicate priorVertex .tick ++ work₂
  have clauseRun := compatibilityEdges_priorClauseComparisonRun
    (occurrencePolarityFlag currentLiteral) priorClause currentClause
    afterClause vertexWork₂ output (some .separator) buffer₂ test currentVertex
    (occurrenceVariableCode currentLiteral)
  have vertexRun' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg
        (.priorStart (occurrencePolarityFlag currentLiteral))
        buffer₁ buffer₂ test [] output
        (List.replicate priorVertex .tick ++ .separator :: afterVertex) work₂
        currentVertex currentClause (occurrenceVariableCode currentLiteral))
      (some (compatibilityEdgesCfg
        (.priorClause (occurrencePolarityFlag currentLiteral) false)
        (some .separator) buffer₂ test [] output
        (List.replicate priorClause .tick ++ .separator :: afterClause)
        vertexWork₂ currentVertex currentClause
        (occurrenceVariableCode currentLiteral))) (priorVertex + 1) := by
    simpa [afterVertex, afterClause, vertexWork₂, encodeUnaryFrameBlock,
      List.append_assoc] using vertexRun
  let afterPolarity := encodeUnaryFrameBlock
      (occurrenceVariableCode priorLiteral) ++ [.frameEnd] ++ tail
  let clauseWork₂ := .separator :: List.replicate priorClause .tick ++
    vertexWork₂
  have polarityRun := compatibilityEdges_priorPolarityRun
    (occurrencePolarityFlag currentLiteral)
    (decide (priorClause = currentClause)) priorLiteral afterPolarity
    clauseWork₂ output (some .separator) none
    (decide (priorClause < currentClause)) currentVertex currentClause
    (occurrenceVariableCode currentLiteral)
  have clauseRun' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg
        (.priorClause (occurrencePolarityFlag currentLiteral) false)
        (some .separator) buffer₂ test [] output
        (List.replicate priorClause .tick ++ .separator :: afterClause)
        vertexWork₂ currentVertex currentClause
        (occurrenceVariableCode currentLiteral))
      (some (compatibilityEdgesCfg
        (.priorPolarity (occurrencePolarityFlag currentLiteral)
          (decide (priorClause = currentClause)))
        (some .separator) none (decide (priorClause < currentClause)) [] output
        (encodeUnaryFrameBlock (occurrencePolarityCode priorLiteral) ++
          afterPolarity) clauseWork₂ currentVertex currentClause
        (occurrenceVariableCode currentLiteral)))
      (compatibilityEdgesComparisonSteps priorClause currentClause) := by
    simpa [afterClause, afterPolarity, clauseWork₂, vertexWork₂,
      encodeUnaryFrameBlock, List.append_assoc] using clauseRun
  let polarityWork₂ :=
    (encodeUnaryFrameBlock (occurrencePolarityCode priorLiteral)).reverse ++
      clauseWork₂
  have variableRun := compatibilityEdges_priorVariableComparisonRun
    (occurrencePolarityFlag currentLiteral)
    (decide (priorClause = currentClause))
    (occurrencePolarityFlag priorLiteral)
    (occurrenceVariableCode priorLiteral)
    (occurrenceVariableCode currentLiteral) (.frameEnd :: tail) polarityWork₂
    output (some .separator) none (decide
      (priorClause < currentClause)) currentVertex currentClause
  have polarityRun' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg
        (.priorPolarity (occurrencePolarityFlag currentLiteral)
          (decide (priorClause = currentClause)))
        (some .separator) none (decide (priorClause < currentClause)) [] output
        (encodeUnaryFrameBlock (occurrencePolarityCode priorLiteral) ++
          afterPolarity) clauseWork₂ currentVertex currentClause
        (occurrenceVariableCode currentLiteral))
      (some (compatibilityEdgesVariableCfg
        (.priorVariable (occurrencePolarityFlag currentLiteral)
          (decide (priorClause = currentClause))
          (occurrencePolarityFlag priorLiteral) false)
        (some .separator) none (decide (priorClause < currentClause)) [] output
        (List.replicate (occurrenceVariableCode priorLiteral) .tick ++
          .separator :: .frameEnd :: tail)
        polarityWork₂ currentVertex (occurrenceVariableCode currentLiteral)
        currentClause))
      ((occurrencePolarityFlag priorLiteral).toNat + 1) := by
    simpa [afterPolarity, polarityWork₂, clauseWork₂,
      encodeUnaryFrameBlock, List.append_assoc] using polarityRun
  let compatible := indexedOccurrencesCompatibleCode
    (⟨⟨currentClause, currentPosition, currentLiteral⟩, currentVertex⟩)
    (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩)
  let rowWork₂ := .separator ::
    List.replicate (occurrenceVariableCode priorLiteral) .tick ++
    polarityWork₂
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg
        (.priorEnd (occurrencePolarityFlag currentLiteral)
          (decide (priorClause = currentClause))
          (occurrencePolarityFlag priorLiteral)
          (decide (occurrenceVariableCode priorLiteral =
            occurrenceVariableCode currentLiteral)))
        (some .separator) none (decide
          (occurrenceVariableCode priorLiteral <
            occurrenceVariableCode currentLiteral)) [] output
        (.frameEnd :: tail) rowWork₂ currentVertex
        (occurrenceVariableCode currentLiteral) currentClause)
      (some (compatibilityEdgesCfg
        (.priorStart (occurrencePolarityFlag currentLiteral))
        (some .frameEnd) none (decide
          (occurrenceVariableCode priorLiteral <
            occurrenceVariableCode currentLiteral)) [] output tail
        (encodeCompatibilityTag compatible ++ .frameEnd :: rowWork₂)
        currentVertex currentClause (occurrenceVariableCode currentLiteral)))
      3 := by
    exact ⟨⟨3, by
      simp [Function.iterate_succ_apply, flip, compatible,
        indexedOccurrencesCompatibleCode, encodeCompatibilityTag,
        occurrenceRowsCompatibleCode, step, compatibilityEdgesProgram,
        compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩,
      le_rfl⟩
  have variableRun' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg
        (.priorVariable (occurrencePolarityFlag currentLiteral)
          (decide (priorClause = currentClause))
          (occurrencePolarityFlag priorLiteral) false)
        (some .separator) none (decide (priorClause < currentClause)) [] output
        (List.replicate (occurrenceVariableCode priorLiteral) .tick ++
          .separator :: .frameEnd :: tail)
        polarityWork₂ currentVertex (occurrenceVariableCode currentLiteral)
        currentClause)
      (some (compatibilityEdgesVariableCfg
        (.priorEnd (occurrencePolarityFlag currentLiteral)
          (decide (priorClause = currentClause))
          (occurrencePolarityFlag priorLiteral)
          (decide (occurrenceVariableCode priorLiteral =
            occurrenceVariableCode currentLiteral)))
        (some .separator) none (decide
          (occurrenceVariableCode priorLiteral <
            occurrenceVariableCode currentLiteral)) [] output
        (.frameEnd :: tail) rowWork₂ currentVertex
        (occurrenceVariableCode currentLiteral) currentClause))
      (compatibilityEdgesComparisonSteps
        (occurrenceVariableCode priorLiteral)
        (occurrenceVariableCode currentLiteral)) := by
    simpa [rowWork₂, polarityWork₂] using variableRun
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (priorVertex + 1)
    (compatibilityEdgesComparisonSteps priorClause currentClause)
    _ _ _ vertexRun' clauseRun'
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ ((occurrencePolarityFlag priorLiteral).toNat + 1)
    _ _ _ first polarityRun'
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (compatibilityEdgesComparisonSteps
      (occurrenceVariableCode priorLiteral)
      (occurrenceVariableCode currentLiteral)) _ _ _ second variableRun'
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 3 _ _ _ third finish
  convert full using 1 <;>
    simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
      encodeUnaryFrame, encodeUnaryFrameBlock, afterVertex,
      vertexWork₂, clauseWork₂, polarityWork₂,
      rowWork₂, compatible, indexedOccurrencesCompatibleCode,
      encodeCompatibilityTag, compatibilityEdgesPriorRowSteps,
      List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]; rfl

end TMClique
end Turing
end Chapter34
end CLRS
