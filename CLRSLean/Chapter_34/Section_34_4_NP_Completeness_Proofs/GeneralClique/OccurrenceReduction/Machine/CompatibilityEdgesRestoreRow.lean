import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCleanup
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: restore one tagged row

This file proves the local restoration pass for one reversed occurrence row.
The physical compatibility tag becomes a one-symbol flag following the
forward row, ready for the edge-emission pass.
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

private inductive CompatibilityRestoreField
  | variable | polarity | clause
  deriving DecidableEq

private def compatibilityRestoreFieldLabel :
    CompatibilityRestoreField → CompatibilityEdgesLabel
  | .variable => .taggedRestoreVariable
  | .polarity => .taggedRestorePolarity
  | .clause => .taggedRestoreClause

private def compatibilityRestoreFieldNext :
    CompatibilityRestoreField → CompatibilityEdgesLabel
  | .variable => .taggedRestorePolarity
  | .polarity => .taggedRestoreClause
  | .clause => .taggedRestoreVertex

private def compatibilityEdges_restoreFieldRun
    (field : CompatibilityRestoreField) (count : Nat)
    (input work₁ tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (compatibilityRestoreFieldLabel field)
        buffer₁ buffer₂ test input output work₁
        (List.replicate count .tick ++ .separator :: tail) upper 0 0)
      (some (compatibilityEdgesCfg (compatibilityRestoreFieldNext field)
        buffer₁ (some .separator) test input output
        (.separator :: List.replicate count .tick ++ work₁) tail
        upper 0 0)) (count + 1) := by
  induction count generalizing buffer₂ work₁ with
  | zero =>
      cases field <;>
        exact ⟨⟨1, by
          simp [flip, compatibilityRestoreFieldLabel,
            compatibilityRestoreFieldNext, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesCfg
        (compatibilityRestoreFieldLabel field) buffer₁ (some .tick) test
        input output (.tick :: work₁)
        (List.replicate count .tick ++ .separator :: tail) upper 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (compatibilityRestoreFieldLabel field)
            buffer₁ buffer₂ test input output work₁
            (List.replicate (count + 1) .tick ++ .separator :: tail)
            upper 0 0) (some after) 1 := by
        cases field <;>
          exact ⟨⟨1, by
            simp [flip, after, compatibilityRestoreFieldLabel,
              List.replicate_succ, step,
              compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
            le_rfl⟩
      have rest := ih (buffer₂ := some .tick) (work₁ := .tick :: work₁)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        1 (count + 1) _ after _ first rest
      simpa only [separator_replicate_tick_append_tick, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

private def compatibilityEdges_restoreVertexTicksRun
    (count : Nat) (input work₁ tail : List UnaryFrameSym)
    (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
        input output work₁ (List.replicate count .tick ++ tail) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁
        (if count = 0 then buffer₂ else some .tick) test input output
        (List.replicate count .tick ++ work₁) tail upper 0 0))
      (2 * count) := by
  induction count generalizing buffer₂ work₁ with
  | zero =>
      exact ⟨⟨0, by simp⟩, le_rfl⟩
  | succ count ih =>
      let afterPush := compatibilityEdgesCfg .taggedRestoreVertex buffer₁
        (some .tick) test input output (.tick :: work₁)
        (List.replicate count .tick ++ tail) upper 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .taggedRestoreVertex buffer₁ buffer₂ test
            input output work₁
            (List.replicate (count + 1) .tick ++ tail) upper 0 0)
          (some afterPush) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, afterPush,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some .tick) (work₁ := .tick :: work₁)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count) _ afterPush _ first rest
      convert full using 1 <;> try omega
      simp only [Nat.succ_ne_zero, if_false, ite_self,
        replicate_tick_append_tick]

/-- Exact local run from a previously consumed tag marker through one reversed
row.  The row is restored in forward order above work one, followed by its
one-symbol compatibility flag. -/
def compatibilityEdges_restoreTaggedRowRun
    (prior : IndexedOccurrence × Nat) (compatible : Bool)
    (input work₁ tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper : Nat) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .taggedRestoreFlag buffer₁ buffer₂ test
          input output work₁
          ((if compatible then .tick else .frameEnd) ::
            (encodeIndexedOccurrenceEntry prior).reverse ++ tail)
          upper 0 0)
        (some (compatibilityEdgesCfg .taggedRestoreVertex buffer₁
          finalBuffer₂ test input output
          (encodeIndexedOccurrenceEntry prior ++
            [if compatible then .tick else .separator] ++ work₁)
          tail upper 0 0))
        (2 * prior.2 + prior.1.clauseIndex +
          occurrencePolarityCode prior.1.literal +
          occurrenceVariableCode prior.1.literal + 7) := by
  rcases prior with ⟨priorOccurrence, priorVertex⟩
  rcases priorOccurrence with ⟨priorClause, priorPosition, priorLiteral⟩
  let rowFlag : UnaryFrameSym := if compatible then .tick else .separator
  let afterFlagBuffer₂ : Option UnaryFrameSym :=
    if compatible then some .tick else some .frameEnd
  let afterFlagWork₁ := rowFlag :: work₁
  have flagRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreFlag buffer₁ buffer₂ test input
        output work₁
        ((if compatible then .tick else .frameEnd) ::
          (encodeIndexedOccurrenceEntry
            (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩)).reverse ++
          tail) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreFrameEnd buffer₁
        afterFlagBuffer₂ test input output afterFlagWork₁
        ((encodeIndexedOccurrenceEntry
          (⟨⟨priorClause, priorPosition, priorLiteral⟩, priorVertex⟩)).reverse ++
          tail) upper 0 0)) 2 := by
    cases compatible <;>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, rowFlag, afterFlagBuffer₂,
          afterFlagWork₁, step, compatibilityEdgesProgram,
          compatibilityEdgesCfg, stepOp]⟩,
        le_rfl⟩
  let reversedFields :=
    (encodeUnaryFrame
      (indexedOccurrenceRowValues priorVertex
        ⟨priorClause, priorPosition, priorLiteral⟩)).reverse
  let afterEndWork₁ := .frameEnd :: afterFlagWork₁
  have endRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreFrameEnd buffer₁
        afterFlagBuffer₂ test
        input output afterFlagWork₁ (.frameEnd :: reversedFields ++ tail)
        upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVariableSeparator buffer₁
        (some .frameEnd) test input output afterEndWork₁
        (reversedFields ++ tail) upper 0 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, afterEndWork₁, step, compatibilityEdgesProgram,
        compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  let afterVariableSeparatorWork₁ := .separator :: afterEndWork₁
  let afterVariableSeparator :=
    List.replicate (occurrenceVariableCode priorLiteral) .tick ++
      .separator ::
        List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
          .separator :: List.replicate priorClause .tick ++
            .separator :: List.replicate priorVertex .tick ++ tail
  have variableSeparatorRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .taggedRestoreVariableSeparator buffer₁
        (some .frameEnd) test input output afterEndWork₁
        (.separator :: afterVariableSeparator) upper 0 0)
      (some (compatibilityEdgesCfg .taggedRestoreVariable buffer₁
        (some .separator) test input output afterVariableSeparatorWork₁
        afterVariableSeparator upper 0 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, afterVariableSeparatorWork₁, step,
        compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
      le_rfl⟩
  have variableRun := compatibilityEdges_restoreFieldRun
    .variable (occurrenceVariableCode priorLiteral) input
    afterVariableSeparatorWork₁
    (List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
      .separator :: List.replicate priorClause .tick ++
        .separator :: List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  have polarityRun := compatibilityEdges_restoreFieldRun
    .polarity (occurrencePolarityFlag priorLiteral).toNat input
    (.separator ::
      List.replicate (occurrenceVariableCode priorLiteral) .tick ++
        afterVariableSeparatorWork₁)
    (List.replicate priorClause .tick ++ .separator ::
      List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  have clauseRun := compatibilityEdges_restoreFieldRun
    .clause priorClause input
    (.separator ::
      List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
      .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
        afterVariableSeparatorWork₁)
    (List.replicate priorVertex .tick ++ tail)
    output buffer₁ (some .separator) test upper
  have vertexRun := compatibilityEdges_restoreVertexTicksRun priorVertex input
    (.separator :: List.replicate priorClause .tick ++
      .separator ::
        List.replicate (occurrencePolarityFlag priorLiteral).toNat .tick ++
        .separator :: List.replicate (occurrenceVariableCode priorLiteral) .tick ++
          afterVariableSeparatorWork₁)
    tail output buffer₁ (some .separator) test upper
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    2 1 _ _ _ flagRun (by
      simpa [reversedFields, encodeIndexedOccurrenceEntry,
        List.reverse_append] using endRun)
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ first (by
      simpa [reversedFields, indexedOccurrenceRowValues, encodeUnaryFrame,
        encodeUnaryFrameBlock, afterVariableSeparator,
        List.reverse_append, List.append_assoc] using variableSeparatorRun)
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (occurrenceVariableCode priorLiteral + 1) _ _ _ second (by
      simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
        List.append_assoc] using variableRun)
  let fourth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ ((occurrencePolarityFlag priorLiteral).toNat + 1)
    _ _ _ third (by
      simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
        List.append_assoc] using polarityRun)
  let fifth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (priorClause + 1) _ _ _ fourth (by
      simpa [compatibilityRestoreFieldLabel, compatibilityRestoreFieldNext,
        List.append_assoc] using clauseRun)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * priorVertex) _ _ _ fifth (by
      simpa [List.append_assoc] using vertexRun)
  refine ⟨if priorVertex = 0 then some .separator else some .tick, ?_⟩
  convert full using 1 <;>
    simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
      encodeUnaryFrame, encodeUnaryFrameBlock, rowFlag, afterFlagWork₁,
      afterEndWork₁, afterVariableSeparatorWork₁,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

end TMClique
end Turing
end Chapter34
end CLRS
