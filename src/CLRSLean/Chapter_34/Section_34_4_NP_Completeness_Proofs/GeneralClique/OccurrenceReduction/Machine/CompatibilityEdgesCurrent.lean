import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesLoad
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: current-row parser

The greatest remaining row is removed from the persistent row stack and its
four unary fields are loaded into the controller's finite state and counters.
This file proves that parser phase independently of pair comparison.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Finite polarity flag used by the compatibility controller. -/
def occurrencePolarityFlag : Literal → Bool
  | .pos _ => false
  | .neg _ => true

@[simp] theorem occurrencePolarityCode_eq_flag (literal : Literal) :
    occurrencePolarityCode literal = (occurrencePolarityFlag literal).toNat := by
  cases literal <;> rfl

private def compatibilityEdges_currentVertex_eval
    (remaining accumulated : Nat)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (clause variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .currentVertex buffer₁ buffer₂ test []
        output (List.replicate remaining .tick ++ .separator :: tail) []
        accumulated clause variableCount)
      (some (compatibilityEdgesCfg .currentClause (some .separator) buffer₂
        test [] output tail [] (accumulated + remaining) clause variableCount))
      (2 * remaining + 1) := by
  induction remaining generalizing accumulated buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram,
          compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let after := compatibilityEdgesCfg .currentVertex (some .tick) buffer₂
        test [] output (List.replicate remaining .tick ++
          .separator :: tail) [] (accumulated + 1) clause variableCount
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .currentVertex buffer₁ buffer₂ test []
            output (List.replicate (remaining + 1) .tick ++
              .separator :: tail) [] accumulated clause variableCount)
          (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip,
            after, List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (accumulated + 1) (some .tick)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * remaining + 1) _ after _ first rest
      convert full using 1 <;>
        simp [Nat.add_comm, Nat.add_left_comm]; omega

private def compatibilityEdges_outerVertex_eval
    (vertex : Nat) (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .outer buffer₁ buffer₂ test [] output
        (List.replicate vertex .tick ++ .separator :: tail) [] 0 0 0)
      (some (compatibilityEdgesCfg .currentClause (some .separator) buffer₂
        test [] output tail [] vertex 0 0)) (2 * vertex + 1) := by
  cases vertex with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram,
          compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  | succ vertex =>
      let after := compatibilityEdgesCfg .currentVertex (some .tick) buffer₂
        test [] output (List.replicate vertex .tick ++ .separator :: tail)
        [] 1 0 0
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .outer buffer₁ buffer₂ test [] output
            (List.replicate (vertex + 1) .tick ++ .separator :: tail)
            [] 0 0 0) (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip,
            after, List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := compatibilityEdges_currentVertex_eval vertex 1 tail output
        (some .tick) buffer₂ test 0 0
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * vertex + 1) _ after _ first rest
      convert full using 1 <;>
        simp [Nat.add_comm]; omega

private def compatibilityEdges_currentClause_eval
    (remaining accumulated upper variableCount : Nat)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .currentClause buffer₁ buffer₂ test []
        output (List.replicate remaining .tick ++ .separator :: tail) []
        upper accumulated variableCount)
      (some (compatibilityEdgesCfg .currentPolarity (some .separator) buffer₂
        test [] output tail [] upper (accumulated + remaining) variableCount))
      (2 * remaining + 1) := by
  induction remaining generalizing accumulated buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram,
          compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let after := compatibilityEdgesCfg .currentClause (some .tick) buffer₂
        test [] output (List.replicate remaining .tick ++
          .separator :: tail) [] upper (accumulated + 1) variableCount
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .currentClause buffer₁ buffer₂ test [] output
            (List.replicate (remaining + 1) .tick ++ .separator :: tail) []
            upper accumulated variableCount) (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip,
            after, List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (accumulated + 1) (some .tick)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * remaining + 1) _ after _ first rest
      convert full using 1 <;>
        simp [Nat.add_comm, Nat.add_left_comm]; omega

private def compatibilityEdges_currentVariable_eval
    (polarity : Bool) (remaining accumulated upper clause : Nat)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.currentVariable polarity)
        buffer₁ buffer₂ test [] output
        (List.replicate remaining .tick ++ .separator :: tail) []
        upper clause accumulated)
      (some (compatibilityEdgesCfg (.currentEnd polarity) (some .separator)
        buffer₂ test [] output tail [] upper clause
        (accumulated + remaining))) (2 * remaining + 1) := by
  induction remaining generalizing accumulated buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram,
          compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let after := compatibilityEdgesCfg (.currentVariable polarity)
        (some .tick) buffer₂ test [] output
        (List.replicate remaining .tick ++ .separator :: tail) []
        upper clause (accumulated + 1)
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.currentVariable polarity)
            buffer₁ buffer₂ test [] output
            (List.replicate (remaining + 1) .tick ++ .separator :: tail) []
            upper clause accumulated) (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip,
            after, List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (accumulated + 1) (some .tick)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * remaining + 1) _ after _ first rest
      convert full using 1 <;>
        simp [Nat.add_comm, Nat.add_left_comm]; omega

/-- Exact cost of removing and parsing the current row. -/
def compatibilityEdgesCurrentRowSteps
    (entry : IndexedOccurrence × Nat) : Nat :=
  2 * entry.2 + 2 * entry.1.clauseIndex +
    (occurrencePolarityFlag entry.1.literal).toNat +
    2 * occurrenceVariableCode entry.1.literal + 5

/-- The greatest remaining occurrence row is loaded into the three counters
and the finite polarity flag. -/
def compatibilityEdges_currentRowRun
    (entry : IndexedOccurrence × Nat)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .outer buffer₁ buffer₂ test [] output
        (encodeIndexedOccurrenceEntry entry ++ tail) [] 0 0 0)
      (some (compatibilityEdgesCfg
        (.priorStart (occurrencePolarityFlag entry.1.literal))
        (some .frameEnd) buffer₂ test [] output tail [] entry.2
        entry.1.clauseIndex (occurrenceVariableCode entry.1.literal)))
      (compatibilityEdgesCurrentRowSteps entry) := by
  rcases entry with ⟨occurrence, vertex⟩
  rcases occurrence with ⟨clauseIndex, positionIndex, literal⟩
  cases literal with
  | pos variableIndex =>
      let afterPolarity := encodeUnaryFrameBlock (variableIndex + 1) ++
        [.frameEnd] ++ tail
      let afterVertex := List.replicate clauseIndex .tick ++ .separator ::
        (encodeUnaryFrameBlock 0 ++ afterPolarity)
      have vertexRun := compatibilityEdges_outerVertex_eval vertex afterVertex
        output buffer₁ buffer₂ test
      have clauseRun := compatibilityEdges_currentClause_eval clauseIndex 0
        vertex 0 (encodeUnaryFrameBlock 0 ++ afterPolarity) output
        (some .separator) buffer₂ test
      have clauseRun' : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .currentClause (some .separator) buffer₂
            test [] output afterVertex [] vertex 0 0)
          (some (compatibilityEdgesCfg .currentPolarity (some .separator)
            buffer₂ test [] output (encodeUnaryFrameBlock 0 ++ afterPolarity)
            [] vertex clauseIndex 0)) (2 * clauseIndex + 1) := by
        simpa [afterVertex] using clauseRun
      have polarityRun : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .currentPolarity (some .separator) buffer₂
            test [] output (encodeUnaryFrameBlock 0 ++ afterPolarity) []
            vertex clauseIndex 0)
          (some (compatibilityEdgesCfg (.currentVariable false)
            (some .separator) buffer₂ test [] output afterPolarity []
            vertex clauseIndex 0)) 1 := by
        exact ⟨⟨1, by
          simp [flip, encodeUnaryFrameBlock, step,
            compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have variableRun := compatibilityEdges_currentVariable_eval false
        (variableIndex + 1) 0 vertex clauseIndex (.frameEnd :: tail) output
        (some .separator) buffer₂ test
      have variableRun' : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.currentVariable false) (some .separator)
            buffer₂ test [] output afterPolarity [] vertex clauseIndex 0)
          (some (compatibilityEdgesCfg (.currentEnd false) (some .separator)
            buffer₂ test [] output (.frameEnd :: tail) [] vertex clauseIndex
            (variableIndex + 1))) (2 * (variableIndex + 1) + 1) := by
        simpa [afterPolarity, encodeUnaryFrameBlock] using variableRun
      have endRun : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.currentEnd false) (some .separator) buffer₂
            test [] output (.frameEnd :: tail) [] vertex clauseIndex
            (variableIndex + 1))
          (some (compatibilityEdgesCfg (.priorStart false) (some .frameEnd)
            buffer₂ test [] output tail [] vertex clauseIndex
            (variableIndex + 1))) 1 := by
        exact ⟨⟨1, by
          simp [flip, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg,
            stepOp]⟩, le_rfl⟩
      let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (2 * vertex + 1) (2 * clauseIndex + 1) _ _ _ vertexRun clauseRun'
      let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ 1 _ _ _ first polarityRun
      let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ (2 * (variableIndex + 1) + 1) _ _ _ second variableRun'
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ 1 _ _ _ third endRun
      convert full using 1 <;>
        simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
          encodeUnaryFrame, occurrencePolarityCode, occurrencePolarityFlag,
          occurrenceVariableCode, encodeUnaryFrameBlock, afterVertex,
          afterPolarity, compatibilityEdgesCurrentRowSteps,
          List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]; omega
  | neg variableIndex =>
      let afterPolarity := encodeUnaryFrameBlock (variableIndex + 1) ++
        [.frameEnd] ++ tail
      let afterVertex := List.replicate clauseIndex .tick ++ .separator ::
        (encodeUnaryFrameBlock 1 ++ afterPolarity)
      have vertexRun := compatibilityEdges_outerVertex_eval vertex afterVertex
        output buffer₁ buffer₂ test
      have clauseRun := compatibilityEdges_currentClause_eval clauseIndex 0
        vertex 0 (encodeUnaryFrameBlock 1 ++ afterPolarity) output
        (some .separator) buffer₂ test
      have clauseRun' : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .currentClause (some .separator) buffer₂
            test [] output afterVertex [] vertex 0 0)
          (some (compatibilityEdgesCfg .currentPolarity (some .separator)
            buffer₂ test [] output (encodeUnaryFrameBlock 1 ++ afterPolarity)
            [] vertex clauseIndex 0)) (2 * clauseIndex + 1) := by
        simpa [afterVertex] using clauseRun
      have polarityRun : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg .currentPolarity (some .separator) buffer₂
            test [] output (encodeUnaryFrameBlock 1 ++ afterPolarity) []
            vertex clauseIndex 0)
          (some (compatibilityEdgesCfg (.currentVariable true)
            (some .separator) buffer₂ test [] output afterPolarity []
            vertex clauseIndex 0)) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip,
            encodeUnaryFrameBlock, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have variableRun := compatibilityEdges_currentVariable_eval true
        (variableIndex + 1) 0 vertex clauseIndex (.frameEnd :: tail) output
        (some .separator) buffer₂ test
      have variableRun' : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.currentVariable true) (some .separator)
            buffer₂ test [] output afterPolarity [] vertex clauseIndex 0)
          (some (compatibilityEdgesCfg (.currentEnd true) (some .separator)
            buffer₂ test [] output (.frameEnd :: tail) [] vertex clauseIndex
            (variableIndex + 1))) (2 * (variableIndex + 1) + 1) := by
        simpa [afterPolarity, encodeUnaryFrameBlock] using variableRun
      have endRun : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.currentEnd true) (some .separator) buffer₂
            test [] output (.frameEnd :: tail) [] vertex clauseIndex
            (variableIndex + 1))
          (some (compatibilityEdgesCfg (.priorStart true) (some .frameEnd)
            buffer₂ test [] output tail [] vertex clauseIndex
            (variableIndex + 1))) 1 := by
        exact ⟨⟨1, by
          simp [flip, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg,
            stepOp]⟩, le_rfl⟩
      let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (2 * vertex + 1) (2 * clauseIndex + 1) _ _ _ vertexRun clauseRun'
      let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ 2 _ _ _ first polarityRun
      let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ (2 * (variableIndex + 1) + 1) _ _ _ second variableRun'
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        _ 1 _ _ _ third endRun
      convert full using 1 <;>
        simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
          encodeUnaryFrame, occurrencePolarityCode, occurrencePolarityFlag,
          occurrenceVariableCode, encodeUnaryFrameBlock, afterVertex,
          afterPolarity, compatibilityEdgesCurrentRowSteps,
          List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]; omega

end TMClique
end Turing
end Chapter34
end CLRS
