import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsCore
import Mathlib.Tactic

/-!
# Indexed occurrence rows: exact one-literal simulation

This file proves the local controller invariants: the persistent vertex and
clause counters are copied to reverse output and restored exactly, while the
literal's polarity and positive unary variable code are consumed from the
canonical occurrence stream.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private theorem occurrenceRows_replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem occurrenceRows_copyVertex_eval (vertex saved : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (input : List GraphSym) (output : List UnaryFrameSym)
    (clause : Nat) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[3 * vertex + 1]
      (some (occurrenceRowsCfg .copyVertex buffer test input output []
        vertex clause saved)) =
      some (occurrenceRowsCfg .pushVertexSep buffer false input
        (List.replicate vertex UnaryFrameSym.tick ++ output) []
        0 clause (saved + vertex)) := by
  induction vertex generalizing saved test output with
  | zero => rfl
  | succ vertex ih =>
      rw [show 3 * (vertex + 1) + 1 =
          (3 * vertex + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[3 * vertex + 1]
          (some (occurrenceRowsCfg .copyVertex buffer true input
            (.tick :: output) [] vertex clause (saved + 1))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, occurrenceRows_replicate_append_cons] using
        ih (saved + 1) true (.tick :: output)

private theorem occurrenceRows_restoreVertex_eval (saved restored : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (input : List GraphSym) (output : List UnaryFrameSym)
    (clause : Nat) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[2 * saved + 1]
      (some (occurrenceRowsCfg .restoreVertex buffer test input output []
        restored clause saved)) =
      some (occurrenceRowsCfg .copyClause buffer false input output []
        (restored + saved) clause 0) := by
  induction saved generalizing restored test with
  | zero => rfl
  | succ saved ih =>
      rw [show 2 * (saved + 1) + 1 = (2 * saved + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[2 * saved + 1]
          (some (occurrenceRowsCfg .restoreVertex buffer true input output []
            (restored + 1) clause saved)) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (restored + 1) true

private theorem occurrenceRows_copyClause_eval (clause saved : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (input : List GraphSym) (output : List UnaryFrameSym)
    (vertex : Nat) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[3 * clause + 1]
      (some (occurrenceRowsCfg .copyClause buffer test input output []
        vertex clause saved)) =
      some (occurrenceRowsCfg .pushClauseSep buffer false input
        (List.replicate clause UnaryFrameSym.tick ++ output) []
        vertex 0 (saved + clause)) := by
  induction clause generalizing saved test output with
  | zero => rfl
  | succ clause ih =>
      rw [show 3 * (clause + 1) + 1 =
          (3 * clause + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[3 * clause + 1]
          (some (occurrenceRowsCfg .copyClause buffer true input
            (.tick :: output) [] vertex clause (saved + 1))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, occurrenceRows_replicate_append_cons] using
        ih (saved + 1) true (.tick :: output)

private theorem occurrenceRows_restoreClause_eval (saved restored : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (input : List GraphSym) (output : List UnaryFrameSym)
    (vertex : Nat) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[2 * saved + 1]
      (some (occurrenceRowsCfg .restoreClause buffer test input output []
        vertex restored saved)) =
      some (occurrenceRowsCfg .readPolarity buffer false input output []
        vertex (restored + saved) 0) := by
  induction saved generalizing restored test with
  | zero => rfl
  | succ saved ih =>
      rw [show 2 * (saved + 1) + 1 = (2 * saved + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[2 * saved + 1]
          (some (occurrenceRowsCfg .restoreClause buffer true input output []
            vertex (restored + 1) saved)) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (restored + 1) true

private def occurrenceRows_countersRun (vertex clause : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (input : List GraphSym) (output : List UnaryFrameSym) :
    EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .copyVertex buffer test input output []
        vertex clause 0)
      (some (occurrenceRowsCfg .readPolarity buffer false input
        (UnaryFrameSym.separator ::
          List.replicate clause UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output)
        [] vertex clause 0))
      (5 * vertex + 5 * clause + 6) := by
  let copyVertex : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .copyVertex buffer test input output []
        vertex clause 0)
      (some (occurrenceRowsCfg .pushVertexSep buffer false input
        (List.replicate vertex UnaryFrameSym.tick ++ output) []
        0 clause vertex)) (3 * vertex + 1) :=
    ⟨⟨3 * vertex + 1, by
      simpa using occurrenceRows_copyVertex_eval vertex 0 buffer test input
        output clause⟩, le_rfl⟩
  let pushVertex : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .pushVertexSep buffer false input
        (List.replicate vertex UnaryFrameSym.tick ++ output) []
        0 clause vertex)
      (some (occurrenceRowsCfg .restoreVertex buffer false input
        (UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output) []
        0 clause vertex)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let restoreVertex : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .restoreVertex buffer false input
        (UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output) []
        0 clause vertex)
      (some (occurrenceRowsCfg .copyClause buffer false input
        (UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output) []
        vertex clause 0)) (2 * vertex + 1) :=
    ⟨⟨2 * vertex + 1, by
      simpa using occurrenceRows_restoreVertex_eval vertex 0 buffer false
        input (UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output) clause⟩,
      le_rfl⟩
  let copyClause : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .copyClause buffer false input
        (UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output) []
        vertex clause 0)
      (some (occurrenceRowsCfg .pushClauseSep buffer false input
        (List.replicate clause UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output) []
        vertex 0 clause)) (3 * clause + 1) :=
    ⟨⟨3 * clause + 1, by
      simpa [List.append_assoc] using
        occurrenceRows_copyClause_eval clause 0 buffer false input
          (UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output) vertex⟩,
      le_rfl⟩
  let pushClause : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .pushClauseSep buffer false input
        (List.replicate clause UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output) []
        vertex 0 clause)
      (some (occurrenceRowsCfg .restoreClause buffer false input
        (UnaryFrameSym.separator ::
          List.replicate clause UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output) []
        vertex 0 clause)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let restoreClause : EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg .restoreClause buffer false input
        (UnaryFrameSym.separator ::
          List.replicate clause UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output) []
        vertex 0 clause)
      (some (occurrenceRowsCfg .readPolarity buffer false input
        (UnaryFrameSym.separator ::
          List.replicate clause UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output) []
        vertex clause 0)) (2 * clause + 1) :=
    ⟨⟨2 * clause + 1, by
      simpa using occurrenceRows_restoreClause_eval clause 0 buffer false
        input
        (UnaryFrameSym.separator ::
          List.replicate clause UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate vertex UnaryFrameSym.tick ++ output) vertex⟩,
      le_rfl⟩
  let h₁ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    (3 * vertex + 1) 1 _ _ _ copyVertex pushVertex
  let h₂ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    _ (2 * vertex + 1) _ _ _ h₁ restoreVertex
  let h₃ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    _ (3 * clause + 1) _ _ _ h₂ copyClause
  let h₄ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    _ 1 _ _ _ h₃ pushClause
  let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
    _ (2 * clause + 1) _ _ _ h₄ restoreClause
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by omega)

private theorem occurrenceRows_variableRun_empty_eval (count : Nat)
    (buffer : Option GraphSym) (test : Bool)
    (output : List UnaryFrameSym) (vertex clause : Nat) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[2 * count + 1]
      (some (occurrenceRowsCfg .variableRun buffer test
        (List.replicate count .endMark) output [] vertex clause 0)) =
      some (occurrenceRowsCfg .pushVariableSep none test []
        (List.replicate count UnaryFrameSym.tick ++ output) []
        vertex clause 0) := by
  induction count generalizing buffer output with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[2 * count + 1]
          (some (occurrenceRowsCfg .variableRun (some .endMark) test
            (List.replicate count .endMark) (.tick :: output) []
            vertex clause 0)) = _
      simpa [List.replicate_succ, occurrenceRows_replicate_append_cons] using
        ih (some .endMark) (.tick :: output)

private theorem occurrenceRows_variableRun_boundary_eval (count : Nat)
    (boundary : GraphSym) (hboundary : boundary ≠ .endMark)
    (buffer : Option GraphSym) (test : Bool)
    (tail : List GraphSym) (output : List UnaryFrameSym)
    (vertex clause : Nat) :
    (flip Option.bind (step occurrenceRowsRevProgram))^[2 * count + 3]
      (some (occurrenceRowsCfg .variableRun buffer test
        (List.replicate count .endMark ++ boundary :: tail) output []
        vertex clause 0)) =
      some (occurrenceRowsCfg .pushVariableSep (some boundary) test
        (boundary :: tail)
        (List.replicate count UnaryFrameSym.tick ++ output) []
        vertex clause 0) := by
  induction count generalizing buffer output with
  | zero =>
      cases boundary <;> simp_all <;> rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 3 = (2 * count + 3) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step occurrenceRowsRevProgram))^[2 * count + 3]
          (some (occurrenceRowsCfg .variableRun (some .endMark) test
            (List.replicate count .endMark ++ boundary :: tail)
            (.tick :: output) [] vertex clause 0)) = _
      simpa [List.replicate_succ, occurrenceRows_replicate_append_cons] using
        ih (some .endMark) (.tick :: output)

/-- Exact local cost for one literal descriptor. -/
def occurrenceRowsLiteralSteps (vertex clause : Nat) (literal : Literal)
    (hasBoundary : Bool) : Nat :=
  5 * vertex + 5 * clause + 2 * occurrenceVariableCode literal + 14 +
    occurrencePolarityCode literal + (if hasBoundary then 2 else 0)

private theorem occurrenceRows_row_reverse (vertex clause : Nat)
    (literal : Literal) :
    (encodeUnaryFrame
        (indexedOccurrenceRowValues vertex
          { clauseIndex := clause, positionIndex := 0, literal }) ++
      [UnaryFrameSym.frameEnd]).reverse =
      UnaryFrameSym.frameEnd :: UnaryFrameSym.separator ::
        List.replicate (occurrenceVariableCode literal) UnaryFrameSym.tick ++
        UnaryFrameSym.separator ::
          List.replicate (occurrencePolarityCode literal) UnaryFrameSym.tick ++
          UnaryFrameSym.separator ::
            List.replicate clause UnaryFrameSym.tick ++
            UnaryFrameSym.separator ::
              List.replicate vertex UnaryFrameSym.tick := by
  cases literal <;>
    simp [indexedOccurrenceRowValues, occurrencePolarityCode,
      occurrenceVariableCode, encodeUnaryFrame, encodeUnaryFrameBlock,
      List.reverse_append]

/-- A literal at end of input becomes one complete reverse-order row and
advances the persistent vertex counter. -/
def occurrenceRows_literalRun_empty (vertex clause : Nat)
    (literal : Literal) (buffer : Option GraphSym) (test : Bool)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg (.scan true) buffer test
        (.vertexMark :: (match literal with
          | .pos index => .posMark :: .varMark ::
              List.replicate (index + 1) .endMark
          | .neg index => .negMark :: .varMark ::
              List.replicate (index + 1) .endMark))
        output [] vertex clause 0)
      (some (occurrenceRowsCfg (.scan true) none false []
        ((encodeUnaryFrame
          (indexedOccurrenceRowValues vertex
            { clauseIndex := clause, positionIndex := 0, literal }) ++
          [UnaryFrameSym.frameEnd]).reverse ++ output) []
        (vertex + 1) clause 0))
      (occurrenceRowsLiteralSteps vertex clause literal false) := by
  cases literal with
  | pos index =>
      let countersOutput := UnaryFrameSym.separator ::
        List.replicate clause UnaryFrameSym.tick ++
        UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output
      have scanVertex : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg (.scan true) buffer test
            (.vertexMark :: .posMark :: .varMark ::
              List.replicate (index + 1) .endMark)
            output [] vertex clause 0)
          (some (occurrenceRowsCfg .copyVertex (some .vertexMark) test
            (.posMark :: .varMark :: List.replicate (index + 1) .endMark)
            output [] vertex clause 0)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let counters := occurrenceRows_countersRun vertex clause
        (some .vertexMark) test
        (.posMark :: .varMark :: List.replicate (index + 1) .endMark)
        output
      have polarity : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .readPolarity (some .vertexMark) false
            (.posMark :: .varMark :: List.replicate (index + 1) .endMark)
            countersOutput [] vertex clause 0)
          (some (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark)
            (UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
      have variableRun : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark)
            (UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)
          (some (occurrenceRowsCfg .pushVariableSep none false []
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)) (2 * (index + 1) + 1) :=
        ⟨⟨2 * (index + 1) + 1, by
          simpa [List.append_assoc] using
            occurrenceRows_variableRun_empty_eval (index + 1)
              (some .varMark) false
              (UnaryFrameSym.separator :: countersOutput) vertex clause⟩,
          le_rfl⟩
      have finish : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .pushVariableSep none false []
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)
          (some (occurrenceRowsCfg (.scan true) none false []
            (UnaryFrameSym.frameEnd :: UnaryFrameSym.separator ::
              List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: countersOutput) []
            (vertex + 1) clause 0)) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        1 (5 * vertex + 5 * clause + 6) _ _ _ scanVertex counters
      let h₂ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 3 _ _ _ h₁ polarity
      let h₃ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ (2 * (index + 1) + 1) _ _ _ h₂ variableRun
      let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 3 _ _ _ h₃ finish
      have htime :
          3 + (2 * (index + 1) + 1 +
            (3 + (5 * vertex + 5 * clause + 6 + 1))) =
            occurrenceRowsLiteralSteps vertex clause (.pos index) false := by
        simp [occurrenceRowsLiteralSteps, occurrenceVariableCode,
          occurrencePolarityCode]
        omega
      rw [← htime]
      rw [occurrenceRows_row_reverse]
      simpa [countersOutput, occurrenceVariableCode,
        occurrencePolarityCode, List.append_assoc] using full
  | neg index =>
      let countersOutput := UnaryFrameSym.separator ::
        List.replicate clause UnaryFrameSym.tick ++
        UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output
      have scanVertex : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg (.scan true) buffer test
            (.vertexMark :: .negMark :: .varMark ::
              List.replicate (index + 1) .endMark)
            output [] vertex clause 0)
          (some (occurrenceRowsCfg .copyVertex (some .vertexMark) test
            (.negMark :: .varMark :: List.replicate (index + 1) .endMark)
            output [] vertex clause 0)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let counters := occurrenceRows_countersRun vertex clause
        (some .vertexMark) test
        (.negMark :: .varMark :: List.replicate (index + 1) .endMark)
        output
      have polarity : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .readPolarity (some .vertexMark) false
            (.negMark :: .varMark :: List.replicate (index + 1) .endMark)
            countersOutput [] vertex clause 0)
          (some (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark)
            (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
              countersOutput) [] vertex clause 0)) 4 :=
        ⟨⟨4, rfl⟩, le_rfl⟩
      have variableRun : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark)
            (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
              countersOutput) [] vertex clause 0)
          (some (occurrenceRowsCfg .pushVariableSep none false []
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) [] vertex clause 0))
            (2 * (index + 1) + 1) :=
        ⟨⟨2 * (index + 1) + 1, by
          simpa [List.append_assoc] using
            occurrenceRows_variableRun_empty_eval (index + 1)
              (some .varMark) false
              (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) vertex clause⟩, le_rfl⟩
      have finish : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .pushVariableSep none false []
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) [] vertex clause 0)
          (some (occurrenceRowsCfg (.scan true) none false []
            (UnaryFrameSym.frameEnd :: UnaryFrameSym.separator ::
              List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) [] (vertex + 1) clause 0)) 3 :=
        ⟨⟨3, rfl⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        1 (5 * vertex + 5 * clause + 6) _ _ _ scanVertex counters
      let h₂ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 4 _ _ _ h₁ polarity
      let h₃ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ (2 * (index + 1) + 1) _ _ _ h₂ variableRun
      let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 3 _ _ _ h₃ finish
      have htime :
          3 + (2 * (index + 1) + 1 +
            (4 + (5 * vertex + 5 * clause + 6 + 1))) =
            occurrenceRowsLiteralSteps vertex clause (.neg index) false := by
        simp [occurrenceRowsLiteralSteps, occurrenceVariableCode,
          occurrencePolarityCode]
        omega
      rw [← htime]
      rw [occurrenceRows_row_reverse]
      simpa [countersOutput, occurrenceVariableCode,
        occurrencePolarityCode, List.append_assoc] using full

/-- A literal before a non-variable boundary becomes one complete row and
leaves that boundary at the head of the input for the outer parser. -/
def occurrenceRows_literalRun_boundary (vertex clause : Nat)
    (literal : Literal) (boundary : GraphSym)
    (hboundary : boundary ≠ .endMark)
    (buffer : Option GraphSym) (test : Bool)
    (tail : List GraphSym) (output : List UnaryFrameSym) :
    EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg (.scan true) buffer test
        (.vertexMark :: (match literal with
          | .pos index => .posMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail
          | .neg index => .negMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail))
        output [] vertex clause 0)
      (some (occurrenceRowsCfg (.scan true) (some boundary) false
        (boundary :: tail)
        ((encodeUnaryFrame
          (indexedOccurrenceRowValues vertex
            { clauseIndex := clause, positionIndex := 0, literal }) ++
          [UnaryFrameSym.frameEnd]).reverse ++ output) []
        (vertex + 1) clause 0))
      (occurrenceRowsLiteralSteps vertex clause literal true) := by
  cases literal with
  | pos index =>
      let countersOutput := UnaryFrameSym.separator ::
        List.replicate clause UnaryFrameSym.tick ++
        UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output
      have scanVertex : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg (.scan true) buffer test
            (.vertexMark :: .posMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail)
            output [] vertex clause 0)
          (some (occurrenceRowsCfg .copyVertex (some .vertexMark) test
            (.posMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail)
            output [] vertex clause 0)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let counters := occurrenceRows_countersRun vertex clause
        (some .vertexMark) test
        (.posMark :: .varMark ::
          List.replicate (index + 1) .endMark ++ boundary :: tail)
        output
      have polarity : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .readPolarity (some .vertexMark) false
            (.posMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail)
            countersOutput [] vertex clause 0)
          (some (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark ++ boundary :: tail)
            (UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
      have variableRun : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark ++ boundary :: tail)
            (UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)
          (some (occurrenceRowsCfg .pushVariableSep (some boundary) false
            (boundary :: tail)
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)) (2 * (index + 1) + 3) :=
        ⟨⟨2 * (index + 1) + 3, by
          simpa [List.append_assoc] using
            occurrenceRows_variableRun_boundary_eval (index + 1)
              boundary hboundary (some .varMark) false tail
              (UnaryFrameSym.separator :: countersOutput) vertex clause⟩,
          le_rfl⟩
      have finish : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .pushVariableSep (some boundary) false
            (boundary :: tail)
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: countersOutput) []
            vertex clause 0)
          (some (occurrenceRowsCfg (.scan true) (some boundary) false
            (boundary :: tail)
            (UnaryFrameSym.frameEnd :: UnaryFrameSym.separator ::
              List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: countersOutput) []
            (vertex + 1) clause 0)) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        1 (5 * vertex + 5 * clause + 6) _ _ _ scanVertex counters
      let h₂ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 3 _ _ _ h₁ polarity
      let h₃ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ (2 * (index + 1) + 3) _ _ _ h₂ variableRun
      let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 3 _ _ _ h₃ finish
      have htime :
          3 + (2 * (index + 1) + 3 +
            (3 + (5 * vertex + 5 * clause + 6 + 1))) =
            occurrenceRowsLiteralSteps vertex clause (.pos index) true := by
        simp [occurrenceRowsLiteralSteps, occurrenceVariableCode,
          occurrencePolarityCode]
        omega
      rw [← htime]
      rw [occurrenceRows_row_reverse]
      simpa [countersOutput, occurrenceVariableCode,
        occurrencePolarityCode, List.append_assoc] using full
  | neg index =>
      let countersOutput := UnaryFrameSym.separator ::
        List.replicate clause UnaryFrameSym.tick ++
        UnaryFrameSym.separator ::
          List.replicate vertex UnaryFrameSym.tick ++ output
      have scanVertex : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg (.scan true) buffer test
            (.vertexMark :: .negMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail)
            output [] vertex clause 0)
          (some (occurrenceRowsCfg .copyVertex (some .vertexMark) test
            (.negMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail)
            output [] vertex clause 0)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let counters := occurrenceRows_countersRun vertex clause
        (some .vertexMark) test
        (.negMark :: .varMark ::
          List.replicate (index + 1) .endMark ++ boundary :: tail)
        output
      have polarity : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .readPolarity (some .vertexMark) false
            (.negMark :: .varMark ::
              List.replicate (index + 1) .endMark ++ boundary :: tail)
            countersOutput [] vertex clause 0)
          (some (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark ++ boundary :: tail)
            (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
              countersOutput) [] vertex clause 0)) 4 :=
        ⟨⟨4, rfl⟩, le_rfl⟩
      have variableRun : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .variableRun (some .varMark) false
            (List.replicate (index + 1) .endMark ++ boundary :: tail)
            (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
              countersOutput) [] vertex clause 0)
          (some (occurrenceRowsCfg .pushVariableSep (some boundary) false
            (boundary :: tail)
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) [] vertex clause 0))
            (2 * (index + 1) + 3) :=
        ⟨⟨2 * (index + 1) + 3, by
          simpa [List.append_assoc] using
            occurrenceRows_variableRun_boundary_eval (index + 1)
              boundary hboundary (some .varMark) false tail
              (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) vertex clause⟩, le_rfl⟩
      have finish : EvalsToInTime (step occurrenceRowsRevProgram)
          (occurrenceRowsCfg .pushVariableSep (some boundary) false
            (boundary :: tail)
            (List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) [] vertex clause 0)
          (some (occurrenceRowsCfg (.scan true) (some boundary) false
            (boundary :: tail)
            (UnaryFrameSym.frameEnd :: UnaryFrameSym.separator ::
              List.replicate (index + 1) UnaryFrameSym.tick ++
              UnaryFrameSym.separator :: UnaryFrameSym.tick ::
                countersOutput) [] (vertex + 1) clause 0)) 3 :=
        ⟨⟨3, rfl⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        1 (5 * vertex + 5 * clause + 6) _ _ _ scanVertex counters
      let h₂ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 4 _ _ _ h₁ polarity
      let h₃ := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ (2 * (index + 1) + 3) _ _ _ h₂ variableRun
      let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        _ 3 _ _ _ h₃ finish
      have htime :
          3 + (2 * (index + 1) + 3 +
            (4 + (5 * vertex + 5 * clause + 6 + 1))) =
            occurrenceRowsLiteralSteps vertex clause (.neg index) true := by
        simp [occurrenceRowsLiteralSteps, occurrenceVariableCode,
          occurrencePolarityCode]
        omega
      rw [← htime]
      rw [occurrenceRows_row_reverse]
      simpa [countersOutput, occurrenceVariableCode,
        occurrencePolarityCode, List.append_assoc] using full

end TMClique
end Turing
end Chapter34
end CLRS
