import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Basic
import Mathlib.Tactic

/-!
# Certificate pair-row generator: one-row simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator

open PolyBuilder

private theorem replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem readVertex_eval (vertex : Nat)
    (buffer : Option CliqueSym) (test : Bool)
    (tail : List CliqueSym) (output : List UnaryFrameSym)
    (position scratch : Nat) :
    (flip Option.bind (step revProgram))^[2 * vertex + 1]
      (some (cfg .vertex buffer test
        (List.replicate vertex CliqueSym.tick ++
          CliqueSym.recordEnd :: tail)
        output (List.replicate position ())
        (List.replicate scratch ()))) =
      some (cfg .pushVertexSeparator (some .recordEnd) test tail
        (List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate position ()) (List.replicate scratch ())) := by
  induction vertex generalizing buffer output with
  | zero => rfl
  | succ vertex ih =>
      rw [show 2 * (vertex + 1) + 1 = (2 * vertex + 1) + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[2 * vertex + 1]
          (some (cfg .vertex (some .tick) test
            (List.replicate vertex CliqueSym.tick ++
              CliqueSym.recordEnd :: tail)
            (.tick :: output) (List.replicate position ())
            (List.replicate scratch ()))) = _
      simpa [List.replicate_succ, replicate_append_cons] using
        ih (some .tick) (.tick :: output)

private theorem copyPosition_eval (position saved : Nat)
    (buffer : Option CliqueSym) (test : Bool)
    (input : List CliqueSym) (output : List UnaryFrameSym) :
    (flip Option.bind (step revProgram))^[3 * position + 1]
      (some (cfg .copyPosition buffer test input output
        (List.replicate position ()) (List.replicate saved ()))) =
      some (cfg .pushPositionSeparator buffer false input
        (List.replicate position UnaryFrameSym.tick ++ output) []
        (List.replicate (saved + position) ())) := by
  induction position generalizing saved test output with
  | zero => rfl
  | succ position ih =>
      rw [show 3 * (position + 1) + 1 =
          (3 * position + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[3 * position + 1]
          (some (cfg .copyPosition buffer true input (.tick :: output)
            (List.replicate position ())
            (List.replicate (saved + 1) ()))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, replicate_append_cons] using
        ih (saved + 1) true (.tick :: output)

private theorem restorePosition_eval (saved restored : Nat)
    (buffer : Option CliqueSym) (test : Bool)
    (input : List CliqueSym) (output : List UnaryFrameSym) :
    (flip Option.bind (step revProgram))^[2 * saved + 1]
      (some (cfg .restorePosition buffer test input output
        (List.replicate restored ()) (List.replicate saved ()))) =
      some (cfg .pushPolaritySeparator buffer false input output
        (List.replicate (restored + saved) ()) []) := by
  induction saved generalizing restored test with
  | zero => rfl
  | succ saved ih =>
      rw [show 2 * (saved + 1) + 1 =
          (2 * saved + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[2 * saved + 1]
          (some (cfg .restorePosition buffer true input output
            (List.replicate (restored + 1) ())
            (List.replicate saved ()))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (restored + 1) true

/-- Exact run for one canonical certificate vertex, returning to the clean
row boundary with the position counter advanced once. -/
def rowRun (position vertex : Nat) (tail : List CliqueSym)
    (output : List UnaryFrameSym) (buffer : Option CliqueSym)
    (test : Bool) :
    EvalsToInTime (step revProgram)
      (cfg .vertex buffer test
        ((encodeCliqueVertex vertex).tail ++ tail)
        output (List.replicate position ()) [])
      (some (cfg .scan (some .recordEnd) false tail
        ((TMClique.encodeIndexedOccurrenceEntry
          (certificatePairOccurrence position, vertex)).reverse ++ output)
        (List.replicate (position + 1) ()) []))
      (2 * vertex + 5 * position + 10) := by
  have read : EvalsToInTime (step revProgram)
      (cfg .vertex buffer test
        ((encodeCliqueVertex vertex).tail ++ tail)
        output (List.replicate position ()) [])
      (some (cfg .pushVertexSeparator (some .recordEnd) test tail
        (List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate position ()) []))
      (2 * vertex + 1) :=
    ⟨⟨2 * vertex + 1, by
      simpa [encodeCliqueVertex, prependCliqueTicks_eq_replicate] using
        readVertex_eval vertex buffer test tail output position 0⟩, le_rfl⟩
  have vertexSeparator : EvalsToInTime (step revProgram)
      (cfg .pushVertexSeparator (some .recordEnd) test tail
        (List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate position ()) [])
      (some (cfg .copyPosition (some .recordEnd) test tail
        (.separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate position ()) [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have copy : EvalsToInTime (step revProgram)
      (cfg .copyPosition (some .recordEnd) test tail
        (.separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate position ()) [])
      (some (cfg .pushPositionSeparator (some .recordEnd) false tail
        (List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        [] (List.replicate position ())))
      (3 * position + 1) :=
    ⟨⟨3 * position + 1, by
      simpa [List.append_assoc] using copyPosition_eval position 0
        (some .recordEnd) test tail
        (.separator :: List.replicate vertex UnaryFrameSym.tick ++ output)⟩,
      le_rfl⟩
  have positionSeparator : EvalsToInTime (step revProgram)
      (cfg .pushPositionSeparator (some .recordEnd) false tail
        (List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        [] (List.replicate position ()))
      (some (cfg .restorePosition (some .recordEnd) false tail
        (.separator :: List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        [] (List.replicate position ()))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have restore : EvalsToInTime (step revProgram)
      (cfg .restorePosition (some .recordEnd) false tail
        (.separator :: List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        [] (List.replicate position ()))
      (some (cfg .pushPolaritySeparator (some .recordEnd) false tail
        (.separator :: List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate position ()) []))
      (2 * position + 1) :=
    ⟨⟨2 * position + 1, by
      simpa using restorePosition_eval position 0 (some .recordEnd) false tail
        (.separator :: List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)⟩,
      le_rfl⟩
  let afterPolarity := cfg .pushVariableTick (some .recordEnd) false tail
    (.separator :: .separator ::
      List.replicate position UnaryFrameSym.tick ++
      .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
    (List.replicate position ()) []
  let afterVariableTick := cfg .pushVariableSeparator (some .recordEnd) false
    tail (.tick :: .separator :: .separator ::
      List.replicate position UnaryFrameSym.tick ++
      .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
    (List.replicate position ()) []
  let afterVariableSeparator := cfg .pushRowEnd (some .recordEnd) false tail
    (.separator :: .tick :: .separator :: .separator ::
      List.replicate position UnaryFrameSym.tick ++
      .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
    (List.replicate position ()) []
  let afterRowEnd := cfg .advancePosition (some .recordEnd) false tail
    (.frameEnd :: .separator :: .tick :: .separator :: .separator ::
      List.replicate position UnaryFrameSym.tick ++
      .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
    (List.replicate position ()) []
  have finish : EvalsToInTime (step revProgram)
      (cfg .pushPolaritySeparator (some .recordEnd) false tail
        (.separator :: List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate position ()) [])
      (some (cfg .scan (some .recordEnd) false tail
        (.frameEnd :: .separator :: .tick :: .separator :: .separator ::
          List.replicate position UnaryFrameSym.tick ++
          .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
        (List.replicate (position + 1) ()) [])) 5 := by
    have pushPolarity : EvalsToInTime (step revProgram)
        (cfg .pushPolaritySeparator (some .recordEnd) false tail
          (.separator :: List.replicate position UnaryFrameSym.tick ++
            .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
          (List.replicate position ()) [])
        (some afterPolarity) 1 :=
      ⟨⟨1, rfl⟩, le_rfl⟩
    have pushVariable : EvalsToInTime (step revProgram)
        afterPolarity (some afterVariableTick) 1 :=
      ⟨⟨1, rfl⟩, le_rfl⟩
    have pushVariableSeparator : EvalsToInTime (step revProgram)
        afterVariableTick (some afterVariableSeparator) 1 :=
      ⟨⟨1, rfl⟩, le_rfl⟩
    have pushEnd : EvalsToInTime (step revProgram)
        afterVariableSeparator (some afterRowEnd) 1 :=
      ⟨⟨1, rfl⟩, le_rfl⟩
    have advance : EvalsToInTime (step revProgram)
        afterRowEnd
        (some (cfg .scan (some .recordEnd) false tail
          (.frameEnd :: .separator :: .tick :: .separator :: .separator ::
            List.replicate position UnaryFrameSym.tick ++
            .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
          (List.replicate (position + 1) ()) [])) 1 := by
      simpa [afterRowEnd, List.replicate_succ] using
        (show EvalsToInTime (step revProgram) afterRowEnd
            (some (cfg .scan (some .recordEnd) false tail
              (.frameEnd :: .separator :: .tick :: .separator :: .separator ::
                List.replicate position UnaryFrameSym.tick ++
                .separator :: List.replicate vertex UnaryFrameSym.tick ++ output)
              (() :: List.replicate position ()) [])) 1 from
          ⟨⟨1, rfl⟩, le_rfl⟩)
    let firstFinish := EvalsToInTime.trans (step revProgram)
      1 1 _ _ _ pushPolarity pushVariable
    let secondFinish := EvalsToInTime.trans (step revProgram)
      _ 1 _ _ _ firstFinish pushVariableSeparator
    let thirdFinish := EvalsToInTime.trans (step revProgram)
      _ 1 _ _ _ secondFinish pushEnd
    let fullFinish := EvalsToInTime.trans (step revProgram)
      _ 1 _ _ _ thirdFinish advance
    exact fullFinish
  let first := EvalsToInTime.trans (step revProgram)
    (2 * vertex + 1) 1 _ _ _ read vertexSeparator
  let second := EvalsToInTime.trans (step revProgram)
    _ (3 * position + 1) _ _ _ first copy
  let third := EvalsToInTime.trans (step revProgram)
    _ 1 _ _ _ second positionSeparator
  let fourth := EvalsToInTime.trans (step revProgram)
    _ (2 * position + 1) _ _ _ third restore
  let full := EvalsToInTime.trans (step revProgram) _ 5 _ _ _ fourth finish
  convert full using 1 <;>
    simp [encode_certificatePairEntry, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.replicate_succ, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]
  omega

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.PairGenerator
