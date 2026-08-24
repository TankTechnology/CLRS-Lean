import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.CandidateRight

/-!
# HAM-CYCLE incidence scanner: occurrence descriptor emission
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder
open HamiltonianCycleReduction

private theorem replicate_cons_comm {alpha : Type} (n : Nat) (a : alpha)
    (tail : List alpha) :
    List.replicate n a ++ a :: tail =
      a :: List.replicate n a ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem unit_cons_replicate (n : Nat) :
    () :: List.replicate n () = List.replicate (n + 1) () := by
  rw [List.replicate_succ]

/-- Restore an occurrence counter from scratch after its unary digits have
been emitted. -/
def restoreOccurrence_run (remaining restored query : Nat)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .restoreOccurrenceInc buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate query ()) (List.replicate restored ())
        (List.replicate remaining ()))
      (some (cfg .advanceOccurrence buffer₁ buffer₂ false input output
        work₁ work₂ (List.replicate query ())
        (List.replicate (remaining + restored) ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing restored test with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg .restoreOccurrenceTick buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate query ())
        (List.replicate restored ()) (List.replicate remaining ())
      let afterInc := cfg .restoreOccurrenceInc buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate query ())
        (List.replicate (restored + 1) ()) (List.replicate remaining ())
      have first : EvalsToInTime (step program)
          (cfg .restoreOccurrenceInc buffer₁ buffer₂ test input output
            work₁ work₂ (List.replicate query ())
            (List.replicate restored ()) (List.replicate (remaining + 1) ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Emit the occurrence's unary digits while saving the counter in scratch. -/
def occurrenceTicks_run (remaining saved query : Nat) (side : Bool)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.emitOccurrence side) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate query ()) (List.replicate remaining ())
        (List.replicate saved ()))
      (some (cfg (.emitFirstSeparator side) buffer₁ buffer₂ false input
        (List.replicate remaining UnaryFrameSym.tick ++ output) work₁ work₂
        (List.replicate query ()) [] (List.replicate (remaining + saved) ())))
      (3 * remaining + 1) := by
  induction remaining generalizing saved test output with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterDec := cfg (.saveOccurrence side) buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate query ())
        (List.replicate remaining ()) (List.replicate saved ())
      let afterSave := cfg (.emitSideTick side) buffer₁ buffer₂ true input
        output work₁ work₂ (List.replicate query ())
        (List.replicate remaining ()) (List.replicate (saved + 1) ())
      let afterEmit := cfg (.emitOccurrence side) buffer₁ buffer₂ true input
        (UnaryFrameSym.tick :: output) work₁ work₂
        (List.replicate query ()) (List.replicate remaining ())
        (List.replicate (saved + 1) ())
      have first : EvalsToInTime (step program)
          (cfg (.emitOccurrence side) buffer₁ buffer₂ test input output work₁
            work₂ (List.replicate query ())
            (List.replicate (remaining + 1) ()) (List.replicate saved ()))
          (some afterDec) 1 :=
        ⟨⟨1, by simp [flip, afterDec, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterSave) 1 :=
        ⟨⟨1, by simp [flip, afterDec, afterSave, step, program, cfg,
          stepOp, unit_cons_replicate]⟩, le_rfl⟩
      have third : EvalsToInTime (step program) afterSave
          (some afterEmit) 1 :=
        ⟨⟨1, by simp [flip, afterSave, afterEmit, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
        (output := UnaryFrameSym.tick :: output)
      let throughSave := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let throughEmit := EvalsToInTime.trans (step program)
        2 1 _ afterSave _ throughSave third
      let full := EvalsToInTime.trans (step program)
        3 (3 * remaining + 1) _ afterEmit _ throughEmit rest
      simpa [List.replicate_succ, replicate_cons_comm, List.append_assoc, Nat.mul_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact descriptor emission cost, excluding the following occurrence
increment. -/
def emitOccurrenceSteps (occurrence : Nat) (side : Bool) : Nat :=
  5 * occurrence + if side then 5 else 4

/-- Emit `(occurrence, side)` in reverse physical order and restore all three
counters. -/
def emitOccurrence_run (query occurrence : Nat) (side : Bool)
    (input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.emitOccurrence side) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate query ()) (List.replicate occurrence ()) [])
      (some (cfg .advanceOccurrence buffer₁ buffer₂ false input
        ((encodeIncidentOccurrence
          { occurrence := occurrence, rightSide := side }).reverse ++ output)
        work₁ work₂ (List.replicate query ())
        (List.replicate occurrence ()) []))
      (emitOccurrenceSteps occurrence side) := by
  have ticks := occurrenceTicks_run occurrence 0 query side input output
    work₁ work₂ buffer₁ buffer₂ test
  cases side with
  | false =>
      let afterFirst := cfg .restoreOccurrence buffer₁ buffer₂ false input
        (UnaryFrameSym.separator ::
          List.replicate occurrence UnaryFrameSym.tick ++ output)
        work₁ work₂ (List.replicate query ()) []
        (List.replicate occurrence ())
      let afterSecond := cfg .restoreOccurrenceInc buffer₁ buffer₂ false input
        (UnaryFrameSym.separator :: UnaryFrameSym.separator ::
          List.replicate occurrence UnaryFrameSym.tick ++ output)
        work₁ work₂ (List.replicate query ()) []
        (List.replicate occurrence ())
      have first : EvalsToInTime (step program)
          (cfg (.emitFirstSeparator false) buffer₁ buffer₂ false input
            (List.replicate occurrence UnaryFrameSym.tick ++ output)
            work₁ work₂ (List.replicate query ()) []
            (List.replicate occurrence ()))
          (some afterFirst) 1 :=
        ⟨⟨1, by simp [flip, afterFirst, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterFirst
          (some afterSecond) 1 :=
        ⟨⟨1, by simp [flip, afterFirst, afterSecond, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have restore := restoreOccurrence_run occurrence 0 query input
        (UnaryFrameSym.separator :: UnaryFrameSym.separator ::
          List.replicate occurrence UnaryFrameSym.tick ++ output)
        work₁ work₂ buffer₁ buffer₂ false
      let throughFirst := EvalsToInTime.trans (step program)
        (3 * occurrence + 1) 1 _ _ _ ticks first
      let throughSecond := EvalsToInTime.trans (step program)
        _ 1 _ afterFirst _ throughFirst second
      let full := EvalsToInTime.trans (step program)
        _ (2 * occurrence + 1) _ afterSecond _ throughSecond restore
      convert full using 1
      all_goals simp [emitOccurrenceSteps, encodeIncidentOccurrence, sideValue,
        encodeUnaryFrame, encodeUnaryFrameBlock, List.reverse_append,
        List.reverse_replicate, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
      omega
  | true =>
      let afterFirst := cfg .emitSecondSeparator buffer₁ buffer₂ false input
        (UnaryFrameSym.separator ::
          List.replicate occurrence UnaryFrameSym.tick ++ output)
        work₁ work₂ (List.replicate query ()) []
        (List.replicate occurrence ())
      let afterSide := cfg .restoreOccurrence buffer₁ buffer₂ false input
        (UnaryFrameSym.tick :: UnaryFrameSym.separator ::
          List.replicate occurrence UnaryFrameSym.tick ++ output)
        work₁ work₂ (List.replicate query ()) []
        (List.replicate occurrence ())
      let afterSecond := cfg .restoreOccurrenceInc buffer₁ buffer₂ false input
        (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
          UnaryFrameSym.separator ::
          List.replicate occurrence UnaryFrameSym.tick ++ output)
        work₁ work₂ (List.replicate query ()) []
        (List.replicate occurrence ())
      have first : EvalsToInTime (step program)
          (cfg (.emitFirstSeparator true) buffer₁ buffer₂ false input
            (List.replicate occurrence UnaryFrameSym.tick ++ output)
            work₁ work₂ (List.replicate query ()) []
            (List.replicate occurrence ()))
          (some afterFirst) 1 :=
        ⟨⟨1, by simp [flip, afterFirst, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterFirst
          (some afterSide) 1 :=
        ⟨⟨1, by simp [flip, afterFirst, afterSide, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have third : EvalsToInTime (step program) afterSide
          (some afterSecond) 1 :=
        ⟨⟨1, by simp [flip, afterSide, afterSecond, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have restore := restoreOccurrence_run occurrence 0 query input
        (UnaryFrameSym.separator :: UnaryFrameSym.tick ::
          UnaryFrameSym.separator ::
          List.replicate occurrence UnaryFrameSym.tick ++ output)
        work₁ work₂ buffer₁ buffer₂ false
      let throughFirst := EvalsToInTime.trans (step program)
        (3 * occurrence + 1) 1 _ _ _ ticks first
      let throughSide := EvalsToInTime.trans (step program)
        _ 1 _ afterFirst _ throughFirst second
      let throughSecond := EvalsToInTime.trans (step program)
        _ 1 _ afterSide _ throughSide third
      let full := EvalsToInTime.trans (step program)
        _ (2 * occurrence + 1) _ afterSecond _ throughSecond restore
      convert full using 1
      all_goals simp [emitOccurrenceSteps, encodeIncidentOccurrence, sideValue,
        encodeUnaryFrame, encodeUnaryFrameBlock, List.reverse_append,
        List.reverse_replicate, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
      omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner
