import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedOrPairFormatCore
import Mathlib.Tactic

/-!
# Formatting marked operand pairs as finite-OR frames: exact simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev formatStep := step unaryFrameMarkedOrPairFormatRevProgram

private theorem replicate_tick_rotate (count : Nat) :
    List.replicate count UnaryFrameSym.tick ++ [UnaryFrameSym.tick] =
      UnaryFrameSym.tick :: List.replicate count UnaryFrameSym.tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append, ih]

private theorem tick_replicate_commute (count : Nat)
    (tail : List UnaryFrameSym) :
    UnaryFrameSym.tick ::
        (List.replicate count UnaryFrameSym.tick ++ tail) =
      List.replicate count UnaryFrameSym.tick ++
        UnaryFrameSym.tick :: tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append, List.cons_append]
      exact congrArg (List.cons UnaryFrameSym.tick) ih

/-- Scan the remaining left ticks and its terminating separator. -/
private def format_leftTicks_run
    (count : Nat) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) :
    EvalsToInTime formatStep
      (unaryFrameMarkedOrPairFormatCfg .scanLeft buffer
        (List.replicate count UnaryFrameSym.tick ++
          UnaryFrameSym.separator :: tail) output)
      (some (unaryFrameMarkedOrPairFormatCfg .emitZero
        (some .separator) tail
        ((List.replicate count UnaryFrameSym.tick ++
          [UnaryFrameSym.separator]).reverse ++ output)))
      (2 * count + 2) := by
  induction count generalizing buffer output with
  | zero => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | succ count ih =>
      have hfirst : EvalsToInTime formatStep
          (unaryFrameMarkedOrPairFormatCfg .scanLeft buffer
            (.tick :: List.replicate count .tick ++
              .separator :: tail) output)
          (some (unaryFrameMarkedOrPairFormatCfg .scanLeft
            (some .tick)
            (List.replicate count .tick ++ .separator :: tail)
            (.tick :: output))) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
      have hrest := ih (output := .tick :: output) (some .tick)
      let full := EvalsToInTime.trans formatStep 2 (2 * count + 2) _ _ _
        hfirst hrest
      rw [List.replicate_succ]
      convert full using 1 <;>
        simp [List.reverse_append, List.append_assoc] <;> omega

/-- Scan the right ticks, increment the value by one, retain its separator,
consume the row marker, and return to the row loop. -/
private def format_rightTicks_run
    (count : Nat) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) :
    EvalsToInTime formatStep
      (unaryFrameMarkedOrPairFormatCfg .scanRight buffer
        (List.replicate count UnaryFrameSym.tick ++
          [UnaryFrameSym.separator, UnaryFrameSym.frameEnd] ++ tail) output)
      (some (unaryFrameMarkedOrPairFormatCfg .beginRow
        (some .frameEnd) tail
        ((List.replicate count UnaryFrameSym.tick ++
          [UnaryFrameSym.tick, UnaryFrameSym.separator,
            UnaryFrameSym.frameEnd]).reverse ++ output)))
      (2 * count + 5) := by
  induction count generalizing buffer output with
  | zero => exact ⟨⟨5, rfl⟩, le_rfl⟩
  | succ count ih =>
      have hfirst : EvalsToInTime formatStep
          (unaryFrameMarkedOrPairFormatCfg .scanRight buffer
            (.tick :: List.replicate count .tick ++
              [.separator, .frameEnd] ++ tail) output)
          (some (unaryFrameMarkedOrPairFormatCfg .scanRight
            (some .tick)
            (List.replicate count .tick ++
              [.separator, .frameEnd] ++ tail)
            (.tick :: output))) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
      have hrest := ih (output := .tick :: output) (some .tick)
      let full := EvalsToInTime.trans formatStep 2 (2 * count + 5) _ _ _
        hfirst hrest
      rw [List.replicate_succ]
      convert full using 1 <;>
        simp [List.reverse_append, List.append_assoc] <;> omega

/-- Exact execution for one well-formed operand pair. -/
private def format_onePair_run
    (frame : AffineOrFinPairFrame)
    (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) :
    EvalsToInTime formatStep
      (unaryFrameMarkedOrPairFormatCfg .beginRow buffer
        (encodeAffineOrFinMarkedPairFrame frame ++ tail) output)
      (some (unaryFrameMarkedOrPairFormatCfg .beginRow
        (some .frameEnd) tail
        ((encodeAffineOrFinPairFrame frame).reverse ++ output)))
      (2 * (frame.left + frame.right) + 9) := by
  let rightInput := List.replicate frame.right UnaryFrameSym.tick ++
    [UnaryFrameSym.separator, UnaryFrameSym.frameEnd] ++ tail
  cases hleft : frame.left with
  | zero =>
      let beforeRight := unaryFrameMarkedOrPairFormatCfg .scanRight
        (some .separator)
        rightInput
        (.separator :: .separator :: .frameEnd :: output)
      have hprefix : EvalsToInTime formatStep
          (unaryFrameMarkedOrPairFormatCfg .beginRow buffer
            (encodeAffineOrFinMarkedPairFrame frame ++ tail) output)
          (some beforeRight) 4 := by
        have raw : EvalsToInTime formatStep
            (unaryFrameMarkedOrPairFormatCfg .beginRow buffer
              (.separator :: rightInput) output)
            (some beforeRight) 4 := ⟨⟨4, rfl⟩, le_rfl⟩
        simpa [encodeAffineOrFinMarkedPairFrame,
          encodeUnaryFrame, encodeUnaryFrameBlock, rightInput,
          hleft, List.append_assoc] using raw
      have hright := format_rightTicks_run frame.right tail
        (.separator :: .separator :: .frameEnd :: output) (some .separator)
      let full := EvalsToInTime.trans formatStep 4
        (2 * frame.right + 5) _ beforeRight _ hprefix
        (by simpa [beforeRight, rightInput] using hright)
      convert full using 1 <;> simp [encodeAffineOrFinPairFrame, encodeUnaryFrame,
        encodeUnaryFrameBlock, hleft, List.replicate_succ,
        replicate_tick_rotate,
        Nat.add_comm, List.reverse_append,
        List.append_assoc] <;> omega
  | succ left =>
      let afterFirst := unaryFrameMarkedOrPairFormatCfg .scanLeft
        (some .tick)
        (List.replicate left .tick ++ .separator :: rightInput)
        (.tick :: .frameEnd :: output)
      have hfirst : EvalsToInTime formatStep
          (unaryFrameMarkedOrPairFormatCfg .beginRow buffer
            (encodeAffineOrFinMarkedPairFrame frame ++ tail) output)
          (some afterFirst) 3 := by
        have raw : EvalsToInTime formatStep
            (unaryFrameMarkedOrPairFormatCfg .beginRow buffer
              (.tick :: List.replicate left .tick ++
                .separator :: rightInput) output)
            (some afterFirst) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
        simpa [encodeAffineOrFinMarkedPairFrame,
          encodeUnaryFrame, encodeUnaryFrameBlock, rightInput,
          hleft, List.replicate_succ, List.append_assoc] using raw
      have hleftRun := format_leftTicks_run left rightInput
        (.tick :: .frameEnd :: output) (some .tick)
      let beforeZero := unaryFrameMarkedOrPairFormatCfg .emitZero
        (some .separator) rightInput
        ((List.replicate left UnaryFrameSym.tick ++
          [UnaryFrameSym.separator]).reverse ++
          UnaryFrameSym.tick :: UnaryFrameSym.frameEnd :: output)
      let afterZero := unaryFrameMarkedOrPairFormatCfg .scanRight
        (some .separator) rightInput
        (UnaryFrameSym.separator ::
          ((List.replicate left UnaryFrameSym.tick ++
            [UnaryFrameSym.separator]).reverse ++
          UnaryFrameSym.tick :: UnaryFrameSym.frameEnd :: output))
      have hzero : EvalsToInTime formatStep beforeZero
          (some afterZero) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let t₁ := EvalsToInTime.trans formatStep 3 (2 * left + 2) _
        afterFirst beforeZero hfirst
        (by simpa [afterFirst, beforeZero] using hleftRun)
      let t₂ := EvalsToInTime.trans formatStep (2 * left + 5) 1 _
        beforeZero _ t₁ hzero
      have t₂' : EvalsToInTime formatStep
          (unaryFrameMarkedOrPairFormatCfg .beginRow buffer
            (encodeAffineOrFinMarkedPairFrame frame ++ tail) output)
          (some afterZero)
          (2 * left + 6) := by
        convert t₂ using 1 <;> omega
      have hright := format_rightTicks_run frame.right tail
        (UnaryFrameSym.separator ::
          (List.replicate left UnaryFrameSym.tick ++
            [UnaryFrameSym.separator]).reverse ++
          UnaryFrameSym.tick :: UnaryFrameSym.frameEnd :: output)
        (some .separator)
      let full := EvalsToInTime.trans formatStep (2 * left + 6)
        (2 * frame.right + 5) _ afterZero _ t₂'
        (by simpa [afterZero, rightInput, List.append_assoc] using hright)
      convert full using 1 <;> simp [encodeAffineOrFinPairFrame, encodeUnaryFrame,
        encodeUnaryFrameBlock, hleft, List.replicate_succ,
        tick_replicate_commute,
        Nat.add_comm,
        List.reverse_append, List.append_assoc] <;> omega

def unaryFrameMarkedOrPairFormatRevSteps
    (frames : List AffineOrFinPairFrame) : Nat :=
  (frames.map fun frame => 2 * (frame.left + frame.right) + 9).sum + 2

/-- Exact clean-halt execution of the complete frame family. -/
def unaryFrameMarkedOrPairFormatRev_run
    (frames : List AffineOrFinPairFrame) :
    EvalsToInTime formatStep
      (initialCfg unaryFrameMarkedOrPairFormatRevProgram
        (encodeAffineOrFinMarkedPairFrames frames))
      (some (haltCfg unaryFrameMarkedOrPairFormatRevProgram
        (encodeAffineOrFinFrames frames).reverse))
      (unaryFrameMarkedOrPairFormatRevSteps frames) := by
  change EvalsToInTime formatStep
    (unaryFrameMarkedOrPairFormatCfg .beginRow none
      (encodeAffineOrFinMarkedPairFrames frames) [])
    (some (haltCfg unaryFrameMarkedOrPairFormatRevProgram
      (encodeAffineOrFinFrames frames).reverse))
    (unaryFrameMarkedOrPairFormatRevSteps frames)
  let rowsRun : ∀ (rows : List AffineOrFinPairFrame)
      (buffer : Option UnaryFrameSym) (output : List UnaryFrameSym),
      EvalsToInTime formatStep
        (unaryFrameMarkedOrPairFormatCfg .beginRow buffer
          (encodeAffineOrFinMarkedPairFrames rows) output)
        (some (unaryFrameMarkedOrPairFormatCfg .beginRow
          (if rows.isEmpty then buffer else some .frameEnd) []
          ((encodeAffineOrFinFrames rows).reverse ++ output)))
        ((rows.map fun frame =>
          2 * (frame.left + frame.right) + 9).sum) := by
    intro rows buffer output
    induction rows generalizing buffer output with
    | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
    | cons frame rest ih =>
        let rowOutput := (encodeAffineOrFinPairFrame frame).reverse ++ output
        have hone := format_onePair_run frame
          (encodeAffineOrFinMarkedPairFrames rest) output buffer
        have hrest := ih (some .frameEnd) rowOutput
        let full := EvalsToInTime.trans formatStep
          (2 * (frame.left + frame.right) + 9)
          ((rest.map fun item => 2 * (item.left + item.right) + 9).sum) _
          (unaryFrameMarkedOrPairFormatCfg .beginRow (some .frameEnd)
            (encodeAffineOrFinMarkedPairFrames rest) rowOutput) _
          (by simpa [encodeAffineOrFinMarkedPairFrames, rowOutput] using hone)
          (by simpa [rowOutput] using hrest)
        simpa [encodeAffineOrFinMarkedPairFrames, encodeAffineOrFinFrames,
          rowOutput, List.reverse_append, List.append_assoc,
          Nat.add_comm] using full
  have hrows := rowsRun frames none []
  let beforeHalt := unaryFrameMarkedOrPairFormatCfg .beginRow
    (if frames.isEmpty then none else some .frameEnd) []
    (encodeAffineOrFinFrames frames).reverse
  have hhalt : EvalsToInTime formatStep beforeHalt
      (some (haltCfg unaryFrameMarkedOrPairFormatRevProgram
        (encodeAffineOrFinFrames frames).reverse)) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans formatStep
    ((frames.map fun frame =>
      2 * (frame.left + frame.right) + 9).sum) 2 _ beforeHalt _
    (by simpa [beforeHalt] using hrows)
    hhalt
  simpa [unaryFrameMarkedOrPairFormatRevSteps, Nat.add_comm] using full

end CLRS.Chapter34.Turing.PolyBuilder
