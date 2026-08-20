import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionController
import Mathlib.Tactic

/-!
# Row-family execution for affine mux invocation progressions

This file lifts the exact single-row controller theorem to an arbitrary list
of arithmetic rows and separately verifies the segment-marker counter clear.
Keeping these inductions outside the fixed-program file limits rebuild cost
while exposing clean composition boundaries for the segment compiler.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Canonical frame reconstructed from one arithmetic source row. -/
def affineMuxInvocationFrameOfRow (selector selectorNot : Nat)
    (row : Nat × Nat × Nat) : AffineMuxFinPairFrame :=
  { whenTrue := row.1
    whenFalse := row.2.1
    selector := selector
    selectorNot := selectorNot
    trueArm := row.2.2
    falseArm := row.2.2 + 1 }

/-- Unary source consumed by the row loop. -/
def affineMuxInvocationRowsSource
    (rows : List (Nat × Nat × Nat)) : List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame (affineUnaryTripleRowValues row)

/-- Exact mux protocol emitted by the row loop. -/
def affineMuxInvocationRowsFrames (selector selectorNot : Nat)
    (rows : List (Nat × Nat × Nat)) : List UnaryFrameSym :=
  rows.flatMap fun row =>
    encodeAffineMuxFinPairFrame
      (affineMuxInvocationFrameOfRow selector selectorNot row)

/-- Exact controller cost of one arithmetic row. -/
def affineMuxInvocationProgressionControllerRowSteps
    (selector selectorNot : Nat) (row : Nat × Nat × Nat) : Nat :=
  2 * row.1 + 2 * row.2.1 + 5 * row.2.2 +
    5 * selector + 5 * selectorNot + 23

/-- Exact accumulated cost of a row family. -/
def affineMuxInvocationProgressionControllerRowsSteps
    (selector selectorNot : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | row :: rest =>
      affineMuxInvocationProgressionControllerRowSteps selector selectorNot row +
        affineMuxInvocationProgressionControllerRowsSteps selector selectorNot rest

/-- Empty row families preserve the incoming pop buffer; every nonempty family
ends with the normalized buffer produced by the single-row controller. -/
def affineMuxInvocationRowsFinalBuffer
    (rows : List (Nat × Nat × Nat))
    (buffer : Option UnaryFrameSym) : Option UnaryFrameSym :=
  match rows with
  | [] => buffer
  | _ :: _ => none

/-- Empty row families preserve the test bit; every nonempty family ends with
the normalized false bit produced by the single-row controller. -/
def affineMuxInvocationRowsFinalTest
    (rows : List (Nat × Nat × Nat)) (test : Bool) : Bool :=
  match rows with
  | [] => test
  | _ :: _ => false

@[simp] theorem affineMuxInvocationRowsFinalBuffer_none
    (rows : List (Nat × Nat × Nat)) :
    affineMuxInvocationRowsFinalBuffer rows none = none := by
  cases rows <;> rfl

@[simp] theorem affineMuxInvocationRowsFinalTest_false
    (rows : List (Nat × Nat × Nat)) :
    affineMuxInvocationRowsFinalTest rows false = false := by
  cases rows <;> rfl

/-- The fixed row loop expands every source row to exactly one existing mux
frame and returns to the same clean `dataCheck` boundary. -/
def affineMuxInvocationProgressionController_rows_emit
    (selector selectorNot : Nat) (rows : List (Nat × Nat × Nat))
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .dataCheck
        buffer₁ buffer₂ test
        (affineMuxInvocationRowsSource rows ++ tail) output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck
        (affineMuxInvocationRowsFinalBuffer rows buffer₁)
        buffer₂ (affineMuxInvocationRowsFinalTest rows test) tail
        ((affineMuxInvocationRowsFrames selector selectorNot rows).reverse ++
          output)
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []))
      (affineMuxInvocationProgressionControllerRowsSteps
        selector selectorNot rows) := by
  induction rows generalizing buffer₁ test output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons row rest ih =>
      let restInput := affineMuxInvocationRowsSource rest ++ tail
      let frame := affineMuxInvocationFrameOfRow selector selectorNot row
      let frameOutput := (encodeAffineMuxFinPairFrame frame).reverse ++ output
      have hrow : EvalsToInTime
          (step affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionControllerCfg .dataCheck
            buffer₁ buffer₂ test
            (affineMuxInvocationRowsSource (row :: rest) ++ tail)
            output [] [] (List.replicate selector ())
            (List.replicate selectorNot ()) [])
          (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
            buffer₂ false restInput frameOutput [] []
            (List.replicate selector ())
            (List.replicate selectorNot ()) []))
          (affineMuxInvocationProgressionControllerRowSteps
            selector selectorNot row) := by
        simpa [affineMuxInvocationRowsSource,
          affineMuxInvocationProgressionControllerRowSteps,
          affineMuxInvocationFrameOfRow, frame, frameOutput, restInput,
          affineUnaryTripleRowValues, List.append_assoc] using
          affineMuxInvocationProgressionController_row_emit
            row.1 row.2.1 row.2.2 selector selectorNot buffer₁ buffer₂
            test restInput output
      have hrest : EvalsToInTime
          (step affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionControllerCfg .dataCheck none
            buffer₂ false restInput frameOutput [] []
            (List.replicate selector ())
            (List.replicate selectorNot ()) [])
          (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
            buffer₂ false tail
            ((affineMuxInvocationRowsFrames selector selectorNot rest).reverse ++
              frameOutput)
            [] [] (List.replicate selector ())
            (List.replicate selectorNot ()) []))
          (affineMuxInvocationProgressionControllerRowsSteps
            selector selectorNot rest) := by
        simpa [restInput] using ih none false frameOutput
      let full := EvalsToInTime.trans
        (step affineMuxInvocationProgressionControllerRevProgram)
        (affineMuxInvocationProgressionControllerRowSteps
          selector selectorNot row)
        (affineMuxInvocationProgressionControllerRowsSteps
          selector selectorNot rest)
        _ _ _ hrow hrest
      convert full using 1
      · simp [affineMuxInvocationRowsFinalBuffer,
          affineMuxInvocationRowsFinalTest, affineMuxInvocationRowsFrames,
          frameOutput, frame,
          affineMuxInvocationFrameOfRow, List.reverse_append,
          List.append_assoc]
      · simp [affineMuxInvocationProgressionControllerRowsSteps,
          Nat.add_comm]

theorem affineMuxInvocationProgressionController_clearSelector_eval
    (selector : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym)
    (selectorNot scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[selector + 1]
      (some (affineMuxInvocationProgressionControllerCfg .clearSelector
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate selector ()) selectorNot scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .clearSelectorNot
        buffer₁ buffer₂ false input output work₁ work₂ []
        selectorNot scratch) := by
  induction selector generalizing test with
  | zero => rfl
  | succ selector ih =>
      rw [show selector + 1 + 1 = (selector + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            selector + 1]
          (some (affineMuxInvocationProgressionControllerCfg .clearSelector
            buffer₁ buffer₂ true input output work₁ work₂
            (List.replicate selector ()) selectorNot scratch)) = _
      simpa using ih true

theorem affineMuxInvocationProgressionController_clearSelectorNot_eval
    (selectorNot : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym)
    (selector scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        selectorNot + 1]
      (some (affineMuxInvocationProgressionControllerCfg .clearSelectorNot
        buffer₁ buffer₂ test input output work₁ work₂ selector
        (List.replicate selectorNot ()) scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .loadSelector
        buffer₁ buffer₂ false input output work₁ work₂ selector
        [] scratch) := by
  induction selectorNot generalizing test with
  | zero => rfl
  | succ selectorNot ih =>
      rw [show selectorNot + 1 + 1 = (selectorNot + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            selectorNot + 1]
          (some (affineMuxInvocationProgressionControllerCfg .clearSelectorNot
            buffer₁ buffer₂ true input output work₁ work₂ selector
            (List.replicate selectorNot ()) scratch)) = _
      simpa using ih true

/-- A segment marker is consumed and both retained selector counters are
cleared before the next segment boundary. -/
def affineMuxInvocationProgressionController_clearSegment
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .dataCheck
        buffer₁ buffer₂ test (.frameEnd :: tail) output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .loadSelector
        (some .frameEnd) buffer₂ false tail output [] [] [] [] []))
      (selector + selectorNot + 3) := by
  let beforeClearSelector :=
    affineMuxInvocationProgressionControllerCfg .clearSelector
      (some .frameEnd) buffer₂ test tail output [] []
      (List.replicate selector ()) (List.replicate selectorNot ()) []
  have hmarker : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .dataCheck
        buffer₁ buffer₂ test (.frameEnd :: tail) output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some beforeClearSelector) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeClearSelectorNot :=
    affineMuxInvocationProgressionControllerCfg .clearSelectorNot
      (some .frameEnd) buffer₂ false tail output [] [] []
      (List.replicate selectorNot ()) []
  have hselector : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeClearSelector (some beforeClearSelectorNot) (selector + 1) :=
    ⟨⟨selector + 1, by
      simpa [beforeClearSelector, beforeClearSelectorNot] using
        affineMuxInvocationProgressionController_clearSelector_eval selector
          (some .frameEnd) buffer₂ test tail output [] []
          (List.replicate selectorNot ()) []⟩, le_rfl⟩
  have hselectorNot : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeClearSelectorNot
      (some (affineMuxInvocationProgressionControllerCfg .loadSelector
        (some .frameEnd) buffer₂ false tail output [] [] [] [] []))
      (selectorNot + 1) :=
    ⟨⟨selectorNot + 1, by
      simpa [beforeClearSelectorNot] using
        affineMuxInvocationProgressionController_clearSelectorNot_eval
          selectorNot (some .frameEnd) buffer₂ false tail output [] [] [] []⟩,
      le_rfl⟩
  let first := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    1 (selector + 1) _ _ _ hmarker hselector
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (selectorNot + 1) _ _ _ first hselectorNot
  convert full using 1
  omega

end CLRS.Chapter34.Turing.PolyBuilder
