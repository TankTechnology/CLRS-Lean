import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Runtime affine unary progressions

Cook--Levin row operands advance by a runtime stride: row {lit}`i` uses values
of the form {lit}`base + i * step`.  This module supplies a fixed counter
machine for that operation.  Its structured input contains three
delimiter-bearing unary values {lit}`(base, step, count)`; its output is the
exact unary frame family for all {lit}`count` affine values.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

set_option maxRecDepth 2048

/-- Runtime parameters for one finite affine progression. -/
structure AffineUnaryProgression where
  base : Nat
  step : Nat
  count : Nat
deriving DecidableEq, Repr

/-- Canonical three-field input of the affine progression controller. -/
def encodeAffineUnaryProgression
    (progression : AffineUnaryProgression) : List UnaryFrameSym :=
  encodeUnaryFrame [progression.base, progression.step, progression.count]

/-- Natural affine values starting from an arbitrary current value. -/
def affineUnaryProgressionValuesFrom : Nat → Nat → Nat → List Nat
  | _, _, 0 => []
  | current, stride, count + 1 =>
      current :: affineUnaryProgressionValuesFrom
        (current + stride) stride count

/-- The natural values produced by an affine progression. -/
def affineUnaryProgressionValues
    (progression : AffineUnaryProgression) : List Nat :=
  affineUnaryProgressionValuesFrom
    progression.base progression.step progression.count

/-- Closed positional form of the recursive affine values. -/
theorem affineUnaryProgressionValuesFrom_eq_ofFn
    (base stride count : Nat) :
    affineUnaryProgressionValuesFrom base stride count =
      List.ofFn fun index : Fin count => base + index.val * stride := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      rw [affineUnaryProgressionValuesFrom, List.ofFn_succ]
      congr 1
      · simp
      · rw [ih]
        apply List.ofFn_inj.mpr
        funext index
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact delimiter-bearing forward output. -/
def affineUnaryProgressionFrameStream
    (progression : AffineUnaryProgression) : List UnaryFrameSym :=
  encodeUnaryFrame (affineUnaryProgressionValues progression)

/-- Finite control for the reversed affine progression streamer. -/
inductive AffineUnaryProgressionLabel
  | loadBase | incBase
  | loadStep | saveStep
  | next
  | emitCurrent | saveCurrent | pushTick | pushSeparator
  | restoreCurrent | restoreCurrentInc
  | advance | advanceInc | restoreStep
  | clearCurrent | clearStep
  | halt | invalid
deriving DecidableEq, Fintype

/-- A fixed program that emits the reverse affine frame stream.  Counter one
stores the current value, counter two temporarily saves it while it is
printed, and work stack one persistently stores the runtime stride. -/
def affineUnaryProgressionRevProgram : Program UnaryFrameSym UnaryFrameSym where
  Label := AffineUnaryProgressionLabel
  main := .loadBase
  op
    | .loadBase => .popInput .invalid fun
        | .tick => .incBase
        | .separator => .loadStep
        | .frameEnd => .invalid
    | .incBase => .inc₁ .loadBase
    | .loadStep => .popInput .invalid fun
        | .tick => .saveStep
        | .separator => .next
        | .frameEnd => .invalid
    | .saveStep => .pushWork₁ .tick .loadStep
    | .next => .popInput .invalid fun
        | .tick => .emitCurrent
        | .separator => .clearCurrent
        | .frameEnd => .invalid
    | .emitCurrent => .dec₁ .pushSeparator .saveCurrent
    | .saveCurrent => .inc₂ .pushTick
    | .pushTick => .pushOutput .tick .emitCurrent
    | .pushSeparator => .pushOutput .separator .restoreCurrent
    | .restoreCurrent => .dec₂ .advance .restoreCurrentInc
    | .restoreCurrentInc => .inc₁ .restoreCurrent
    | .advance => .moveWork₁Work₂ .restoreStep fun
        | .tick => .advanceInc
        | _ => .invalid
    | .advanceInc => .inc₁ .advance
    | .restoreStep => .moveWork₂Work₁ .next fun
        | .tick => .restoreStep
        | _ => .invalid
    | .clearCurrent => .dec₁ .clearStep .clearCurrent
    | .clearStep => .popWork₁ .halt fun _ => .clearStep
    | .halt => .halt
    | .invalid => .halt

private def affineUnaryProgressionCfg
    (label : AffineUnaryProgressionLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    BuilderCfg affineUnaryProgressionRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := current
  counter₂ := saved
  counter₃ := []

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem loadBase_eval (base : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * base + 1]
      (some (affineUnaryProgressionCfg .loadBase buffer₁ buffer₂ test
        (encodeUnaryFrameBlock base ++ tail) output work₁ work₂
        current saved)) =
      some (affineUnaryProgressionCfg .loadStep (some .separator) buffer₂ test
        tail output work₁ work₂
        (List.replicate base () ++ current) saved) := by
  induction base generalizing buffer₁ current with
  | zero => rfl
  | succ base ih =>
      rw [show 2 * (base + 1) + 1 = (2 * base + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * base + 1]
          (some (affineUnaryProgressionCfg .loadBase (some .tick) buffer₂ test
            (encodeUnaryFrameBlock base ++ tail) output work₁ work₂
            (() :: current) saved)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem loadStep_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * stride + 1]
      (some (affineUnaryProgressionCfg .loadStep buffer₁ buffer₂ test
        (encodeUnaryFrameBlock stride ++ tail) output work₁ work₂
        current saved)) =
      some (affineUnaryProgressionCfg .next (some .separator) buffer₂ test
        tail output (List.replicate stride .tick ++ work₁) work₂
        current saved) := by
  induction stride generalizing buffer₁ work₁ with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 1 = (2 * stride + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * stride + 1]
          (some (affineUnaryProgressionCfg .loadStep (some .tick) buffer₂ test
            (encodeUnaryFrameBlock stride ++ tail) output (.tick :: work₁) work₂
            current saved)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₁)

private theorem emitCurrent_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (saved : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[3 * value + 1]
      (some (affineUnaryProgressionCfg .emitCurrent buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate value ()) saved)) =
      some (affineUnaryProgressionCfg .pushSeparator buffer₁ buffer₂ false
        input (List.replicate value .tick ++ output) work₁ work₂ []
        (List.replicate value () ++ saved)) := by
  induction value generalizing test output saved with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[3 * value + 1]
          (some (affineUnaryProgressionCfg .emitCurrent buffer₁ buffer₂ true
            input (.tick :: output) work₁ work₂ (List.replicate value ())
            (() :: saved))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (() :: saved)

private theorem restoreCurrent_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * value + 1]
      (some (affineUnaryProgressionCfg .restoreCurrent buffer₁ buffer₂ test
        input output work₁ work₂ current (List.replicate value ()))) =
      some (affineUnaryProgressionCfg .advance buffer₁ buffer₂ false
        input output work₁ work₂
        (List.replicate value () ++ current) []) := by
  induction value generalizing test current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * value + 1]
          (some (affineUnaryProgressionCfg .restoreCurrent buffer₁ buffer₂ true
            input output work₁ work₂ (() :: current)
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (() :: current)

private theorem advance_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym) (current saved : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * stride + 1]
      (some (affineUnaryProgressionCfg .advance buffer₁ buffer₂ test
        input output (List.replicate stride .tick) work₂ current saved)) =
      some (affineUnaryProgressionCfg .restoreStep none buffer₂ test
        input output [] (List.replicate stride .tick ++ work₂)
        (List.replicate stride () ++ current) saved) := by
  induction stride generalizing buffer₁ work₂ current with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 1 = (2 * stride + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[2 * stride + 1]
          (some (affineUnaryProgressionCfg .advance (some .tick) buffer₂ test
            input output (List.replicate stride .tick) (.tick :: work₂)
            (() :: current) saved)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₂) (() :: current)

private theorem restoreStep_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym) (current saved : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[stride + 1]
      (some (affineUnaryProgressionCfg .restoreStep buffer₁ buffer₂ test
        input output work₁ (List.replicate stride .tick) current saved)) =
      some (affineUnaryProgressionCfg .next buffer₁ none test
        input output (List.replicate stride .tick ++ work₁) [] current saved) := by
  induction stride generalizing buffer₂ work₁ with
  | zero => rfl
  | succ stride ih =>
      rw [show stride + 1 + 1 = (stride + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[stride + 1]
          (some (affineUnaryProgressionCfg .restoreStep buffer₁ (some .tick) test
            input output (.tick :: work₁) (List.replicate stride .tick)
            current saved)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₁)

private def affineUnaryProgressionPhaseSteps : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | current, stride, count + 1 =>
      5 * current + 3 * stride + 6 +
        affineUnaryProgressionPhaseSteps (current + stride) stride count

private def affineUnaryProgressionStreamFrom : Nat → Nat → Nat →
    List UnaryFrameSym
  | _, _, 0 => []
  | current, stride, count + 1 =>
      encodeUnaryFrameBlock current ++
        affineUnaryProgressionStreamFrom (current + stride) stride count

private def affineUnaryProgression_onePhase (current stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (rest output : List UnaryFrameSym) :
    EvalsToInTime (step affineUnaryProgressionRevProgram)
      (affineUnaryProgressionCfg .next buffer₁ buffer₂ test
        (.tick :: rest) output (List.replicate stride .tick) []
        (List.replicate current ()) [])
      (some (affineUnaryProgressionCfg .next none none false
        rest ((encodeUnaryFrameBlock current).reverse ++ output)
        (List.replicate stride .tick) []
        (List.replicate (current + stride) ()) []))
      (5 * current + 3 * stride + 6) := by
  let afterPop := affineUnaryProgressionCfg .emitCurrent (some .tick) buffer₂ test
    rest output (List.replicate stride .tick) []
    (List.replicate current ()) []
  let afterEmit := affineUnaryProgressionCfg .pushSeparator (some .tick) buffer₂
    false rest (List.replicate current .tick ++ output)
    (List.replicate stride .tick) [] [] (List.replicate current ())
  let afterSeparator := affineUnaryProgressionCfg .restoreCurrent
    (some .tick) buffer₂ false rest
    ((encodeUnaryFrameBlock current).reverse ++ output)
    (List.replicate stride .tick) [] [] (List.replicate current ())
  let afterRestore := affineUnaryProgressionCfg .advance
    (some .tick) buffer₂ false rest
    ((encodeUnaryFrameBlock current).reverse ++ output)
    (List.replicate stride .tick) [] (List.replicate current ()) []
  let afterAdvance := affineUnaryProgressionCfg .restoreStep none buffer₂ false
    rest ((encodeUnaryFrameBlock current).reverse ++ output) []
    (List.replicate stride .tick) (List.replicate (current + stride) ()) []
  have hpop : EvalsToInTime (step affineUnaryProgressionRevProgram)
      (affineUnaryProgressionCfg .next buffer₁ buffer₂ test
        (.tick :: rest) output (List.replicate stride .tick) []
        (List.replicate current ()) []) (some afterPop) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hemit : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterPop (some afterEmit) (3 * current + 1) := by
    exact ⟨⟨3 * current + 1, by
      simpa [afterPop, afterEmit] using
        emitCurrent_eval current (some .tick) buffer₂ test rest output
          (List.replicate stride .tick) [] []⟩, le_rfl⟩
  have hout :
      .separator :: (List.replicate current .tick ++ output) =
        (encodeUnaryFrameBlock current).reverse ++ output := by
    simp [encodeUnaryFrameBlock, List.reverse_append]
  have hseparator : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterEmit (some afterSeparator) 1 := by
    have hraw :
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[1]
          (some afterEmit) =
          some (affineUnaryProgressionCfg .restoreCurrent
            (some .tick) buffer₂ false rest
            (.separator :: (List.replicate current .tick ++ output))
            (List.replicate stride .tick) [] []
            (List.replicate current ())) := rfl
    rw [hout] at hraw
    exact ⟨⟨1, by
      change (flip Option.bind
        (step affineUnaryProgressionRevProgram))^[1]
          (some afterEmit) = some afterSeparator
      exact hraw⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterSeparator (some afterRestore) (2 * current + 1) := by
    exact ⟨⟨2 * current + 1, by
      simpa [afterSeparator, afterRestore] using
        restoreCurrent_eval current (some .tick) buffer₂ false rest
          ((encodeUnaryFrameBlock current).reverse ++ output)
          (List.replicate stride .tick) [] []⟩, le_rfl⟩
  have hcurrent :
      List.replicate stride () ++ List.replicate current () =
        List.replicate (current + stride) () := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hadvance : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterRestore (some afterAdvance) (2 * stride + 1) := by
    have hraw := advance_eval stride (some .tick) buffer₂ false rest
      ((encodeUnaryFrameBlock current).reverse ++ output) []
      (List.replicate current ()) []
    rw [hcurrent, List.append_nil] at hraw
    exact ⟨⟨2 * stride + 1, by
      change (flip Option.bind
        (step affineUnaryProgressionRevProgram))^[2 * stride + 1]
          (some afterRestore) = some afterAdvance
      exact hraw⟩, le_rfl⟩
  have hrestoreStep : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterAdvance
      (some (affineUnaryProgressionCfg .next none none false rest
        ((encodeUnaryFrameBlock current).reverse ++ output)
        (List.replicate stride .tick) []
        (List.replicate (current + stride) ()) []))
      (stride + 1) := by
    have hraw := restoreStep_eval stride none buffer₂ false rest
      ((encodeUnaryFrameBlock current).reverse ++ output) []
      (List.replicate (current + stride) ()) []
    rw [List.append_nil] at hraw
    exact ⟨⟨stride + 1, by
      change (flip Option.bind
        (step affineUnaryProgressionRevProgram))^[stride + 1]
          (some afterAdvance) = _
      exact hraw⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    1 (3 * current + 1) _ afterPop _ hpop hemit
  let h₂ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    ((3 * current + 1) + 1) 1 _ afterEmit _ h₁ hseparator
  let h₃ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    (1 + ((3 * current + 1) + 1)) (2 * current + 1)
    _ afterSeparator _ h₂ hrestore
  let h₄ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    ((2 * current + 1) + (1 + ((3 * current + 1) + 1)))
    (2 * stride + 1) _ afterRestore _ h₃ hadvance
  let full := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    ((2 * stride + 1) +
      ((2 * current + 1) + (1 + ((3 * current + 1) + 1))))
    (stride + 1) _ afterAdvance _ h₄ hrestoreStep
  have hbound :
      stride + 1 +
          ((2 * stride + 1) +
            ((2 * current + 1) + (1 + ((3 * current + 1) + 1)))) =
        5 * current + 3 * stride + 6 := by omega
  rw [← hbound]
  exact full

private def affineUnaryProgression_inputPhases (current stride : Nat)
    (buffer₁ : Option UnaryFrameSym)
    (count : Nat) (tail output : List UnaryFrameSym) :
    Σ finalBuffer,
      EvalsToInTime (step affineUnaryProgressionRevProgram)
        (affineUnaryProgressionCfg .next buffer₁ none false
          (List.replicate count .tick ++ tail) output
          (List.replicate stride .tick) [] (List.replicate current ()) [])
        (some (affineUnaryProgressionCfg .next finalBuffer none false tail
          ((affineUnaryProgressionStreamFrom current stride count).reverse ++
            output)
          (List.replicate stride .tick) []
          (List.replicate (current + count * stride) ()) []))
        (affineUnaryProgressionPhaseSteps current stride count) := by
  induction count generalizing current buffer₁ output with
  | zero =>
      exact ⟨buffer₁, ⟨⟨0, by
        simp [affineUnaryProgressionStreamFrom]⟩, le_rfl⟩⟩
  | succ count ih =>
      let first := affineUnaryProgression_onePhase current stride buffer₁
        none false (List.replicate count .tick ++ tail) output
      rcases ih (current + stride) none
          ((encodeUnaryFrameBlock current).reverse ++ output) with
        ⟨finalBuffer, remaining⟩
      let full := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
        (5 * current + 3 * stride + 6)
        (affineUnaryProgressionPhaseSteps (current + stride) stride count)
        _
        (affineUnaryProgressionCfg .next none none false
          (List.replicate count .tick ++ tail)
          ((encodeUnaryFrameBlock current).reverse ++ output)
          (List.replicate stride .tick) []
          (List.replicate (current + stride) ()) [])
        _ first remaining
      have hcurrent : current + stride + count * stride =
          current + (count + 1) * stride := by
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hout :
          (affineUnaryProgressionStreamFrom
              (current + stride) stride count).reverse ++
              ((encodeUnaryFrameBlock current).reverse ++ output) =
            (affineUnaryProgressionStreamFrom
              current stride (count + 1)).reverse ++ output := by
        simp [affineUnaryProgressionStreamFrom, List.reverse_append,
          List.append_assoc]
      rw [hcurrent, hout] at full
      refine ⟨finalBuffer, ?_⟩
      simpa [List.replicate_succ, affineUnaryProgressionPhaseSteps,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using full

private theorem affineUnaryProgressionStreamFrom_eq
    (base stride count : Nat) :
    affineUnaryProgressionStreamFrom base stride count =
      encodeUnaryFrame
        (affineUnaryProgressionValuesFrom base stride count) := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      simp [affineUnaryProgressionStreamFrom,
        affineUnaryProgressionValuesFrom, encodeUnaryFrame, ih]

private def affineUnaryProgressionRevSteps
    (progression : AffineUnaryProgression) : Nat :=
  2 * progression.base + 1 +
    (2 * progression.step + 1) +
    affineUnaryProgressionPhaseSteps
      progression.base progression.step progression.count +
    (progression.base + progression.count * progression.step) +
    progression.step + 4

private theorem clearCurrent_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (saved : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[value + 1]
      (some (affineUnaryProgressionCfg .clearCurrent buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate value ()) saved)) =
      some (affineUnaryProgressionCfg .clearStep buffer₁ buffer₂ false
        input output work₁ work₂ [] saved) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[value + 1]
          (some (affineUnaryProgressionCfg .clearCurrent buffer₁ buffer₂ true
            input output work₁ work₂ (List.replicate value ()) saved)) = _
      simpa using ih true

private theorem clearStep_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym) (current saved : List Unit) :
    (flip Option.bind (step affineUnaryProgressionRevProgram))^[stride + 1]
      (some (affineUnaryProgressionCfg .clearStep buffer₁ buffer₂ test
        input output (List.replicate stride .tick) work₂ current saved)) =
      some (affineUnaryProgressionCfg .halt none buffer₂ test
        input output [] work₂ current saved) := by
  induction stride generalizing buffer₁ with
  | zero => rfl
  | succ stride ih =>
      rw [show stride + 1 + 1 = (stride + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineUnaryProgressionRevProgram))^[stride + 1]
          (some (affineUnaryProgressionCfg .clearStep (some .tick) buffer₂ test
            input output (List.replicate stride .tick) work₂ current saved)) = _
      simpa using ih (some .tick)

/-- Exact successful run on every canonical structured progression input. -/
def affineUnaryProgressionRev_run (progression : AffineUnaryProgression) :
    EvalsToInTime (step affineUnaryProgressionRevProgram)
      (initialCfg affineUnaryProgressionRevProgram
        (encodeAffineUnaryProgression progression))
      (some (haltCfg affineUnaryProgressionRevProgram
        (affineUnaryProgressionFrameStream progression).reverse))
      (affineUnaryProgressionRevSteps progression) := by
  let countFrame := encodeUnaryFrameBlock progression.count
  let afterBase := affineUnaryProgressionCfg .loadStep (some .separator) none false
    (encodeUnaryFrameBlock progression.step ++ countFrame) [] [] []
    (List.replicate progression.base ()) []
  let afterStep := affineUnaryProgressionCfg .next (some .separator) none false
    countFrame [] (List.replicate progression.step .tick) []
    (List.replicate progression.base ()) []
  have hbase : EvalsToInTime (step affineUnaryProgressionRevProgram)
      (initialCfg affineUnaryProgressionRevProgram
        (encodeAffineUnaryProgression progression))
      (some afterBase) (2 * progression.base + 1) := by
    exact ⟨⟨2 * progression.base + 1, by
      simpa [encodeAffineUnaryProgression, encodeUnaryFrame, afterBase,
        initialCfg, affineUnaryProgressionCfg,
        affineUnaryProgressionRevProgram] using
        loadBase_eval progression.base none none false
          (encodeUnaryFrameBlock progression.step ++ countFrame) [] [] [] [] []⟩,
      le_rfl⟩
  have hstep : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterBase (some afterStep) (2 * progression.step + 1) := by
    exact ⟨⟨2 * progression.step + 1, by
      simpa [afterBase, afterStep] using
        loadStep_eval progression.step (some .separator) none false
          countFrame [] [] [] (List.replicate progression.base ()) []⟩,
      le_rfl⟩
  rcases affineUnaryProgression_inputPhases progression.base progression.step
      (some .separator) progression.count [.separator] [] with
    ⟨finalBuffer, phases⟩
  have hphases : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterStep
      (some (affineUnaryProgressionCfg .next finalBuffer none false
        [.separator]
        ((affineUnaryProgressionFrameStream progression).reverse)
        (List.replicate progression.step .tick) []
        (List.replicate
          (progression.base + progression.count * progression.step) ()) []))
      (affineUnaryProgressionPhaseSteps progression.base progression.step
        progression.count) := by
    simpa [afterStep, countFrame, encodeUnaryFrameBlock,
      affineUnaryProgressionFrameStream, affineUnaryProgressionValues,
      affineUnaryProgressionStreamFrom_eq] using phases
  let current := progression.base + progression.count * progression.step
  let output := (affineUnaryProgressionFrameStream progression).reverse
  let afterCount := affineUnaryProgressionCfg .clearCurrent (some .separator)
    none false [] output (List.replicate progression.step .tick) []
    (List.replicate current ()) []
  let afterCurrent := affineUnaryProgressionCfg .clearStep (some .separator)
    none false [] output (List.replicate progression.step .tick) [] [] []
  let beforeHalt := affineUnaryProgressionCfg .halt none none false [] output
    [] [] [] []
  have hcount : EvalsToInTime (step affineUnaryProgressionRevProgram)
      (affineUnaryProgressionCfg .next finalBuffer none false [.separator]
        output (List.replicate progression.step .tick) []
        (List.replicate current ()) [])
      (some afterCount) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hcurrent : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterCount (some afterCurrent) (current + 1) := by
    exact ⟨⟨current + 1, by
      simpa [afterCount, afterCurrent] using
        clearCurrent_eval current (some .separator) none false [] output
          (List.replicate progression.step .tick) [] []⟩, le_rfl⟩
  have hclearStep : EvalsToInTime (step affineUnaryProgressionRevProgram)
      afterCurrent (some beforeHalt) (progression.step + 1) := by
    exact ⟨⟨progression.step + 1, by
      simpa [afterCurrent, beforeHalt] using
        clearStep_eval progression.step (some .separator) none false [] output
          [] [] []⟩, le_rfl⟩
  have hhalt : EvalsToInTime (step affineUnaryProgressionRevProgram)
      beforeHalt
      (some (haltCfg affineUnaryProgressionRevProgram output)) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    (2 * progression.base + 1) (2 * progression.step + 1)
    _ afterBase _ hbase hstep
  let h₂ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    ((2 * progression.step + 1) + (2 * progression.base + 1))
    (affineUnaryProgressionPhaseSteps progression.base progression.step
      progression.count) _ afterStep _ h₁ hphases
  let h₃ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    (affineUnaryProgressionPhaseSteps progression.base progression.step
        progression.count +
      ((2 * progression.step + 1) + (2 * progression.base + 1)))
    1 _ _ _ h₂ hcount
  let h₄ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    (1 + (affineUnaryProgressionPhaseSteps progression.base progression.step
        progression.count +
      ((2 * progression.step + 1) + (2 * progression.base + 1))))
    (current + 1) _ afterCount _ h₃ hcurrent
  let h₅ := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    ((current + 1) +
      (1 + (affineUnaryProgressionPhaseSteps progression.base progression.step
        progression.count +
      ((2 * progression.step + 1) + (2 * progression.base + 1)))))
    (progression.step + 1) _ afterCurrent _ h₄ hclearStep
  let full := EvalsToInTime.trans (step affineUnaryProgressionRevProgram)
    ((progression.step + 1) + ((current + 1) +
      (1 + (affineUnaryProgressionPhaseSteps progression.base progression.step
        progression.count +
      ((2 * progression.step + 1) + (2 * progression.base + 1))))))
    1 _ beforeHalt _ h₅ hhalt
  have hbound :
      1 + ((progression.step + 1) + ((current + 1) +
        (1 + (affineUnaryProgressionPhaseSteps progression.base progression.step
          progression.count +
        ((2 * progression.step + 1) + (2 * progression.base + 1)))))) =
      affineUnaryProgressionRevSteps progression := by
    simp only [affineUnaryProgressionRevSteps, current]
    omega
  rw [← hbound]
  exact full

private theorem affineUnaryProgressionPhaseSteps_le
    (current stride count : Nat) :
    affineUnaryProgressionPhaseSteps current stride count ≤
      count * (5 * (current + count * stride) + 3 * stride + 6) := by
  induction count generalizing current with
  | zero => simp [affineUnaryProgressionPhaseSteps]
  | succ count ih =>
      simp only [affineUnaryProgressionPhaseSteps]
      have h := ih (current + stride)
      nlinarith

private theorem encodeAffineUnaryProgression_length
    (progression : AffineUnaryProgression) :
    (encodeAffineUnaryProgression progression).length =
      progression.base + progression.step + progression.count + 3 := by
  simp [encodeAffineUnaryProgression]
  omega

private theorem affineUnaryProgressionRev_steps_le
    (progression : AffineUnaryProgression) :
    affineUnaryProgressionRevSteps progression ≤
      30 * (encodeAffineUnaryProgression progression).length ^ 3 + 30 := by
  have hphase := affineUnaryProgressionPhaseSteps_le
    progression.base progression.step progression.count
  let n := progression.base + progression.step + progression.count + 3
  have hn : 1 ≤ n := by omega
  have hbase : progression.base ≤ n := by omega
  have hstep : progression.step ≤ n := by omega
  have hcount : progression.count ≤ n := by omega
  have hproduct : progression.count * progression.step ≤ n ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hcount hstep
  have hn_square : n ≤ n ^ 2 := by nlinarith
  have hcurrent :
      progression.base + progression.count * progression.step ≤ 2 * n ^ 2 := by
    omega
  have hphaseFactor :
      5 * (progression.base + progression.count * progression.step) +
          3 * progression.step + 6 ≤
        20 * n ^ 2 := by
    nlinarith
  have hphase' :
      affineUnaryProgressionPhaseSteps
          progression.base progression.step progression.count ≤
        20 * n ^ 3 := by
    calc
      _ ≤ progression.count *
          (5 * (progression.base + progression.count * progression.step) +
            3 * progression.step + 6) := hphase
      _ ≤ n * (20 * n ^ 2) := Nat.mul_le_mul hcount hphaseFactor
      _ = 20 * n ^ 3 := by ring
  have hn_square_cube : n ^ 2 ≤ n ^ 3 := by nlinarith
  rw [encodeAffineUnaryProgression_length]
  change affineUnaryProgressionRevSteps progression ≤ 30 * n ^ 3 + 30
  simp only [affineUnaryProgressionRevSteps]
  omega

/-- Concrete polynomial-time machine for the reversed affine frame stream. -/
noncomputable def affineUnaryProgressionRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryProgression id
      (fun progression =>
        (affineUnaryProgressionFrameStream progression).reverse) where
  tm := compile affineUnaryProgressionRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 30 * Polynomial.X ^ 3 + 30
  outputsFun := fun progression => by
    have builderRun := affineUnaryProgressionRev_run progression
    have compiledRun := compile_evalsToInTime
      affineUnaryProgressionRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineUnaryProgressionRevProgram).step
        (_root_.Turing.initList (compile affineUnaryProgressionRevProgram)
          (encodeAffineUnaryProgression progression))
        (some (_root_.Turing.haltList
          (compile affineUnaryProgressionRevProgram)
          (affineUnaryProgressionFrameStream progression).reverse))
        (affineUnaryProgressionRevSteps progression) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineUnaryProgressionRevSteps progression ≤
        (30 * Polynomial.X ^ 3 + 30).eval
          (encodeAffineUnaryProgression progression).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineUnaryProgressionRev_steps_le progression
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineUnaryProgressionRevProgram).step
        (_root_.Turing.initList (compile affineUnaryProgressionRevProgram)
          (encodeAffineUnaryProgression progression))
        (some (_root_.Turing.haltList
          (compile affineUnaryProgressionRevProgram)
          (affineUnaryProgressionFrameStream progression).reverse))
        ((30 * Polynomial.X ^ 3 + 30).eval
          (encodeAffineUnaryProgression progression).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the concrete prepend-based run gives the forward affine unary
frame family. -/
noncomputable def affineUnaryProgressionFrameStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryProgression id affineUnaryProgressionFrameStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineUnaryProgressionRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
