import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Runtime affine unary triple progressions

Several Cook--Levin operands advance together from one tableau row to the
next.  This module verifies a fixed counter machine for three simultaneous
affine progressions.  The machine consumes unary bases, unary strides, and a
shared unary row count, then emits the three current values in row-major
delimiter-bearing frames.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

set_option maxRecDepth 2048

/-- Runtime parameters for three affine values sharing one row count. -/
structure AffineUnaryTripleProgression where
  base₁ : Nat
  base₂ : Nat
  base₃ : Nat
  step₁ : Nat
  step₂ : Nat
  step₃ : Nat
  count : Nat
deriving DecidableEq, Repr

/-- Canonical seven-field input of the triple progression controller. -/
def encodeAffineUnaryTripleProgression
    (progression : AffineUnaryTripleProgression) : List UnaryFrameSym :=
  encodeUnaryFrame
    [progression.base₁, progression.base₂, progression.base₃,
      progression.step₁, progression.step₂, progression.step₃,
      progression.count]

/-- Three affine rows starting from arbitrary current values. -/
def affineUnaryTripleProgressionRowsFrom :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → List (Nat × Nat × Nat)
  | _, _, _, _, _, _, 0 => []
  | current₁, current₂, current₃, stride₁, stride₂, stride₃, count + 1 =>
      (current₁, current₂, current₃) ::
        affineUnaryTripleProgressionRowsFrom
          (current₁ + stride₁) (current₂ + stride₂) (current₃ + stride₃)
          stride₁ stride₂ stride₃ count

/-- Natural row triples produced by the structured progression. -/
def affineUnaryTripleProgressionRows
    (progression : AffineUnaryTripleProgression) :
    List (Nat × Nat × Nat) :=
  affineUnaryTripleProgressionRowsFrom
    progression.base₁ progression.base₂ progression.base₃
    progression.step₁ progression.step₂ progression.step₃ progression.count

/-- Closed positional form of the three recursive affine values. -/
theorem affineUnaryTripleProgressionRowsFrom_eq_ofFn
    (base₁ base₂ base₃ stride₁ stride₂ stride₃ count : Nat) :
    affineUnaryTripleProgressionRowsFrom
        base₁ base₂ base₃ stride₁ stride₂ stride₃ count =
      List.ofFn fun index : Fin count =>
        (base₁ + index.val * stride₁,
          base₂ + index.val * stride₂,
          base₃ + index.val * stride₃) := by
  induction count generalizing base₁ base₂ base₃ with
  | zero => rfl
  | succ count ih =>
      rw [affineUnaryTripleProgressionRowsFrom, List.ofFn_succ]
      congr 1
      · simp
      · rw [ih]
        apply List.ofFn_inj.mpr
        funext index
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Positional form specialized to a structured progression. -/
theorem affineUnaryTripleProgressionRows_eq_ofFn
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionRows progression =
      List.ofFn fun index : Fin progression.count =>
        (progression.base₁ + index.val * progression.step₁,
          progression.base₂ + index.val * progression.step₂,
          progression.base₃ + index.val * progression.step₃) := by
  exact affineUnaryTripleProgressionRowsFrom_eq_ofFn _ _ _ _ _ _ _

/-- Flatten one row triple into its three unary values. -/
def affineUnaryTripleRowValues
    (row : Nat × Nat × Nat) : List Nat :=
  [row.1, row.2.1, row.2.2]

/-- Exact delimiter-bearing forward output. -/
def affineUnaryTripleProgressionFrameStream
    (progression : AffineUnaryTripleProgression) : List UnaryFrameSym :=
  (affineUnaryTripleProgressionRows progression).flatMap fun row =>
    encodeUnaryFrame (affineUnaryTripleRowValues row)

/-- Finite control for the reversed triple progression streamer. -/
inductive AffineUnaryTripleProgressionLabel
  | loadBase₁ | incBase₁
  | loadBase₂ | incBase₂
  | loadBase₃ | incBase₃
  | loadStep₁ | saveStep₁ | separateStep₁
  | loadStep₂ | saveStep₂ | separateStep₂
  | loadStep₃ | saveStep₃
  | next
  | emit₁ | save₁ | pushTick₁ | pushSeparator₁ | restore₁ | restoreInc₁
  | emit₂ | save₂ | pushTick₂ | pushSeparator₂ | restore₂ | restoreInc₂
  | emit₃ | save₃ | pushTick₃ | pushSeparator₃ | restore₃ | restoreInc₃
  | advance₃ | advanceInc₃
  | advance₂ | advanceInc₂
  | advance₁ | advanceInc₁
  | restoreSteps
  | clear₁ | clear₂ | clear₃ | clearSteps
  | halt | invalid
deriving DecidableEq, Fintype

/-- A fixed program emitting the reverse row-major triple stream.  The three
counters store the current values.  Work stack one stores the three strides,
and work stack two is reused first as emission scratch and then while the
stride block is rotated and restored. -/
def affineUnaryTripleProgressionRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineUnaryTripleProgressionLabel
  main := .loadBase₁
  op
    | .loadBase₁ => .popInput .invalid fun
        | .tick => .incBase₁
        | .separator => .loadBase₂
        | .frameEnd => .invalid
    | .incBase₁ => .inc₁ .loadBase₁
    | .loadBase₂ => .popInput .invalid fun
        | .tick => .incBase₂
        | .separator => .loadBase₃
        | .frameEnd => .invalid
    | .incBase₂ => .inc₂ .loadBase₂
    | .loadBase₃ => .popInput .invalid fun
        | .tick => .incBase₃
        | .separator => .loadStep₁
        | .frameEnd => .invalid
    | .incBase₃ => .inc₃ .loadBase₃
    | .loadStep₁ => .popInput .invalid fun
        | .tick => .saveStep₁
        | .separator => .separateStep₁
        | .frameEnd => .invalid
    | .saveStep₁ => .pushWork₁ .tick .loadStep₁
    | .separateStep₁ => .pushWork₁ .separator .loadStep₂
    | .loadStep₂ => .popInput .invalid fun
        | .tick => .saveStep₂
        | .separator => .separateStep₂
        | .frameEnd => .invalid
    | .saveStep₂ => .pushWork₁ .tick .loadStep₂
    | .separateStep₂ => .pushWork₁ .separator .loadStep₃
    | .loadStep₃ => .popInput .invalid fun
        | .tick => .saveStep₃
        | .separator => .next
        | .frameEnd => .invalid
    | .saveStep₃ => .pushWork₁ .tick .loadStep₃
    | .next => .popInput .invalid fun
        | .tick => .emit₁
        | .separator => .clear₁
        | .frameEnd => .invalid
    | .emit₁ => .dec₁ .pushSeparator₁ .save₁
    | .save₁ => .pushWork₂ .tick .pushTick₁
    | .pushTick₁ => .pushOutput .tick .emit₁
    | .pushSeparator₁ => .pushOutput .separator .restore₁
    | .restore₁ => .popWork₂ .emit₂ fun
        | .tick => .restoreInc₁
        | _ => .invalid
    | .restoreInc₁ => .inc₁ .restore₁
    | .emit₂ => .dec₂ .pushSeparator₂ .save₂
    | .save₂ => .pushWork₂ .tick .pushTick₂
    | .pushTick₂ => .pushOutput .tick .emit₂
    | .pushSeparator₂ => .pushOutput .separator .restore₂
    | .restore₂ => .popWork₂ .emit₃ fun
        | .tick => .restoreInc₂
        | _ => .invalid
    | .restoreInc₂ => .inc₂ .restore₂
    | .emit₃ => .dec₃ .pushSeparator₃ .save₃
    | .save₃ => .pushWork₂ .tick .pushTick₃
    | .pushTick₃ => .pushOutput .tick .emit₃
    | .pushSeparator₃ => .pushOutput .separator .restore₃
    | .restore₃ => .popWork₂ .advance₃ fun
        | .tick => .restoreInc₃
        | _ => .invalid
    | .restoreInc₃ => .inc₃ .restore₃
    | .advance₃ => .moveWork₁Work₂ .restoreSteps fun
        | .tick => .advanceInc₃
        | .separator => .advance₂
        | .frameEnd => .invalid
    | .advanceInc₃ => .inc₃ .advance₃
    | .advance₂ => .moveWork₁Work₂ .invalid fun
        | .tick => .advanceInc₂
        | .separator => .advance₁
        | .frameEnd => .invalid
    | .advanceInc₂ => .inc₂ .advance₂
    | .advance₁ => .moveWork₁Work₂ .restoreSteps fun
        | .tick => .advanceInc₁
        | _ => .invalid
    | .advanceInc₁ => .inc₁ .advance₁
    | .restoreSteps => .moveWork₂Work₁ .next fun
        | .tick => .restoreSteps
        | .separator => .restoreSteps
        | .frameEnd => .invalid
    | .clear₁ => .dec₁ .clear₂ .clear₁
    | .clear₂ => .dec₂ .clear₃ .clear₂
    | .clear₃ => .dec₃ .clearSteps .clear₃
    | .clearSteps => .popWork₁ .halt fun _ => .clearSteps
    | .halt => .halt
    | .invalid => .halt

private def affineUnaryTripleProgressionCfg
    (label : AffineUnaryTripleProgressionLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    BuilderCfg affineUnaryTripleProgressionRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := current₁
  counter₂ := current₂
  counter₃ := current₃

/-- Clean contextual entry used by continuous family wrappers. -/
def affineUnaryTripleProgressionLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineUnaryTripleProgressionRevProgram :=
  affineUnaryTripleProgressionCfg .loadBase₁ none none false
    input output [] [] [] [] []

/-- Redirectable clean exit after one progression has consumed exactly its
seven unary fields.  The input tail and existing output suffix are preserved. -/
def affineUnaryTripleProgressionFinishCfg
    (tail output : List UnaryFrameSym) :
    BuilderCfg affineUnaryTripleProgressionRevProgram :=
  affineUnaryTripleProgressionCfg .halt none none false
    tail output [] [] [] [] []

private theorem triple_replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem loadBase₁_eval (base : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * base + 1]
      (some (affineUnaryTripleProgressionCfg .loadBase₁ buffer₁ buffer₂ test
        (encodeUnaryFrameBlock base ++ tail) output work₁ work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .loadBase₂ (some .separator)
        buffer₂ test tail output work₁ work₂
        (List.replicate base () ++ current₁) current₂ current₃) := by
  induction base generalizing buffer₁ current₁ with
  | zero => rfl
  | succ base ih =>
      rw [show 2 * (base + 1) + 1 = (2 * base + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * base + 1]
          (some (affineUnaryTripleProgressionCfg .loadBase₁ (some .tick)
            buffer₂ test (encodeUnaryFrameBlock base ++ tail) output work₁
            work₂ (() :: current₁) current₂ current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current₁)

private theorem loadBase₂_eval (base : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * base + 1]
      (some (affineUnaryTripleProgressionCfg .loadBase₂ buffer₁ buffer₂ test
        (encodeUnaryFrameBlock base ++ tail) output work₁ work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .loadBase₃ (some .separator)
        buffer₂ test tail output work₁ work₂ current₁
        (List.replicate base () ++ current₂) current₃) := by
  induction base generalizing buffer₁ current₂ with
  | zero => rfl
  | succ base ih =>
      rw [show 2 * (base + 1) + 1 = (2 * base + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * base + 1]
          (some (affineUnaryTripleProgressionCfg .loadBase₂ (some .tick)
            buffer₂ test (encodeUnaryFrameBlock base ++ tail) output work₁
            work₂ current₁ (() :: current₂) current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current₂)

private theorem loadBase₃_eval (base : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * base + 1]
      (some (affineUnaryTripleProgressionCfg .loadBase₃ buffer₁ buffer₂ test
        (encodeUnaryFrameBlock base ++ tail) output work₁ work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .loadStep₁ (some .separator)
        buffer₂ test tail output work₁ work₂ current₁ current₂
        (List.replicate base () ++ current₃)) := by
  induction base generalizing buffer₁ current₃ with
  | zero => rfl
  | succ base ih =>
      rw [show 2 * (base + 1) + 1 = (2 * base + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * base + 1]
          (some (affineUnaryTripleProgressionCfg .loadBase₃ (some .tick)
            buffer₂ test (encodeUnaryFrameBlock base ++ tail) output work₁
            work₂ current₁ current₂ (() :: current₃))) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current₃)

private theorem loadStep₁_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 2]
      (some (affineUnaryTripleProgressionCfg .loadStep₁ buffer₁ buffer₂ test
        (encodeUnaryFrameBlock stride ++ tail) output work₁ work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .loadStep₂ (some .separator)
        buffer₂ test tail output
        (.separator :: (List.replicate stride .tick ++ work₁)) work₂
        current₁ current₂ current₃) := by
  induction stride generalizing buffer₁ work₁ with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 2 = (2 * stride + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 2]
          (some (affineUnaryTripleProgressionCfg .loadStep₁ (some .tick)
            buffer₂ test (encodeUnaryFrameBlock stride ++ tail) output
            (.tick :: work₁) work₂ current₁ current₂ current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₁)

private theorem loadStep₂_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 2]
      (some (affineUnaryTripleProgressionCfg .loadStep₂ buffer₁ buffer₂ test
        (encodeUnaryFrameBlock stride ++ tail) output work₁ work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .loadStep₃ (some .separator)
        buffer₂ test tail output
        (.separator :: (List.replicate stride .tick ++ work₁)) work₂
        current₁ current₂ current₃) := by
  induction stride generalizing buffer₁ work₁ with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 2 = (2 * stride + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 2]
          (some (affineUnaryTripleProgressionCfg .loadStep₂ (some .tick)
            buffer₂ test (encodeUnaryFrameBlock stride ++ tail) output
            (.tick :: work₁) work₂ current₁ current₂ current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₁)

private theorem loadStep₃_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
      (some (affineUnaryTripleProgressionCfg .loadStep₃ buffer₁ buffer₂ test
        (encodeUnaryFrameBlock stride ++ tail) output work₁ work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .next (some .separator)
        buffer₂ test tail output (List.replicate stride .tick ++ work₁) work₂
        current₁ current₂ current₃) := by
  induction stride generalizing buffer₁ work₁ with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 1 = (2 * stride + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
          (some (affineUnaryTripleProgressionCfg .loadStep₃ (some .tick)
            buffer₂ test (encodeUnaryFrameBlock stride ++ tail) output
            (.tick :: work₁) work₂ current₁ current₂ current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₁)

private theorem emit₁_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[3 * value + 1]
      (some (affineUnaryTripleProgressionCfg .emit₁ buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate value ()) current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .pushSeparator₁ buffer₁ buffer₂ false
        input (List.replicate value .tick ++ output) work₁
        (List.replicate value .tick ++ work₂) [] current₂ current₃) := by
  induction value generalizing test output work₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[3 * value + 1]
          (some (affineUnaryTripleProgressionCfg .emit₁ buffer₁ buffer₂ true
            input (.tick :: output) work₁ (.tick :: work₂)
            (List.replicate value ()) current₂ current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₂)

private theorem restore₁_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * value + 1]
      (some (affineUnaryTripleProgressionCfg .restore₁ buffer₁ buffer₂ test
        input output work₁ (List.replicate value .tick)
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .emit₂ buffer₁ none test
        input output work₁ [] (List.replicate value () ++ current₁)
        current₂ current₃) := by
  induction value generalizing buffer₂ current₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * value + 1]
          (some (affineUnaryTripleProgressionCfg .restore₁ buffer₁
            (some .tick) test
            input output work₁ (List.replicate value .tick)
            (() :: current₁) current₂ current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current₁)

private theorem emit₂_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[3 * value + 1]
      (some (affineUnaryTripleProgressionCfg .emit₂ buffer₁ buffer₂ test
        input output work₁ work₂ current₁ (List.replicate value ()) current₃)) =
      some (affineUnaryTripleProgressionCfg .pushSeparator₂ buffer₁ buffer₂ false
        input (List.replicate value .tick ++ output) work₁
        (List.replicate value .tick ++ work₂) current₁ [] current₃) := by
  induction value generalizing test output work₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[3 * value + 1]
          (some (affineUnaryTripleProgressionCfg .emit₂ buffer₁ buffer₂ true
            input (.tick :: output) work₁ (.tick :: work₂) current₁
            (List.replicate value ()) current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₂)

private theorem restore₂_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * value + 1]
      (some (affineUnaryTripleProgressionCfg .restore₂ buffer₁ buffer₂ test
        input output work₁ (List.replicate value .tick)
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .emit₃ buffer₁ none test
        input output work₁ [] current₁
        (List.replicate value () ++ current₂) current₃) := by
  induction value generalizing buffer₂ current₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * value + 1]
          (some (affineUnaryTripleProgressionCfg .restore₂ buffer₁
            (some .tick) test
            input output work₁ (List.replicate value .tick)
            current₁ (() :: current₂) current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current₂)

private theorem emit₃_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[3 * value + 1]
      (some (affineUnaryTripleProgressionCfg .emit₃ buffer₁ buffer₂ test
        input output work₁ work₂ current₁ current₂
        (List.replicate value ()))) =
      some (affineUnaryTripleProgressionCfg .pushSeparator₃ buffer₁ buffer₂ false
        input (List.replicate value .tick ++ output) work₁
        (List.replicate value .tick ++ work₂) current₁ current₂ []) := by
  induction value generalizing test output work₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[3 * value + 1]
          (some (affineUnaryTripleProgressionCfg .emit₃ buffer₁ buffer₂ true
            input (.tick :: output) work₁ (.tick :: work₂) current₁ current₂
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₂)

private theorem restore₃_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * value + 1]
      (some (affineUnaryTripleProgressionCfg .restore₃ buffer₁ buffer₂ test
        input output work₁ (List.replicate value .tick)
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .advance₃ buffer₁ none test
        input output work₁ [] current₁ current₂
        (List.replicate value () ++ current₃)) := by
  induction value generalizing buffer₂ current₃ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * value + 1]
          (some (affineUnaryTripleProgressionCfg .restore₃ buffer₁
            (some .tick) test
            input output work₁ (List.replicate value .tick)
            current₁ current₂ (() :: current₃))) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current₃)

private theorem advance₃_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output tail work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
      (some (affineUnaryTripleProgressionCfg .advance₃ buffer₁ buffer₂ test
        input output (List.replicate stride .tick ++ .separator :: tail) work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .advance₂ (some .separator) buffer₂
        test input output tail
        (.separator :: (List.replicate stride .tick ++ work₂))
        current₁ current₂ (List.replicate stride () ++ current₃)) := by
  induction stride generalizing buffer₁ work₂ current₃ with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 1 = (2 * stride + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
          (some (affineUnaryTripleProgressionCfg .advance₃ (some .tick)
            buffer₂ test input output
            (List.replicate stride .tick ++ .separator :: tail)
            (.tick :: work₂) current₁ current₂ (() :: current₃))) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₂)
        (() :: current₃)

private theorem advance₂_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output tail work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
      (some (affineUnaryTripleProgressionCfg .advance₂ buffer₁ buffer₂ test
        input output (List.replicate stride .tick ++ .separator :: tail) work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .advance₁ (some .separator) buffer₂
        test input output tail
        (.separator :: (List.replicate stride .tick ++ work₂))
        current₁ (List.replicate stride () ++ current₂) current₃) := by
  induction stride generalizing buffer₁ work₂ current₂ with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 1 = (2 * stride + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
          (some (affineUnaryTripleProgressionCfg .advance₂ (some .tick)
            buffer₂ test input output
            (List.replicate stride .tick ++ .separator :: tail)
            (.tick :: work₂) current₁ (() :: current₂) current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₂)
        (() :: current₂)

private theorem advance₁_eval (stride : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
      (some (affineUnaryTripleProgressionCfg .advance₁ buffer₁ buffer₂ test
        input output (List.replicate stride .tick) work₂
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .restoreSteps none buffer₂ test
        input output [] (List.replicate stride .tick ++ work₂)
        (List.replicate stride () ++ current₁) current₂ current₃) := by
  induction stride generalizing buffer₁ work₂ current₁ with
  | zero => rfl
  | succ stride ih =>
      rw [show 2 * (stride + 1) + 1 = (2 * stride + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[2 * stride + 1]
          (some (affineUnaryTripleProgressionCfg .advance₁ (some .tick)
            buffer₂ test input output (List.replicate stride .tick)
            (.tick :: work₂) (() :: current₁) current₂ current₃)) = _
      simpa only [List.replicate_succ, triple_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: work₂)
        (() :: current₁)

private theorem restoreSteps_eval (stride₁ stride₂ stride₃ : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[
        stride₁ + stride₂ + stride₃ + 3]
      (some (affineUnaryTripleProgressionCfg .restoreSteps buffer₁ buffer₂ test
        input output work₁
        (List.replicate stride₁ .tick ++ .separator ::
          (List.replicate stride₂ .tick ++ .separator ::
            List.replicate stride₃ .tick))
        current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .next buffer₁ none test
        input output
        (List.replicate stride₃ .tick ++ .separator ::
          (List.replicate stride₂ .tick ++ .separator ::
            (List.replicate stride₁ .tick ++ work₁))) []
        current₁ current₂ current₃) := by
  let symbols : List UnaryFrameSym :=
    List.replicate stride₁ UnaryFrameSym.tick ++ UnaryFrameSym.separator ::
      (List.replicate stride₂ UnaryFrameSym.tick ++ UnaryFrameSym.separator ::
        List.replicate stride₃ UnaryFrameSym.tick)
  have hlength : symbols.length = stride₁ + stride₂ + stride₃ + 2 := by
    simp [symbols]
    omega
  have hreverse : symbols.reverse ++ work₁ =
      List.replicate stride₃ .tick ++ .separator ::
        (List.replicate stride₂ .tick ++ .separator ::
          (List.replicate stride₁ .tick ++ work₁)) := by
    simp [symbols, List.reverse_append, List.append_assoc]
  have general (values : List UnaryFrameSym)
      (hvalues : ∀ symbol ∈ values, symbol ≠ .frameEnd)
      (buffer₂ : Option UnaryFrameSym) (work₁ : List UnaryFrameSym) :
      (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[
          values.length + 1]
        (some (affineUnaryTripleProgressionCfg .restoreSteps buffer₁ buffer₂ test
          input output work₁ values current₁ current₂ current₃)) =
        some (affineUnaryTripleProgressionCfg .next buffer₁ none test
          input output (values.reverse ++ work₁) []
          current₁ current₂ current₃) := by
    induction values generalizing buffer₂ work₁ with
    | nil => rfl
    | cons symbol values ih =>
        rw [show (symbol :: values).length + 1 =
            (values.length + 1) + 1 by simp,
          Function.iterate_succ_apply]
        cases symbol with
        | tick =>
            change
              (flip Option.bind
                (step affineUnaryTripleProgressionRevProgram))^[
                  values.length + 1]
                (some (affineUnaryTripleProgressionCfg .restoreSteps buffer₁
                  (some .tick) test input output (.tick :: work₁) values
                  current₁ current₂ current₃)) = _
            simpa [List.reverse_cons, List.append_assoc] using
              ih (fun symbol hsymbol => hvalues symbol (by simp [hsymbol]))
                (some .tick) (.tick :: work₁)
        | separator =>
            change
              (flip Option.bind
                (step affineUnaryTripleProgressionRevProgram))^[
                  values.length + 1]
                (some (affineUnaryTripleProgressionCfg .restoreSteps buffer₁
                  (some .separator) test input output (.separator :: work₁)
                  values current₁ current₂ current₃)) = _
            simpa [List.reverse_cons, List.append_assoc] using
              ih (fun symbol hsymbol => hvalues symbol (by simp [hsymbol]))
                (some .separator) (.separator :: work₁)
        | frameEnd =>
            exact False.elim ((hvalues .frameEnd (by simp)) rfl)
  have hsymbols : ∀ symbol ∈ symbols, symbol ≠ .frameEnd := by
    intro symbol hsymbol
    simp only [symbols, List.mem_append, List.mem_replicate,
      List.mem_cons] at hsymbol
    rcases hsymbol with hsymbol | hsymbol
    · rcases hsymbol with ⟨_, rfl⟩
      simp
    · rcases hsymbol with rfl | hsymbol
      · simp
      · rcases hsymbol with hsymbol | hsymbol
        · rcases hsymbol with ⟨_, rfl⟩
          simp
        · rcases hsymbol with rfl | hsymbol
          · simp
          · rcases hsymbol with ⟨_, rfl⟩
            simp
  have h := general symbols hsymbols buffer₂ work₁
  rw [hlength, hreverse] at h
  simpa [Nat.add_assoc] using h

private def affineUnaryTripleProgressionPhaseSteps :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | _, _, _, _, _, _, 0 => 0
  | current₁, current₂, current₃, stride₁, stride₂, stride₃, count + 1 =>
      5 * (current₁ + current₂ + current₃) +
          3 * (stride₁ + stride₂ + stride₃) + 16 +
        affineUnaryTripleProgressionPhaseSteps
          (current₁ + stride₁) (current₂ + stride₂) (current₃ + stride₃)
          stride₁ stride₂ stride₃ count

private def affineUnaryTripleProgressionStreamFrom :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → List UnaryFrameSym
  | _, _, _, _, _, _, 0 => []
  | current₁, current₂, current₃, stride₁, stride₂, stride₃, count + 1 =>
      encodeUnaryFrame [current₁, current₂, current₃] ++
        affineUnaryTripleProgressionStreamFrom
          (current₁ + stride₁) (current₂ + stride₂) (current₃ + stride₃)
          stride₁ stride₂ stride₃ count

private def affineUnaryTripleProgression_onePhase
    (current₁ current₂ current₃ stride₁ stride₂ stride₃ : Nat)
    (buffer₁ : Option UnaryFrameSym) (rest output : List UnaryFrameSym) :
    EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      (affineUnaryTripleProgressionCfg .next buffer₁ none false
        (.tick :: rest) output
        (List.replicate stride₃ .tick ++ .separator ::
          (List.replicate stride₂ .tick ++ .separator ::
            List.replicate stride₁ .tick)) []
        (List.replicate current₁ ()) (List.replicate current₂ ())
        (List.replicate current₃ ()))
      (some (affineUnaryTripleProgressionCfg .next none none false
        rest
        ((encodeUnaryFrame [current₁, current₂, current₃]).reverse ++ output)
        (List.replicate stride₃ .tick ++ .separator ::
          (List.replicate stride₂ .tick ++ .separator ::
            List.replicate stride₁ .tick)) []
        (List.replicate (current₁ + stride₁) ())
        (List.replicate (current₂ + stride₂) ())
        (List.replicate (current₃ + stride₃) ())))
      (5 * (current₁ + current₂ + current₃) +
        3 * (stride₁ + stride₂ + stride₃) + 16) := by
  let steps : List UnaryFrameSym :=
    List.replicate stride₃ UnaryFrameSym.tick ++ UnaryFrameSym.separator ::
      (List.replicate stride₂ UnaryFrameSym.tick ++ UnaryFrameSym.separator ::
        List.replicate stride₁ UnaryFrameSym.tick)
  let block₁ := encodeUnaryFrameBlock current₁
  let block₂ := encodeUnaryFrameBlock current₂
  let block₃ := encodeUnaryFrameBlock current₃
  let out₁ := block₁.reverse ++ output
  let out₂ := block₂.reverse ++ out₁
  let out₃ := block₃.reverse ++ out₂
  let afterPop := affineUnaryTripleProgressionCfg .emit₁ (some .tick) none false
    rest output steps [] (List.replicate current₁ ())
    (List.replicate current₂ ()) (List.replicate current₃ ())
  let beforeSep₁ := affineUnaryTripleProgressionCfg .pushSeparator₁
    (some .tick) none false rest (List.replicate current₁ .tick ++ output)
    steps (List.replicate current₁ .tick) []
    (List.replicate current₂ ()) (List.replicate current₃ ())
  let beforeRestore₁ := affineUnaryTripleProgressionCfg .restore₁
    (some .tick) none false rest out₁ steps
    (List.replicate current₁ .tick) []
    (List.replicate current₂ ()) (List.replicate current₃ ())
  let beforeEmit₂ := affineUnaryTripleProgressionCfg .emit₂
    (some .tick) none false rest out₁ steps []
    (List.replicate current₁ ()) (List.replicate current₂ ())
    (List.replicate current₃ ())
  let beforeSep₂ := affineUnaryTripleProgressionCfg .pushSeparator₂
    (some .tick) none false rest (List.replicate current₂ .tick ++ out₁)
    steps (List.replicate current₂ .tick)
    (List.replicate current₁ ()) [] (List.replicate current₃ ())
  let beforeRestore₂ := affineUnaryTripleProgressionCfg .restore₂
    (some .tick) none false rest out₂ steps
    (List.replicate current₂ .tick)
    (List.replicate current₁ ()) [] (List.replicate current₃ ())
  let beforeEmit₃ := affineUnaryTripleProgressionCfg .emit₃
    (some .tick) none false rest out₂ steps []
    (List.replicate current₁ ()) (List.replicate current₂ ())
    (List.replicate current₃ ())
  let beforeSep₃ := affineUnaryTripleProgressionCfg .pushSeparator₃
    (some .tick) none false rest (List.replicate current₃ .tick ++ out₂)
    steps (List.replicate current₃ .tick)
    (List.replicate current₁ ()) (List.replicate current₂ ()) []
  let beforeRestore₃ := affineUnaryTripleProgressionCfg .restore₃
    (some .tick) none false rest out₃ steps
    (List.replicate current₃ .tick)
    (List.replicate current₁ ()) (List.replicate current₂ ()) []
  let beforeAdvance₃ := affineUnaryTripleProgressionCfg .advance₃
    (some .tick) none false rest out₃ steps []
    (List.replicate current₁ ()) (List.replicate current₂ ())
    (List.replicate current₃ ())
  let beforeAdvance₂ := affineUnaryTripleProgressionCfg .advance₂
    (some .separator) none false rest out₃
    (List.replicate stride₂ .tick ++ .separator ::
      List.replicate stride₁ .tick)
    (.separator :: List.replicate stride₃ .tick)
    (List.replicate current₁ ()) (List.replicate current₂ ())
    (List.replicate (current₃ + stride₃) ())
  let beforeAdvance₁ := affineUnaryTripleProgressionCfg .advance₁
    (some .separator) none false rest out₃ (List.replicate stride₁ .tick)
    (.separator :: (List.replicate stride₂ .tick ++ .separator ::
      List.replicate stride₃ .tick))
    (List.replicate current₁ ())
    (List.replicate (current₂ + stride₂) ())
    (List.replicate (current₃ + stride₃) ())
  let beforeRestoreSteps := affineUnaryTripleProgressionCfg .restoreSteps
    none none false rest out₃ []
    (List.replicate stride₁ .tick ++ .separator ::
      (List.replicate stride₂ .tick ++ .separator ::
        List.replicate stride₃ .tick))
    (List.replicate (current₁ + stride₁) ())
    (List.replicate (current₂ + stride₂) ())
    (List.replicate (current₃ + stride₃) ())
  have hout₁ :
      .separator :: (List.replicate current₁ .tick ++ output) = out₁ := by
    simp [out₁, block₁, encodeUnaryFrameBlock, List.reverse_append]
  have hout₂ :
      .separator :: (List.replicate current₂ .tick ++ out₁) = out₂ := by
    simp [out₂, block₂, encodeUnaryFrameBlock, List.reverse_append]
  have hout₃ :
      .separator :: (List.replicate current₃ .tick ++ out₂) = out₃ := by
    simp [out₃, block₃, encodeUnaryFrameBlock, List.reverse_append]
  have houtFull : out₃ =
      (encodeUnaryFrame [current₁, current₂, current₃]).reverse ++ output := by
    simp [out₃, out₂, out₁, block₁, block₂, block₃, encodeUnaryFrame,
      List.reverse_append, List.append_assoc]
  have hpop : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      (affineUnaryTripleProgressionCfg .next buffer₁ none false
        (.tick :: rest) output steps []
        (List.replicate current₁ ()) (List.replicate current₂ ())
        (List.replicate current₃ ())) (some afterPop) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hemit₁ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      afterPop (some beforeSep₁) (3 * current₁ + 1) :=
    ⟨⟨_, by simpa [afterPop, beforeSep₁] using
      (emit₁_eval current₁ (some .tick) none false rest output steps []
        (List.replicate current₂ ()) (List.replicate current₃ ()))⟩, le_rfl⟩
  have hsep₁ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeSep₁ (some beforeRestore₁) 1 := by
    have hraw :
        (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[1]
          (some beforeSep₁) =
        some (affineUnaryTripleProgressionCfg .restore₁
          (some .tick) none false rest
          (.separator :: (List.replicate current₁ .tick ++ output)) steps
          (List.replicate current₁ .tick) []
          (List.replicate current₂ ()) (List.replicate current₃ ())) := by
      rfl
    rw [hout₁] at hraw
    exact ⟨⟨1, by simpa [beforeRestore₁] using hraw⟩, le_rfl⟩
  have hrestore₁ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeRestore₁ (some beforeEmit₂) (2 * current₁ + 1) :=
    ⟨⟨_, by simpa [beforeRestore₁, beforeEmit₂] using
      (restore₁_eval current₁ (some .tick) none false rest out₁ steps []
        (List.replicate current₂ ()) (List.replicate current₃ ()))⟩, le_rfl⟩
  have hemit₂ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeEmit₂ (some beforeSep₂) (3 * current₂ + 1) :=
    ⟨⟨_, by simpa [beforeEmit₂, beforeSep₂] using
      (emit₂_eval current₂ (some .tick) none false rest out₁ steps []
        (List.replicate current₁ ()) (List.replicate current₃ ()))⟩, le_rfl⟩
  have hsep₂ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeSep₂ (some beforeRestore₂) 1 := by
    have hraw :
        (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[1]
          (some beforeSep₂) =
        some (affineUnaryTripleProgressionCfg .restore₂
          (some .tick) none false rest
          (.separator :: (List.replicate current₂ .tick ++ out₁)) steps
          (List.replicate current₂ .tick)
          (List.replicate current₁ ()) [] (List.replicate current₃ ())) := by
      rfl
    rw [hout₂] at hraw
    exact ⟨⟨1, by simpa [beforeRestore₂] using hraw⟩, le_rfl⟩
  have hrestore₂ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeRestore₂ (some beforeEmit₃) (2 * current₂ + 1) :=
    ⟨⟨_, by simpa [beforeRestore₂, beforeEmit₃] using
      (restore₂_eval current₂ (some .tick) none false rest out₂ steps
        (List.replicate current₁ ()) [] (List.replicate current₃ ()))⟩, le_rfl⟩
  have hemit₃ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeEmit₃ (some beforeSep₃) (3 * current₃ + 1) :=
    ⟨⟨_, by simpa [beforeEmit₃, beforeSep₃] using
      (emit₃_eval current₃ (some .tick) none false rest out₂ steps []
        (List.replicate current₁ ()) (List.replicate current₂ ()))⟩, le_rfl⟩
  have hsep₃ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeSep₃ (some beforeRestore₃) 1 := by
    have hraw :
        (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[1]
          (some beforeSep₃) =
        some (affineUnaryTripleProgressionCfg .restore₃
          (some .tick) none false rest
          (.separator :: (List.replicate current₃ .tick ++ out₂)) steps
          (List.replicate current₃ .tick)
          (List.replicate current₁ ()) (List.replicate current₂ ()) []) := by
      rfl
    rw [hout₃] at hraw
    exact ⟨⟨1, by simpa [beforeRestore₃] using hraw⟩, le_rfl⟩
  have hrestore₃ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeRestore₃ (some beforeAdvance₃) (2 * current₃ + 1) :=
    ⟨⟨_, by simpa [beforeRestore₃, beforeAdvance₃] using
      (restore₃_eval current₃ (some .tick) none false rest out₃ steps
        (List.replicate current₁ ()) (List.replicate current₂ ()) [])⟩, le_rfl⟩
  have hcurrent₃ :
      List.replicate stride₃ () ++ List.replicate current₃ () =
        List.replicate (current₃ + stride₃) () := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hadvance₃ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeAdvance₃ (some beforeAdvance₂) (2 * stride₃ + 1) := by
    have h := advance₃_eval stride₃ (some .tick) none false rest out₃
      (List.replicate stride₂ .tick ++ .separator ::
        List.replicate stride₁ .tick) []
      (List.replicate current₁ ()) (List.replicate current₂ ())
      (List.replicate current₃ ())
    rw [List.append_nil, hcurrent₃] at h
    exact ⟨⟨_, by simpa [beforeAdvance₃, beforeAdvance₂, steps] using h⟩,
      le_rfl⟩
  have hcurrent₂ :
      List.replicate stride₂ () ++ List.replicate current₂ () =
        List.replicate (current₂ + stride₂) () := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hadvance₂ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeAdvance₂ (some beforeAdvance₁) (2 * stride₂ + 1) := by
    have h := advance₂_eval stride₂ (some .separator) none false rest out₃
      (List.replicate stride₁ .tick)
      (.separator :: List.replicate stride₃ .tick)
      (List.replicate current₁ ()) (List.replicate current₂ ())
      (List.replicate (current₃ + stride₃) ())
    rw [hcurrent₂] at h
    exact ⟨⟨_, by simpa [beforeAdvance₂, beforeAdvance₁] using h⟩, le_rfl⟩
  have hcurrent₁ :
      List.replicate stride₁ () ++ List.replicate current₁ () =
        List.replicate (current₁ + stride₁) () := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hadvance₁ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeAdvance₁ (some beforeRestoreSteps) (2 * stride₁ + 1) := by
    have h := advance₁_eval stride₁ (some .separator) none false rest out₃
      (.separator :: (List.replicate stride₂ .tick ++ .separator ::
        List.replicate stride₃ .tick))
      (List.replicate current₁ ())
      (List.replicate (current₂ + stride₂) ())
      (List.replicate (current₃ + stride₃) ())
    rw [hcurrent₁] at h
    exact ⟨⟨_, by simpa [beforeAdvance₁, beforeRestoreSteps] using h⟩, le_rfl⟩
  have hrestoreSteps : EvalsToInTime
      (step affineUnaryTripleProgressionRevProgram)
      beforeRestoreSteps
      (some (affineUnaryTripleProgressionCfg .next none none false rest out₃
        steps []
        (List.replicate (current₁ + stride₁) ())
        (List.replicate (current₂ + stride₂) ())
        (List.replicate (current₃ + stride₃) ())))
      (stride₁ + stride₂ + stride₃ + 3) :=
    ⟨⟨_, by simpa [beforeRestoreSteps, steps] using
      (restoreSteps_eval stride₁ stride₂ stride₃ none none false rest out₃ []
        (List.replicate (current₁ + stride₁) ())
        (List.replicate (current₂ + stride₂) ())
        (List.replicate (current₃ + stride₃) ()))⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    1 (3 * current₁ + 1) _ afterPop _ hpop hemit₁
  let h₂ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((3 * current₁ + 1) + 1) 1 _ beforeSep₁ _ h₁ hsep₁
  let h₃ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    (1 + ((3 * current₁ + 1) + 1)) (2 * current₁ + 1)
    _ beforeRestore₁ _ h₂ hrestore₁
  let h₄ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * current₁ + 1) + (1 + ((3 * current₁ + 1) + 1)))
    (3 * current₂ + 1) _ beforeEmit₂ _ h₃ hemit₂
  let h₅ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((3 * current₂ + 1) +
      ((2 * current₁ + 1) + (1 + ((3 * current₁ + 1) + 1))))
    1 _ beforeSep₂ _ h₄ hsep₂
  let h₆ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    (1 + ((3 * current₂ + 1) +
      ((2 * current₁ + 1) + (1 + ((3 * current₁ + 1) + 1)))))
    (2 * current₂ + 1) _ beforeRestore₂ _ h₅ hrestore₂
  let h₇ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * current₂ + 1) + (1 + ((3 * current₂ + 1) +
      ((2 * current₁ + 1) + (1 + ((3 * current₁ + 1) + 1))))))
    (3 * current₃ + 1) _ beforeEmit₃ _ h₆ hemit₃
  let h₈ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((3 * current₃ + 1) + ((2 * current₂ + 1) +
      (1 + ((3 * current₂ + 1) + ((2 * current₁ + 1) +
        (1 + ((3 * current₁ + 1) + 1)))))))
    1 _ beforeSep₃ _ h₇ hsep₃
  let h₉ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    (1 + ((3 * current₃ + 1) + ((2 * current₂ + 1) +
      (1 + ((3 * current₂ + 1) + ((2 * current₁ + 1) +
        (1 + ((3 * current₁ + 1) + 1))))))))
    (2 * current₃ + 1) _ beforeRestore₃ _ h₈ hrestore₃
  let h₁₀ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * current₃ + 1) + (1 + ((3 * current₃ + 1) +
      ((2 * current₂ + 1) + (1 + ((3 * current₂ + 1) +
        ((2 * current₁ + 1) + (1 + ((3 * current₁ + 1) + 1)))))))))
    (2 * stride₃ + 1) _ beforeAdvance₃ _ h₉ hadvance₃
  let h₁₁ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * stride₃ + 1) + ((2 * current₃ + 1) +
      (1 + ((3 * current₃ + 1) + ((2 * current₂ + 1) +
        (1 + ((3 * current₂ + 1) + ((2 * current₁ + 1) +
          (1 + ((3 * current₁ + 1) + 1))))))))))
    (2 * stride₂ + 1) _ beforeAdvance₂ _ h₁₀ hadvance₂
  let h₁₂ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * stride₂ + 1) + ((2 * stride₃ + 1) +
      ((2 * current₃ + 1) + (1 + ((3 * current₃ + 1) +
        ((2 * current₂ + 1) + (1 + ((3 * current₂ + 1) +
          ((2 * current₁ + 1) + (1 + ((3 * current₁ + 1) + 1)))))))))))
    (2 * stride₁ + 1) _ beforeAdvance₁ _ h₁₁ hadvance₁
  let full := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * stride₁ + 1) + ((2 * stride₂ + 1) +
      ((2 * stride₃ + 1) + ((2 * current₃ + 1) +
        (1 + ((3 * current₃ + 1) + ((2 * current₂ + 1) +
          (1 + ((3 * current₂ + 1) + ((2 * current₁ + 1) +
            (1 + ((3 * current₁ + 1) + 1))))))))))))
    (stride₁ + stride₂ + stride₃ + 3) _ beforeRestoreSteps _ h₁₂
    hrestoreSteps
  rw [houtFull] at full
  have hbound :
      stride₁ + stride₂ + stride₃ + 3 +
        ((2 * stride₁ + 1) + ((2 * stride₂ + 1) +
          ((2 * stride₃ + 1) + ((2 * current₃ + 1) +
            (1 + ((3 * current₃ + 1) + ((2 * current₂ + 1) +
              (1 + ((3 * current₂ + 1) + ((2 * current₁ + 1) +
                (1 + ((3 * current₁ + 1) + 1)))))))))))) =
        5 * (current₁ + current₂ + current₃) +
          3 * (stride₁ + stride₂ + stride₃) + 16 := by omega
  rw [← hbound]
  simpa [steps] using full

private def affineUnaryTripleProgression_inputPhases
    (current₁ current₂ current₃ stride₁ stride₂ stride₃ : Nat)
    (buffer₁ : Option UnaryFrameSym) (count : Nat)
    (tail output : List UnaryFrameSym) :
    Σ finalBuffer,
      EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
        (affineUnaryTripleProgressionCfg .next buffer₁ none false
          (List.replicate count .tick ++ tail) output
          (List.replicate stride₃ .tick ++ .separator ::
            (List.replicate stride₂ .tick ++ .separator ::
              List.replicate stride₁ .tick)) []
          (List.replicate current₁ ()) (List.replicate current₂ ())
          (List.replicate current₃ ()))
        (some (affineUnaryTripleProgressionCfg .next finalBuffer none false
          tail
          ((affineUnaryTripleProgressionStreamFrom
              current₁ current₂ current₃ stride₁ stride₂ stride₃ count).reverse ++
            output)
          (List.replicate stride₃ .tick ++ .separator ::
            (List.replicate stride₂ .tick ++ .separator ::
              List.replicate stride₁ .tick)) []
          (List.replicate (current₁ + count * stride₁) ())
          (List.replicate (current₂ + count * stride₂) ())
          (List.replicate (current₃ + count * stride₃) ())))
        (affineUnaryTripleProgressionPhaseSteps
          current₁ current₂ current₃ stride₁ stride₂ stride₃ count) := by
  induction count generalizing current₁ current₂ current₃ buffer₁ output with
  | zero =>
      exact ⟨buffer₁, ⟨⟨0, by
        simp [affineUnaryTripleProgressionStreamFrom]⟩, le_rfl⟩⟩
  | succ count ih =>
      let first := affineUnaryTripleProgression_onePhase
        current₁ current₂ current₃ stride₁ stride₂ stride₃ buffer₁
        (List.replicate count .tick ++ tail) output
      rcases ih (current₁ + stride₁) (current₂ + stride₂)
          (current₃ + stride₃) none
          ((encodeUnaryFrame [current₁, current₂, current₃]).reverse ++ output) with
        ⟨finalBuffer, remaining⟩
      let full := EvalsToInTime.trans
        (step affineUnaryTripleProgressionRevProgram)
        (5 * (current₁ + current₂ + current₃) +
          3 * (stride₁ + stride₂ + stride₃) + 16)
        (affineUnaryTripleProgressionPhaseSteps
          (current₁ + stride₁) (current₂ + stride₂) (current₃ + stride₃)
          stride₁ stride₂ stride₃ count)
        _
        (affineUnaryTripleProgressionCfg .next none none false
          (List.replicate count .tick ++ tail)
          ((encodeUnaryFrame [current₁, current₂, current₃]).reverse ++ output)
          (List.replicate stride₃ .tick ++ .separator ::
            (List.replicate stride₂ .tick ++ .separator ::
              List.replicate stride₁ .tick)) []
          (List.replicate (current₁ + stride₁) ())
          (List.replicate (current₂ + stride₂) ())
          (List.replicate (current₃ + stride₃) ()))
        _ first remaining
      have hcurrent₁ : current₁ + stride₁ + count * stride₁ =
          current₁ + (count + 1) * stride₁ := by
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hcurrent₂ : current₂ + stride₂ + count * stride₂ =
          current₂ + (count + 1) * stride₂ := by
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hcurrent₃ : current₃ + stride₃ + count * stride₃ =
          current₃ + (count + 1) * stride₃ := by
        simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      have hout :
          (affineUnaryTripleProgressionStreamFrom
              (current₁ + stride₁) (current₂ + stride₂) (current₃ + stride₃)
              stride₁ stride₂ stride₃ count).reverse ++
              ((encodeUnaryFrame [current₁, current₂, current₃]).reverse ++
                output) =
            (affineUnaryTripleProgressionStreamFrom
              current₁ current₂ current₃ stride₁ stride₂ stride₃
              (count + 1)).reverse ++ output := by
        simp [affineUnaryTripleProgressionStreamFrom, List.reverse_append,
          List.append_assoc]
      rw [hcurrent₁, hcurrent₂, hcurrent₃, hout] at full
      refine ⟨finalBuffer, ?_⟩
      simpa [List.replicate_succ, affineUnaryTripleProgressionPhaseSteps,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using full

private theorem affineUnaryTripleProgressionStreamFrom_eq
    (base₁ base₂ base₃ stride₁ stride₂ stride₃ count : Nat) :
    affineUnaryTripleProgressionStreamFrom
        base₁ base₂ base₃ stride₁ stride₂ stride₃ count =
      (affineUnaryTripleProgressionRowsFrom
        base₁ base₂ base₃ stride₁ stride₂ stride₃ count).flatMap fun row =>
          encodeUnaryFrame (affineUnaryTripleRowValues row) := by
  induction count generalizing base₁ base₂ base₃ with
  | zero => rfl
  | succ count ih =>
      simp [affineUnaryTripleProgressionStreamFrom,
        affineUnaryTripleProgressionRowsFrom, affineUnaryTripleRowValues, ih]

private theorem clear₁_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[value + 1]
      (some (affineUnaryTripleProgressionCfg .clear₁ buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate value ()) current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .clear₂ buffer₁ buffer₂ false
        input output work₁ work₂ [] current₂ current₃) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[value + 1]
          (some (affineUnaryTripleProgressionCfg .clear₁ buffer₁ buffer₂ true
            input output work₁ work₂ (List.replicate value ())
            current₂ current₃)) = _
      simpa using ih true

private theorem clear₂_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[value + 1]
      (some (affineUnaryTripleProgressionCfg .clear₂ buffer₁ buffer₂ test
        input output work₁ work₂ current₁ (List.replicate value ()) current₃)) =
      some (affineUnaryTripleProgressionCfg .clear₃ buffer₁ buffer₂ false
        input output work₁ work₂ current₁ [] current₃) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[value + 1]
          (some (affineUnaryTripleProgressionCfg .clear₂ buffer₁ buffer₂ true
            input output work₁ work₂ current₁ (List.replicate value ())
            current₃)) = _
      simpa using ih true

private theorem clear₃_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current₁ current₂ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[value + 1]
      (some (affineUnaryTripleProgressionCfg .clear₃ buffer₁ buffer₂ test
        input output work₁ work₂ current₁ current₂
        (List.replicate value ()))) =
      some (affineUnaryTripleProgressionCfg .clearSteps buffer₁ buffer₂ false
        input output work₁ work₂ current₁ current₂ []) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[value + 1]
          (some (affineUnaryTripleProgressionCfg .clear₃ buffer₁ buffer₂ true
            input output work₁ work₂ current₁ current₂
            (List.replicate value ()))) = _
      simpa using ih true

private theorem clearSteps_eval (values : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (current₁ current₂ current₃ : List Unit) :
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[
        values.length + 1]
      (some (affineUnaryTripleProgressionCfg .clearSteps buffer₁ buffer₂ test
        input output values work₂ current₁ current₂ current₃)) =
      some (affineUnaryTripleProgressionCfg .halt none buffer₂ test
        input output [] work₂ current₁ current₂ current₃) := by
  induction values generalizing buffer₁ with
  | nil => rfl
  | cons value values ih =>
      rw [show (value :: values).length + 1 = values.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineUnaryTripleProgressionRevProgram))^[values.length + 1]
          (some (affineUnaryTripleProgressionCfg .clearSteps (some value)
            buffer₂ test input output values work₂ current₁ current₂ current₃)) = _
      simpa using ih (some value)

def affineUnaryTripleProgressionRevSteps
    (progression : AffineUnaryTripleProgression) : Nat :=
  (2 * progression.base₁ + 1) +
    (2 * progression.base₂ + 1) +
    (2 * progression.base₃ + 1) +
    (2 * progression.step₁ + 2) +
    (2 * progression.step₂ + 2) +
    (2 * progression.step₃ + 1) +
    affineUnaryTripleProgressionPhaseSteps
      progression.base₁ progression.base₂ progression.base₃
      progression.step₁ progression.step₂ progression.step₃ progression.count +
    1 +
    (progression.base₁ + progression.count * progression.step₁ + 1) +
    (progression.base₂ + progression.count * progression.step₂ + 1) +
    (progression.base₃ + progression.count * progression.step₃ + 1) +
    (progression.step₁ + progression.step₂ + progression.step₃ + 3) + 1

/-- Exact cost through the redirectable finish label, before its standalone
halt instruction. -/
def affineUnaryTripleProgressionBodySteps
    (progression : AffineUnaryTripleProgression) : Nat :=
  affineUnaryTripleProgressionRevSteps progression - 1

/-- Exact contextual run through the redirectable finish label.  It consumes
one canonical seven-field descriptor and preserves both the remaining input
tail and the existing output suffix. -/
def affineUnaryTripleProgression_runToFinishWithTail
    (progression : AffineUnaryTripleProgression)
    (tail outputSuffix : List UnaryFrameSym) :
    EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      (affineUnaryTripleProgressionLoopCfg
        (encodeAffineUnaryTripleProgression progression ++ tail)
        outputSuffix)
      (some (affineUnaryTripleProgressionFinishCfg tail
        ((affineUnaryTripleProgressionFrameStream progression).reverse ++
          outputSuffix)))
      (affineUnaryTripleProgressionBodySteps progression) := by
  let base₂Frame := encodeUnaryFrameBlock progression.base₂
  let base₃Frame := encodeUnaryFrameBlock progression.base₃
  let step₁Frame := encodeUnaryFrameBlock progression.step₁
  let step₂Frame := encodeUnaryFrameBlock progression.step₂
  let step₃Frame := encodeUnaryFrameBlock progression.step₃
  let countFrame := encodeUnaryFrameBlock progression.count
  let steps : List UnaryFrameSym :=
    List.replicate progression.step₃ .tick ++ .separator ::
      (List.replicate progression.step₂ .tick ++ .separator ::
        List.replicate progression.step₁ .tick)
  let afterBase₁ := affineUnaryTripleProgressionCfg .loadBase₂
    (some .separator) none false
    (base₂Frame ++ base₃Frame ++ step₁Frame ++ step₂Frame ++ step₃Frame ++
      countFrame ++ tail) outputSuffix [] []
    (List.replicate progression.base₁ ()) [] []
  let afterBase₂ := affineUnaryTripleProgressionCfg .loadBase₃
    (some .separator) none false
    (base₃Frame ++ step₁Frame ++ step₂Frame ++ step₃Frame ++
      countFrame ++ tail)
    outputSuffix [] [] (List.replicate progression.base₁ ())
    (List.replicate progression.base₂ ()) []
  let afterBase₃ := affineUnaryTripleProgressionCfg .loadStep₁
    (some .separator) none false
    (step₁Frame ++ step₂Frame ++ step₃Frame ++ countFrame ++ tail)
    outputSuffix [] []
    (List.replicate progression.base₁ ())
    (List.replicate progression.base₂ ())
    (List.replicate progression.base₃ ())
  let afterStep₁ := affineUnaryTripleProgressionCfg .loadStep₂
    (some .separator) none false
    (step₂Frame ++ step₃Frame ++ countFrame ++ tail)
    outputSuffix (.separator :: List.replicate progression.step₁ .tick) []
    (List.replicate progression.base₁ ())
    (List.replicate progression.base₂ ())
    (List.replicate progression.base₃ ())
  let afterStep₂ := affineUnaryTripleProgressionCfg .loadStep₃
    (some .separator) none false (step₃Frame ++ countFrame ++ tail)
    outputSuffix
    (.separator :: (List.replicate progression.step₂ .tick ++
      .separator :: List.replicate progression.step₁ .tick)) []
    (List.replicate progression.base₁ ())
    (List.replicate progression.base₂ ())
    (List.replicate progression.base₃ ())
  let afterStep₃ := affineUnaryTripleProgressionCfg .next
    (some .separator) none false (countFrame ++ tail) outputSuffix steps []
    (List.replicate progression.base₁ ())
    (List.replicate progression.base₂ ())
    (List.replicate progression.base₃ ())
  have hbase₁ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      (affineUnaryTripleProgressionLoopCfg
        (encodeAffineUnaryTripleProgression progression ++ tail)
        outputSuffix)
      (some afterBase₁) (2 * progression.base₁ + 1) :=
    ⟨⟨_, by simpa [encodeAffineUnaryTripleProgression, encodeUnaryFrame,
      base₂Frame, base₃Frame, step₁Frame, step₂Frame, step₃Frame, countFrame,
      afterBase₁, affineUnaryTripleProgressionLoopCfg,
      affineUnaryTripleProgressionCfg,
      affineUnaryTripleProgressionRevProgram, List.append_assoc] using
      (loadBase₁_eval progression.base₁ none none false
        (base₂Frame ++ base₃Frame ++ step₁Frame ++ step₂Frame ++ step₃Frame ++
          countFrame ++ tail) outputSuffix [] [] [] [] [])⟩, le_rfl⟩
  have hbase₂ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      afterBase₁ (some afterBase₂) (2 * progression.base₂ + 1) :=
    ⟨⟨_, by simpa [afterBase₁, afterBase₂] using
      (loadBase₂_eval progression.base₂ (some .separator) none false
        (base₃Frame ++ step₁Frame ++ step₂Frame ++ step₃Frame ++
          countFrame ++ tail)
        outputSuffix [] [] (List.replicate progression.base₁ ()) [] [])⟩,
      le_rfl⟩
  have hbase₃ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      afterBase₂ (some afterBase₃) (2 * progression.base₃ + 1) :=
    ⟨⟨_, by simpa [afterBase₂, afterBase₃] using
      (loadBase₃_eval progression.base₃ (some .separator) none false
        (step₁Frame ++ step₂Frame ++ step₃Frame ++ countFrame ++ tail)
        outputSuffix [] []
        (List.replicate progression.base₁ ())
        (List.replicate progression.base₂ ()) [])⟩, le_rfl⟩
  have hstep₁ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      afterBase₃ (some afterStep₁) (2 * progression.step₁ + 2) :=
    ⟨⟨_, by simpa [afterBase₃, afterStep₁] using
      (loadStep₁_eval progression.step₁ (some .separator) none false
        (step₂Frame ++ step₃Frame ++ countFrame ++ tail)
        outputSuffix [] []
        (List.replicate progression.base₁ ())
        (List.replicate progression.base₂ ())
        (List.replicate progression.base₃ ()))⟩, le_rfl⟩
  have hstep₂ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      afterStep₁ (some afterStep₂) (2 * progression.step₂ + 2) :=
    ⟨⟨_, by simpa [afterStep₁, afterStep₂] using
      (loadStep₂_eval progression.step₂ (some .separator) none false
        (step₃Frame ++ countFrame ++ tail) outputSuffix
        (.separator :: List.replicate progression.step₁ .tick) []
        (List.replicate progression.base₁ ())
        (List.replicate progression.base₂ ())
        (List.replicate progression.base₃ ()))⟩, le_rfl⟩
  have hstep₃ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      afterStep₂ (some afterStep₃) (2 * progression.step₃ + 1) :=
    ⟨⟨_, by simpa [afterStep₂, afterStep₃, steps] using
      (loadStep₃_eval progression.step₃ (some .separator) none false
        (countFrame ++ tail) outputSuffix
        (.separator :: (List.replicate progression.step₂ .tick ++
          .separator :: List.replicate progression.step₁ .tick)) []
        (List.replicate progression.base₁ ())
        (List.replicate progression.base₂ ())
        (List.replicate progression.base₃ ()))⟩, le_rfl⟩
  rcases affineUnaryTripleProgression_inputPhases
      progression.base₁ progression.base₂ progression.base₃
      progression.step₁ progression.step₂ progression.step₃
      (some .separator) progression.count (.separator :: tail) outputSuffix with
    ⟨finalBuffer, phases⟩
  let final₁ := progression.base₁ + progression.count * progression.step₁
  let final₂ := progression.base₂ + progression.count * progression.step₂
  let final₃ := progression.base₃ + progression.count * progression.step₃
  let output :=
    (affineUnaryTripleProgressionFrameStream progression).reverse ++
      outputSuffix
  have hphases : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      afterStep₃
      (some (affineUnaryTripleProgressionCfg .next finalBuffer none false
        (.separator :: tail) output steps []
        (List.replicate final₁ ()) (List.replicate final₂ ())
        (List.replicate final₃ ())))
      (affineUnaryTripleProgressionPhaseSteps
        progression.base₁ progression.base₂ progression.base₃
        progression.step₁ progression.step₂ progression.step₃
        progression.count) := by
    simpa [afterStep₃, countFrame, encodeUnaryFrameBlock, steps, output,
      final₁, final₂, final₃, affineUnaryTripleProgressionFrameStream,
      affineUnaryTripleProgressionRows,
      affineUnaryTripleProgressionStreamFrom_eq] using phases
  let beforeClear₁ := affineUnaryTripleProgressionCfg .clear₁
    (some .separator) none false tail output steps []
    (List.replicate final₁ ()) (List.replicate final₂ ())
    (List.replicate final₃ ())
  let beforeClear₂ := affineUnaryTripleProgressionCfg .clear₂
    (some .separator) none false tail output steps [] []
    (List.replicate final₂ ()) (List.replicate final₃ ())
  let beforeClear₃ := affineUnaryTripleProgressionCfg .clear₃
    (some .separator) none false tail output steps [] [] []
    (List.replicate final₃ ())
  let beforeClearSteps := affineUnaryTripleProgressionCfg .clearSteps
    (some .separator) none false tail output steps [] [] [] []
  let beforeHalt := affineUnaryTripleProgressionCfg .halt
    none none false tail output [] [] [] [] []
  have hcount : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      (affineUnaryTripleProgressionCfg .next finalBuffer none false
        (.separator :: tail) output steps []
        (List.replicate final₁ ()) (List.replicate final₂ ())
        (List.replicate final₃ ()))
      (some beforeClear₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear₁ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeClear₁ (some beforeClear₂) (final₁ + 1) :=
    ⟨⟨_, by simpa [beforeClear₁, beforeClear₂] using
      (clear₁_eval final₁ (some .separator) none false tail output steps []
        (List.replicate final₂ ()) (List.replicate final₃ ()))⟩, le_rfl⟩
  have hclear₂ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeClear₂ (some beforeClear₃) (final₂ + 1) :=
    ⟨⟨_, by simpa [beforeClear₂, beforeClear₃] using
      (clear₂_eval final₂ (some .separator) none false tail output steps [] []
        (List.replicate final₃ ()))⟩, le_rfl⟩
  have hclear₃ : EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      beforeClear₃ (some beforeClearSteps) (final₃ + 1) :=
    ⟨⟨_, by simpa [beforeClear₃, beforeClearSteps] using
      (clear₃_eval final₃ (some .separator) none false tail output steps [] [] [])⟩,
      le_rfl⟩
  have hstepsLength : steps.length =
      progression.step₁ + progression.step₂ + progression.step₃ + 2 := by
    simp [steps]
    omega
  have hclearSteps : EvalsToInTime
      (step affineUnaryTripleProgressionRevProgram)
      beforeClearSteps (some beforeHalt)
      (progression.step₁ + progression.step₂ + progression.step₃ + 3) := by
    have h := clearSteps_eval steps (some .separator) none false tail output []
      [] [] []
    rw [hstepsLength] at h
    exact ⟨⟨_, by simpa [beforeClearSteps, beforeHalt] using h⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    (2 * progression.base₁ + 1) (2 * progression.base₂ + 1)
    _ afterBase₁ _ hbase₁ hbase₂
  let h₂ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1))
    (2 * progression.base₃ + 1) _ afterBase₂ _ h₁ hbase₃
  let h₃ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * progression.base₃ + 1) +
      ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1)))
    (2 * progression.step₁ + 2) _ afterBase₃ _ h₂ hstep₁
  let h₄ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
      ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1))))
    (2 * progression.step₂ + 2) _ afterStep₁ _ h₃ hstep₂
  let h₅ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * progression.step₂ + 2) + ((2 * progression.step₁ + 2) +
      ((2 * progression.base₃ + 1) + ((2 * progression.base₂ + 1) +
        (2 * progression.base₁ + 1)))))
    (2 * progression.step₃ + 1) _ afterStep₂ _ h₄ hstep₃
  let h₆ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((2 * progression.step₃ + 1) + ((2 * progression.step₂ + 2) +
      ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
        ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1))))))
    (affineUnaryTripleProgressionPhaseSteps
      progression.base₁ progression.base₂ progression.base₃
      progression.step₁ progression.step₂ progression.step₃ progression.count)
    _ afterStep₃ _ h₅ hphases
  let h₇ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    (affineUnaryTripleProgressionPhaseSteps
      progression.base₁ progression.base₂ progression.base₃
      progression.step₁ progression.step₂ progression.step₃ progression.count +
      ((2 * progression.step₃ + 1) + ((2 * progression.step₂ + 2) +
        ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
          ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1)))))))
    1 _ _ _ h₆ hcount
  let h₈ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    (1 + (affineUnaryTripleProgressionPhaseSteps
      progression.base₁ progression.base₂ progression.base₃
      progression.step₁ progression.step₂ progression.step₃ progression.count +
      ((2 * progression.step₃ + 1) + ((2 * progression.step₂ + 2) +
        ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
          ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1))))))))
    (final₁ + 1) _ beforeClear₁ _ h₇ hclear₁
  let h₉ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((final₁ + 1) + (1 + (affineUnaryTripleProgressionPhaseSteps
      progression.base₁ progression.base₂ progression.base₃
      progression.step₁ progression.step₂ progression.step₃ progression.count +
      ((2 * progression.step₃ + 1) + ((2 * progression.step₂ + 2) +
        ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
          ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1)))))))))
    (final₂ + 1) _ beforeClear₂ _ h₈ hclear₂
  let h₁₀ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((final₂ + 1) + ((final₁ + 1) +
      (1 + (affineUnaryTripleProgressionPhaseSteps
        progression.base₁ progression.base₂ progression.base₃
        progression.step₁ progression.step₂ progression.step₃ progression.count +
        ((2 * progression.step₃ + 1) + ((2 * progression.step₂ + 2) +
          ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
            ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1))))))))))
    (final₃ + 1) _ beforeClear₃ _ h₉ hclear₃
  let h₁₁ := EvalsToInTime.trans (step affineUnaryTripleProgressionRevProgram)
    ((final₃ + 1) + ((final₂ + 1) + ((final₁ + 1) +
      (1 + (affineUnaryTripleProgressionPhaseSteps
        progression.base₁ progression.base₂ progression.base₃
        progression.step₁ progression.step₂ progression.step₃ progression.count +
        ((2 * progression.step₃ + 1) + ((2 * progression.step₂ + 2) +
          ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
            ((2 * progression.base₂ + 1) + (2 * progression.base₁ + 1)))))))))))
    (progression.step₁ + progression.step₂ + progression.step₃ + 3)
    _ beforeClearSteps _ h₁₀ hclearSteps
  have hbound :
      (progression.step₁ + progression.step₂ + progression.step₃ + 3) +
        ((final₃ + 1) + ((final₂ + 1) + ((final₁ + 1) +
          (1 + (affineUnaryTripleProgressionPhaseSteps
            progression.base₁ progression.base₂ progression.base₃
            progression.step₁ progression.step₂ progression.step₃
            progression.count +
            ((2 * progression.step₃ + 1) + ((2 * progression.step₂ + 2) +
              ((2 * progression.step₁ + 2) + ((2 * progression.base₃ + 1) +
                ((2 * progression.base₂ + 1) +
                  (2 * progression.base₁ + 1))))))))))) =
        affineUnaryTripleProgressionBodySteps progression := by
    simp only [affineUnaryTripleProgressionBodySteps,
      affineUnaryTripleProgressionRevSteps, final₁, final₂, final₃]
    omega
  rw [← hbound]
  simpa [output, affineUnaryTripleProgressionFinishCfg] using h₁₁

/-- Exact successful run on every standalone canonical structured input. -/
def affineUnaryTripleProgressionRev_run
    (progression : AffineUnaryTripleProgression) :
    EvalsToInTime (step affineUnaryTripleProgressionRevProgram)
      (initialCfg affineUnaryTripleProgressionRevProgram
        (encodeAffineUnaryTripleProgression progression))
      (some (haltCfg affineUnaryTripleProgressionRevProgram
        (affineUnaryTripleProgressionFrameStream progression).reverse))
      (affineUnaryTripleProgressionRevSteps progression) := by
  have body := affineUnaryTripleProgression_runToFinishWithTail
    progression [] []
  have body' : EvalsToInTime
      (step affineUnaryTripleProgressionRevProgram)
      (affineUnaryTripleProgressionLoopCfg
        (encodeAffineUnaryTripleProgression progression) [])
      (some (affineUnaryTripleProgressionFinishCfg []
        (affineUnaryTripleProgressionFrameStream progression).reverse))
      (affineUnaryTripleProgressionBodySteps progression) := by
    simpa using body
  have haltStep : EvalsToInTime
      (step affineUnaryTripleProgressionRevProgram)
      (affineUnaryTripleProgressionFinishCfg []
        (affineUnaryTripleProgressionFrameStream progression).reverse)
      (some (haltCfg affineUnaryTripleProgressionRevProgram
        (affineUnaryTripleProgressionFrameStream progression).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step affineUnaryTripleProgressionRevProgram)
    (affineUnaryTripleProgressionBodySteps progression) 1 _ _ _
    body' haltStep
  convert full using 1
  · rfl
  · unfold affineUnaryTripleProgressionBodySteps
    have hpos : 0 < affineUnaryTripleProgressionRevSteps progression := by
      simp [affineUnaryTripleProgressionRevSteps]
    omega

private theorem affineUnaryTripleProgressionPhaseSteps_le
    (current₁ current₂ current₃ stride₁ stride₂ stride₃ count : Nat) :
    affineUnaryTripleProgressionPhaseSteps
        current₁ current₂ current₃ stride₁ stride₂ stride₃ count ≤
      count *
        (5 * (current₁ + current₂ + current₃ +
          count * (stride₁ + stride₂ + stride₃)) +
          3 * (stride₁ + stride₂ + stride₃) + 16) := by
  induction count generalizing current₁ current₂ current₃ with
  | zero => simp [affineUnaryTripleProgressionPhaseSteps]
  | succ count ih =>
      simp only [affineUnaryTripleProgressionPhaseSteps]
      have h := ih (current₁ + stride₁) (current₂ + stride₂)
        (current₃ + stride₃)
      nlinarith

private theorem encodeAffineUnaryTripleProgression_length
    (progression : AffineUnaryTripleProgression) :
    (encodeAffineUnaryTripleProgression progression).length =
      progression.base₁ + progression.base₂ + progression.base₃ +
        progression.step₁ + progression.step₂ + progression.step₃ +
        progression.count + 7 := by
  simp [encodeAffineUnaryTripleProgression]
  omega

theorem affineUnaryTripleProgressionRev_steps_le
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionRevSteps progression ≤
      100 * (encodeAffineUnaryTripleProgression progression).length ^ 3 +
        100 := by
  have hphase := affineUnaryTripleProgressionPhaseSteps_le
    progression.base₁ progression.base₂ progression.base₃
    progression.step₁ progression.step₂ progression.step₃ progression.count
  let n := progression.base₁ + progression.base₂ + progression.base₃ +
    progression.step₁ + progression.step₂ + progression.step₃ +
    progression.count + 7
  have hn : 1 ≤ n := by omega
  have hb₁ : progression.base₁ ≤ n := by omega
  have hb₂ : progression.base₂ ≤ n := by omega
  have hb₃ : progression.base₃ ≤ n := by omega
  have hs₁ : progression.step₁ ≤ n := by omega
  have hs₂ : progression.step₂ ≤ n := by omega
  have hs₃ : progression.step₃ ≤ n := by omega
  have hc : progression.count ≤ n := by omega
  have hp₁ : progression.count * progression.step₁ ≤ n ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hc hs₁
  have hp₂ : progression.count * progression.step₂ ≤ n ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hc hs₂
  have hp₃ : progression.count * progression.step₃ ≤ n ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hc hs₃
  have hbaseSum :
      progression.base₁ + progression.base₂ + progression.base₃ ≤ 3 * n := by
    omega
  have hstepSum :
      progression.step₁ + progression.step₂ + progression.step₃ ≤ 3 * n := by
    omega
  have hcountStepSum :
      progression.count *
          (progression.step₁ + progression.step₂ + progression.step₃) ≤
        3 * n ^ 2 := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have hn_square : n ≤ n ^ 2 := by nlinarith
  have hfactor :
      5 * (progression.base₁ + progression.base₂ + progression.base₃ +
          progression.count *
            (progression.step₁ + progression.step₂ + progression.step₃)) +
          3 * (progression.step₁ + progression.step₂ + progression.step₃) +
          16 ≤
        60 * n ^ 2 := by
    nlinarith
  have hphase' :
      affineUnaryTripleProgressionPhaseSteps
          progression.base₁ progression.base₂ progression.base₃
          progression.step₁ progression.step₂ progression.step₃
          progression.count ≤
        60 * n ^ 3 := by
    calc
      _ ≤ progression.count *
          (5 * (progression.base₁ + progression.base₂ + progression.base₃ +
            progression.count *
              (progression.step₁ + progression.step₂ + progression.step₃)) +
            3 * (progression.step₁ + progression.step₂ + progression.step₃) +
            16) := hphase
      _ ≤ n * (60 * n ^ 2) := Nat.mul_le_mul hc hfactor
      _ = 60 * n ^ 3 := by ring
  have hfinal₁ :
      progression.base₁ + progression.count * progression.step₁ ≤
        2 * n ^ 2 := by omega
  have hfinal₂ :
      progression.base₂ + progression.count * progression.step₂ ≤
        2 * n ^ 2 := by omega
  have hfinal₃ :
      progression.base₃ + progression.count * progression.step₃ ≤
        2 * n ^ 2 := by omega
  have hn_square_cube : n ^ 2 ≤ n ^ 3 := by nlinarith
  rw [encodeAffineUnaryTripleProgression_length]
  change affineUnaryTripleProgressionRevSteps progression ≤ 100 * n ^ 3 + 100
  simp only [affineUnaryTripleProgressionRevSteps]
  omega

/-- The redirectable contextual body inherits the standalone cubic bound. -/
theorem affineUnaryTripleProgressionBody_steps_le
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionBodySteps progression ≤
      100 * (encodeAffineUnaryTripleProgression progression).length ^ 3 +
        100 :=
  (Nat.sub_le _ _).trans
    (affineUnaryTripleProgressionRev_steps_le progression)

/-- Concrete polynomial-time machine for the reversed triple frame stream. -/
noncomputable def affineUnaryTripleProgressionRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgression id
      (fun progression =>
        (affineUnaryTripleProgressionFrameStream progression).reverse) where
  tm := compile affineUnaryTripleProgressionRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 100 * Polynomial.X ^ 3 + 100
  outputsFun := fun progression => by
    have builderRun := affineUnaryTripleProgressionRev_run progression
    have compiledRun := compile_evalsToInTime
      affineUnaryTripleProgressionRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineUnaryTripleProgressionRevProgram).step
        (_root_.Turing.initList (compile affineUnaryTripleProgressionRevProgram)
          (encodeAffineUnaryTripleProgression progression))
        (some (_root_.Turing.haltList
          (compile affineUnaryTripleProgressionRevProgram)
          (affineUnaryTripleProgressionFrameStream progression).reverse))
        (affineUnaryTripleProgressionRevSteps progression) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineUnaryTripleProgressionRevSteps progression ≤
        (100 * Polynomial.X ^ 3 + 100).eval
          (encodeAffineUnaryTripleProgression progression).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineUnaryTripleProgressionRev_steps_le progression
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineUnaryTripleProgressionRevProgram).step
        (_root_.Turing.initList (compile affineUnaryTripleProgressionRevProgram)
          (encodeAffineUnaryTripleProgression progression))
        (some (_root_.Turing.haltList
          (compile affineUnaryTripleProgressionRevProgram)
          (affineUnaryTripleProgressionFrameStream progression).reverse))
        ((100 * Polynomial.X ^ 3 + 100).eval
          (encodeAffineUnaryTripleProgression progression).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the prepend-based run gives the forward row-major triple stream. -/
noncomputable def
    affineUnaryTripleProgressionFrameStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgression id
      affineUnaryTripleProgressionFrameStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineUnaryTripleProgressionRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
