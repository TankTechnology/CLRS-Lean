import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneOutputSource
import Mathlib.Tactic

/-!
# Family source for exactly-one output wires

This layer iterates the compact one-frame source without intermediate halts.
An outer `frameEnd` terminates the family; each invocation still contains only
the frame's `start` and `count`, never its already-computed output wire.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Concatenated compact invocations in the order consumed by the family. -/
def encodeAffineExactlyOneOutputSourceInvocationFamily
    (frames : List AffineExactlyOneFrame) : List UnaryFrameSym :=
  frames.flatMap encodeAffineExactlyOneOutputSourceInvocation

/-- Unary output-wire blocks in the same frame order. -/
def affineExactlyOneOutputSourceFamilyStream
    (frames : List AffineExactlyOneFrame) : List UnaryFrameSym :=
  encodeUnaryFrame (frames.map affineExactlyOneFrameOutputWire)

/-- Outer dispatch and embedded one-frame phases. -/
inductive AffineExactlyOneOutputFamilySourceLabel
  | check
  | save (symbol : UnaryFrameSym)
  | restore | clearBuffer
  | body (label : AffineExactlyOneOutputSourceLabel)
  | finish | invalid
deriving DecidableEq, Fintype

private def outputFamilyRelabelOp :
    Op UnaryFrameSym UnaryFrameSym AffineExactlyOneOutputSourceLabel →
      Op UnaryFrameSym UnaryFrameSym
        AffineExactlyOneOutputFamilySourceLabel
  | .pushOutput symbol next => .pushOutput symbol (.body next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.body next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.body next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .inc₁ next => .inc₁ (.body next)
  | .inc₂ next => .inc₂ (.body next)
  | .inc₃ next => .inc₃ (.body next)
  | .dec₁ nextZero nextSucc => .dec₁ (.body nextZero) (.body nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.body nextZero) (.body nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.body nextZero) (.body nextSucc)
  | .jump next => .jump (.body next)
  | .halt => .halt

/-- One fixed controller for every finite list of compact invocations. -/
def affineExactlyOneOutputFamilySourceRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneOutputFamilySourceLabel
  main := .check
  op
    | .check => .popInput .invalid fun
        | .frameEnd => .finish
        | symbol => .save symbol
    | .save symbol => .pushWork₁ symbol .restore
    | .restore => .moveWork₁Input .invalid (fun _ => .clearBuffer)
    | .clearBuffer => .popWork₁
        (.body affineExactlyOneOutputSourceRevProgram.main)
        (fun _ => .invalid)
    | .body .finish => .jump .check
    | .body label => outputFamilyRelabelOp
        (affineExactlyOneOutputSourceRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

private def affineExactlyOneOutputFamilySourceCfg
    (label : AffineExactlyOneOutputFamilySourceLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineExactlyOneOutputFamilySourceRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := first
  counter₂ := second
  counter₃ := third

/-- Clean family entry. -/
def affineExactlyOneOutputFamilySourceLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneOutputFamilySourceRevProgram :=
  affineExactlyOneOutputFamilySourceCfg .check none none false
    input output [] [] [] [] []

/-- Clean outer continuation after consuming the family terminator. -/
def affineExactlyOneOutputFamilySourceFinishCfg
    (tail output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneOutputFamilySourceRevProgram :=
  affineExactlyOneOutputFamilySourceCfg .finish (some .frameEnd) none false
    tail output [] [] [] [] []

private def liftOutputFamilyBodyCfg
    (c : BuilderCfg affineExactlyOneOutputSourceRevProgram) :
    BuilderCfg affineExactlyOneOutputFamilySourceRevProgram where
  label := c.label.map .body
  buffer₁ := c.buffer₁
  buffer₂ := c.buffer₂
  test := c.test
  input := c.input
  output := c.output
  work₁ := c.work₁
  work₂ := c.work₂
  counter₁ := c.counter₁
  counter₂ := c.counter₂
  counter₃ := c.counter₃

private theorem outputFamilyRelabel_stepOp
    (op : Op UnaryFrameSym UnaryFrameSym
      AffineExactlyOneOutputSourceLabel)
    (c : BuilderCfg affineExactlyOneOutputSourceRevProgram) :
    stepOp (outputFamilyRelabelOp op) (liftOutputFamilyBodyCfg c) =
      liftOutputFamilyBodyCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [outputFamilyRelabelOp, liftOutputFamilyBodyCfg,
      stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneOutputFamilySource_op_body
    (label : AffineExactlyOneOutputSourceLabel)
    (hexit : label ≠ .finish) :
    affineExactlyOneOutputFamilySourceRevProgram.op (.body label) =
      outputFamilyRelabelOp
        (affineExactlyOneOutputSourceRevProgram.op label) := by
  cases label <;>
    simp_all [affineExactlyOneOutputFamilySourceRevProgram]

private theorem liftOutputFamilyBody_step
    (c : BuilderCfg affineExactlyOneOutputSourceRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineExactlyOneOutputFamilySourceRevProgram
        (liftOutputFamilyBodyCfg c) =
      Option.map liftOutputFamilyBodyCfg
        (step affineExactlyOneOutputSourceRevProgram c) := by
  unfold step
  rw [show (liftOutputFamilyBodyCfg c).label = c.label.map .body by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneOutputFamilySource_op_body label hlabelExit]
      exact congrArg some
        (outputFamilyRelabel_stepOp
          (affineExactlyOneOutputSourceRevProgram.op label) c)

private theorem outputFamily_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem outputFamily_haltExit_no_return
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (hop : P.op exit = .halt) (a b : BuilderCfg P)
    (ha : a.label = some exit) (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (step P a) ≠ some b := by
  intro n
  let halted : BuilderCfg P :=
    { a with label := none, buffer₁ := none, buffer₂ := none, test := false }
  have hstep : step P a = some halted := by
    unfold step
    rw [ha]
    simp [hop, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step P))^[n] (step P halted) ≠ some b
      have hnone : step P halted = none := rfl
      rw [hnone, outputFamily_iterate_bind_none]
      simp

private theorem outputFamily_lift_iterations_to_finish
    {a b : BuilderCfg affineExactlyOneOutputSourceRevProgram}
    (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind
      (step affineExactlyOneOutputSourceRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind
        (step affineExactlyOneOutputFamilySourceRevProgram))^[n]
          (some (liftOutputFamilyBodyCfg a)) =
            some (liftOutputFamilyBodyCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      subst a
      rfl
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind
        (step affineExactlyOneOutputSourceRevProgram))^[n]
          (step affineExactlyOneOutputSourceRevProgram a) = some b at h
      change (flip Option.bind
        (step affineExactlyOneOutputFamilySourceRevProgram))^[n]
          (step affineExactlyOneOutputFamilySourceRevProgram
            (liftOutputFamilyBodyCfg a)) =
              some (liftOutputFamilyBodyCfg b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact outputFamily_haltExit_no_return
          AffineExactlyOneOutputSourceLabel.finish rfl a b ha hb n h
      cases hsource : step affineExactlyOneOutputSourceRevProgram a with
      | none =>
          rw [hsource, outputFamily_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftOutputFamilyBody_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def outputFamily_dispatch_run
    (frame : AffineExactlyOneFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneOutputFamilySourceRevProgram)
      (affineExactlyOneOutputFamilySourceLoopCfg
        (encodeAffineExactlyOneOutputSourceInvocation frame ++ tail) output)
      (some (liftOutputFamilyBodyCfg
        (affineExactlyOneOutputSourceLoopCfg frame tail output))) 4 := by
  rcases frame with ⟨start, rowBase, count⟩
  cases start <;> exact ⟨⟨4, rfl⟩, le_rfl⟩

private def outputFamily_body_run
    (frame : AffineExactlyOneFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneOutputFamilySourceRevProgram)
      (liftOutputFamilyBodyCfg
        (affineExactlyOneOutputSourceLoopCfg frame tail output))
      (some (liftOutputFamilyBodyCfg
        (affineExactlyOneOutputSourceFinishCfg tail
          ((encodeUnaryFrameBlock
            (affineExactlyOneFrameOutputWire frame)).reverse ++ output))))
      (affineExactlyOneOutputSourceSteps frame) := by
  have sourceRun := affineExactlyOneOutputSource_runToFinish frame tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact outputFamily_lift_iterations_to_finish rfl sourceRun.steps
    sourceRun.evals_in_steps

/-- Exact family runtime, including dispatch, loop-back, and outer sentinel. -/
def affineExactlyOneOutputFamilySourceSteps :
    List AffineExactlyOneFrame → Nat
  | [] => 1
  | frame :: rest =>
      4 + affineExactlyOneOutputSourceSteps frame + 1 +
        affineExactlyOneOutputFamilySourceSteps rest

/-- The fixed family controller emits every computed output wire in order,
consumes the outer terminator, and preserves the following invocation. -/
def affineExactlyOneOutputFamilySource_runToFinish
    (frames : List AffineExactlyOneFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneOutputFamilySourceRevProgram)
      (affineExactlyOneOutputFamilySourceLoopCfg
        (encodeAffineExactlyOneOutputSourceInvocationFamily frames ++
          .frameEnd :: tail) output)
      (some (affineExactlyOneOutputFamilySourceFinishCfg tail
        ((affineExactlyOneOutputSourceFamilyStream frames).reverse ++
          output)))
      (affineExactlyOneOutputFamilySourceSteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let restInput :=
        encodeAffineExactlyOneOutputSourceInvocationFamily rest ++
          .frameEnd :: tail
      let headOutput :=
        (encodeUnaryFrameBlock
          (affineExactlyOneFrameOutputWire frame)).reverse ++ output
      let bodyStart := liftOutputFamilyBodyCfg
        (affineExactlyOneOutputSourceLoopCfg frame restInput output)
      let bodyDone := liftOutputFamilyBodyCfg
        (affineExactlyOneOutputSourceFinishCfg restInput headOutput)
      let restStart := affineExactlyOneOutputFamilySourceLoopCfg
        restInput headOutput
      have hdispatch : EvalsToInTime
          (step affineExactlyOneOutputFamilySourceRevProgram)
          (affineExactlyOneOutputFamilySourceLoopCfg
            (encodeAffineExactlyOneOutputSourceInvocation frame ++ restInput)
            output)
          (some bodyStart) 4 := by
        simpa [bodyStart] using outputFamily_dispatch_run frame restInput output
      have hbody : EvalsToInTime
          (step affineExactlyOneOutputFamilySourceRevProgram)
          bodyStart (some bodyDone)
          (affineExactlyOneOutputSourceSteps frame) := by
        simpa [bodyStart, bodyDone, headOutput] using
          outputFamily_body_run frame restInput output
      have hbridge : EvalsToInTime
          (step affineExactlyOneOutputFamilySourceRevProgram)
          bodyDone (some restStart) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hrest := ih headOutput
      let h₁ := EvalsToInTime.trans
        (step affineExactlyOneOutputFamilySourceRevProgram) 4 _ _ bodyStart _
          hdispatch hbody
      let h₂ := EvalsToInTime.trans
        (step affineExactlyOneOutputFamilySourceRevProgram) _ 1 _ bodyDone _
          h₁ hbridge
      let full := EvalsToInTime.trans
        (step affineExactlyOneOutputFamilySourceRevProgram) _ _ _ restStart _
          h₂ hrest
      convert full using 1
      · simp [encodeAffineExactlyOneOutputSourceInvocationFamily,
          restInput, List.append_assoc]
      · simp [affineExactlyOneOutputFamilySourceFinishCfg,
          affineExactlyOneOutputSourceFamilyStream, headOutput,
          encodeUnaryFrame, List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneOutputFamilySourceSteps]
        omega

/-- The family source is quadratic in the complete compact invocation. -/
theorem affineExactlyOneOutputFamilySourceSteps_le
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneOutputFamilySourceSteps frames ≤
      25 *
        ((encodeAffineExactlyOneOutputSourceInvocationFamily frames).length +
          1) ^ 2 := by
  induction frames with
  | nil => simp [affineExactlyOneOutputFamilySourceSteps,
      encodeAffineExactlyOneOutputSourceInvocationFamily]
  | cons frame rest ih =>
      let headLength :=
        (encodeAffineExactlyOneOutputSourceInvocation frame).length
      let tailLength :=
        (encodeAffineExactlyOneOutputSourceInvocationFamily rest).length
      let measure := headLength + tailLength + 1
      have hheadLength : 3 ≤ headLength := by
        simp [headLength, encodeAffineExactlyOneOutputSourceInvocation,
          encodeUnaryFrame_length]
        omega
      have hheadMeasure : headLength ≤ measure := by
        simp [measure]
        omega
      have htailMeasure : tailLength + 1 ≤ measure := by
        simp [measure]
      have hheadSquare := Nat.pow_le_pow_left hheadMeasure 2
      have htailSquare := Nat.pow_le_pow_left htailMeasure 2
      have hhead := affineExactlyOneOutputSourceSteps_le frame
      have hhead' : affineExactlyOneOutputSourceSteps frame ≤
          20 * measure ^ 2 :=
        hhead.trans (Nat.mul_le_mul_left 20 hheadSquare)
      have htail : affineExactlyOneOutputFamilySourceSteps rest ≤
          25 * measure ^ 2 :=
        ih.trans (Nat.mul_le_mul_left 25 htailSquare)
      have hmeasure : measure = headLength + tailLength + 1 := rfl
      simp only [affineExactlyOneOutputFamilySourceSteps,
        encodeAffineExactlyOneOutputSourceInvocationFamily,
        List.flatMap_cons, List.length_append]
      change 4 + affineExactlyOneOutputSourceSteps frame + 1 +
          affineExactlyOneOutputFamilySourceSteps rest ≤
        25 * measure ^ 2
      nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
