import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Stack
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction

/-!
# Continuous stack-family and conjunction serialization

This module links the runtime-length stack-validity family to the final
tail-first conjunction without an intermediate halt.  An explicit outer
`frameEnd` terminates the stack family; one checked cleanup step then enters
the unchanged conjunction controller.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Runtime data for the complete row-validity suffix after halted agreement. -/
structure AffineValidityTailFrame where
  stackFrames : List AffineStackFrame
  finalFrame : AffineConjunctionFrame
deriving DecidableEq, Repr

/-- Delimiter-bearing input owned by the continuous tail controller. -/
def encodeAffineValidityTailFrame
    (frame : AffineValidityTailFrame) : List UnaryFrameSym :=
  encodeAffineStackFamily frame.stackFrames ++
    .frameEnd :: encodeAffineConjunctionFrame frame.finalFrame

/-- Exact forward byte stream of the linked stack and conjunction phases. -/
def affineValidityTailGateStream
    (frame : AffineValidityTailFrame) : List CircuitSym :=
  affineStackFamilyGateStream frame.stackFrames ++
    affineConjunctionGateStream frame.finalFrame

/-- Disjoint finite-control phases of the linked tail controller. -/
inductive AffineValidityTailLabel
  | stack (label : AffineStackLabel)
  | conjunction (label : AffineConjunctionLabel)
  | invalid
deriving DecidableEq, Fintype

private def liftStackOp :
    Op UnaryFrameSym CircuitSym AffineStackLabel →
      Op UnaryFrameSym CircuitSym AffineValidityTailLabel
  | .pushOutput symbol next => .pushOutput symbol (.stack next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.stack next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.stack next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.stack nextEmpty) (fun symbol => .stack (nextMoved symbol))
  | .inc₁ next => .inc₁ (.stack next)
  | .inc₂ next => .inc₂ (.stack next)
  | .inc₃ next => .inc₃ (.stack next)
  | .dec₁ nextZero nextSucc => .dec₁ (.stack nextZero) (.stack nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.stack nextZero) (.stack nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.stack nextZero) (.stack nextSucc)
  | .jump next => .jump (.stack next)
  | .halt => .halt

private def liftConjunctionOp :
    Op UnaryFrameSym CircuitSym AffineConjunctionLabel →
      Op UnaryFrameSym CircuitSym AffineValidityTailLabel
  | .pushOutput symbol next => .pushOutput symbol (.conjunction next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.conjunction next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.conjunction next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.conjunction nextEmpty)
        (fun symbol => .conjunction (nextMoved symbol))
  | .inc₁ next => .inc₁ (.conjunction next)
  | .inc₂ next => .inc₂ (.conjunction next)
  | .inc₃ next => .inc₃ (.conjunction next)
  | .dec₁ nextZero nextSucc =>
      .dec₁ (.conjunction nextZero) (.conjunction nextSucc)
  | .dec₂ nextZero nextSucc =>
      .dec₂ (.conjunction nextZero) (.conjunction nextSucc)
  | .dec₃ nextZero nextSucc =>
      .dec₃ (.conjunction nextZero) (.conjunction nextSucc)
  | .jump next => .jump (.conjunction next)
  | .halt => .halt

/-- One fixed controller for every runtime stack family and final conjunction.
The successful stack exit is the only redirected operation. -/
def affineValidityTailRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineValidityTailLabel
  main := .stack affineStackRevProgram.main
  op
    | .stack .finish =>
        .popWork₁ (.conjunction affineConjunctionRevProgram.main)
          (fun _ => .invalid)
    | .stack label => liftStackOp (affineStackRevProgram.op label)
    | .conjunction label =>
        liftConjunctionOp (affineConjunctionRevProgram.op label)
    | .invalid => .halt

/-- Fieldwise configuration surface for the linked controller. -/
def affineValidityTailCfg (label : AffineValidityTailLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineValidityTailRevProgram where
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

/-- Clean public entry for the linked runtime frame. -/
def affineValidityTailLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineValidityTailRevProgram :=
  affineValidityTailCfg affineValidityTailRevProgram.main none none false
    input output [] [] [] [] []

private def liftStackCfg (c : BuilderCfg affineStackRevProgram) :
    BuilderCfg affineValidityTailRevProgram where
  label := c.label.map .stack
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

private def liftConjunctionCfg
    (c : BuilderCfg affineConjunctionRevProgram) :
    BuilderCfg affineValidityTailRevProgram where
  label := c.label.map .conjunction
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

private theorem liftStack_stepOp
    (op : Op UnaryFrameSym CircuitSym AffineStackLabel)
    (c : BuilderCfg affineStackRevProgram) :
    stepOp (liftStackOp op) (liftStackCfg c) =
      liftStackCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [liftStackOp, liftStackCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineValidityTail_op_stack
    (label : AffineStackLabel) (hexit : label ≠ .finish) :
    affineValidityTailRevProgram.op (.stack label) =
      liftStackOp (affineStackRevProgram.op label) := by
  cases label <;> simp_all [affineValidityTailRevProgram]

private theorem liftStack_step (c : BuilderCfg affineStackRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineValidityTailRevProgram (liftStackCfg c) =
      Option.map liftStackCfg (step affineStackRevProgram c) := by
  unfold step
  rw [show (liftStackCfg c).label = c.label.map .stack by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineValidityTail_op_stack label hlabelExit]
      change some (stepOp
          (liftStackOp (affineStackRevProgram.op label))
          (liftStackCfg c)) =
        some (liftStackCfg
          (stepOp (affineStackRevProgram.op label) c))
      exact congrArg some
        (liftStack_stepOp (affineStackRevProgram.op label) c)

private theorem liftConjunction_stepOp
    (op : Op UnaryFrameSym CircuitSym AffineConjunctionLabel)
    (c : BuilderCfg affineConjunctionRevProgram) :
    stepOp (liftConjunctionOp op) (liftConjunctionCfg c) =
      liftConjunctionCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [liftConjunctionOp, liftConjunctionCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem liftConjunction_step
    (c : BuilderCfg affineConjunctionRevProgram) :
    step affineValidityTailRevProgram (liftConjunctionCfg c) =
      Option.map liftConjunctionCfg
        (step affineConjunctionRevProgram c) := by
  unfold step
  rw [show (liftConjunctionCfg c).label =
      c.label.map .conjunction by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      change some (stepOp
          (liftConjunctionOp (affineConjunctionRevProgram.op label))
          (liftConjunctionCfg c)) =
        some (liftConjunctionCfg
          (stepOp (affineConjunctionRevProgram.op label) c))
      exact congrArg some
        (liftConjunction_stepOp (affineConjunctionRevProgram.op label) c)

private theorem conjunction_iterate_bind_none (n : Nat) :
    (flip Option.bind (step affineConjunctionRevProgram))^[n]
      (none : Option (BuilderCfg affineConjunctionRevProgram)) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem liftConjunction_iterations
    {a b : BuilderCfg affineConjunctionRevProgram} : ∀ n : Nat,
    (flip Option.bind (step affineConjunctionRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineValidityTailRevProgram))^[n]
        (some (liftConjunctionCfg a)) = some (liftConjunctionCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change
        (flip Option.bind (step affineConjunctionRevProgram))^[n]
          (step affineConjunctionRevProgram a) = some b at h
      change
        (flip Option.bind (step affineValidityTailRevProgram))^[n]
          (step affineValidityTailRevProgram (liftConjunctionCfg a)) =
            some (liftConjunctionCfg b)
      cases hstep : step affineConjunctionRevProgram a with
      | none =>
          rw [hstep, conjunction_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftConjunction_step a
          rw [hstep] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hstep] at h
          exact ih h

private theorem stack_iterate_bind_none (n : Nat) :
    (flip Option.bind (step affineStackRevProgram))^[n]
      (none : Option (BuilderCfg affineStackRevProgram)) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem stack_finish_no_return
    (a b : BuilderCfg affineStackRevProgram)
    (ha : a.label = some .finish) (hb : b.label = some .finish)
    (n : Nat) :
    (flip Option.bind (step affineStackRevProgram))^[n]
        (step affineStackRevProgram a) ≠ some b := by
  rcases a with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at ha
  subst label
  let halted : BuilderCfg affineStackRevProgram := {
    label := none
    buffer₁ := none
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := work₁
    work₂ := work₂
    counter₁ := counter₁
    counter₂ := counter₂
    counter₃ := counter₃ }
  have hstep : step affineStackRevProgram
      { label := some AffineStackLabel.finish
        buffer₁ := buffer₁, buffer₂ := buffer₂, test := test
        input := input, output := output, work₁ := work₁, work₂ := work₂
        counter₁ := counter₁, counter₂ := counter₂,
        counter₃ := counter₃ } = some halted := rfl
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineStackRevProgram))^[n]
          (step affineStackRevProgram halted) ≠ some b
      have hnone : step affineStackRevProgram halted = none := rfl
      rw [hnone, stack_iterate_bind_none]
      simp

private theorem liftStack_iterations_to_finish
    {a b : BuilderCfg affineStackRevProgram}
    (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind (step affineStackRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineValidityTailRevProgram))^[n]
        (some (liftStackCfg a)) = some (liftStackCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change
        (flip Option.bind (step affineStackRevProgram))^[n]
          (step affineStackRevProgram a) = some b at h
      change
        (flip Option.bind (step affineValidityTailRevProgram))^[n]
          (step affineValidityTailRevProgram (liftStackCfg a)) =
            some (liftStackCfg b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact stack_finish_no_return a b ha hb n h
      cases hstep : step affineStackRevProgram a with
      | none =>
          rw [hstep, stack_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftStack_step a haexit
          rw [hstep] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hstep] at h
          exact ih h

private def affineValidityTail_stack_runToFinish
    (frame : AffineValidityTailFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityTailRevProgram)
      (affineValidityTailLoopCfg
        (encodeAffineValidityTailFrame frame ++ tail) output)
      (some (liftStackCfg (affineStackFamilyTerminatorCfg
        (encodeAffineConjunctionFrame frame.finalFrame ++ tail)
        ((affineStackFamilyGateStream frame.stackFrames).reverse ++ output))))
      (affineStackFamilyUntilTerminatorSteps frame.stackFrames) := by
  have sourceRun := affineStackFamily_runToTerminator frame.stackFrames
    (encodeAffineConjunctionFrame frame.finalFrame ++ tail) output
  have htarget : (affineStackFamilyTerminatorCfg
      (encodeAffineConjunctionFrame frame.finalFrame ++ tail)
      ((affineStackFamilyGateStream frame.stackFrames).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have lifted := liftStack_iterations_to_finish htarget sourceRun.steps
    sourceRun.evals_in_steps
  have hsourceLift : liftStackCfg (affineStackLoopCfg
      (encodeAffineStackFamily frame.stackFrames ++
        .frameEnd :: (encodeAffineConjunctionFrame frame.finalFrame ++ tail))
      output) =
      affineValidityTailLoopCfg
        (encodeAffineValidityTailFrame frame ++ tail) output := by
    simp [liftStackCfg, affineStackLoopCfg, affineStackCfg,
      affineStackRevProgram, affineValidityTailLoopCfg,
      affineValidityTailCfg, affineValidityTailRevProgram,
      encodeAffineValidityTailFrame, List.append_assoc]
  rw [hsourceLift] at lifted
  exact lifted

private def affineValidityTail_bridge
    (frame : AffineValidityTailFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityTailRevProgram)
      (liftStackCfg (affineStackFamilyTerminatorCfg
        (encodeAffineConjunctionFrame frame.finalFrame ++ tail) output))
      (some (liftConjunctionCfg (affineConjunctionLoopCfg
        (encodeAffineConjunctionFrame frame.finalFrame ++ tail) output))) 1 :=
  ⟨⟨1, rfl⟩, le_rfl⟩

private def affineValidityTail_conjunction_runToFinish
    (frame : AffineConjunctionFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityTailRevProgram)
      (liftConjunctionCfg (affineConjunctionLoopCfg
        (encodeAffineConjunctionFrame frame ++ tail) output))
      (some (liftConjunctionCfg (affineConjunctionFinishCfg tail
        ((affineConjunctionGateStream frame).reverse ++ output))))
      (affineConjunctionUntilFinishSteps frame) := by
  have sourceRun := affineConjunction_runToFinish frame tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact liftConjunction_iterations sourceRun.steps sourceRun.evals_in_steps

/-- Redirectable clean exit after the full validity suffix. -/
def affineValidityTailFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineValidityTailRevProgram :=
  liftConjunctionCfg (affineConjunctionFinishCfg tail output)

/-- Exact contextual runtime through the redirectable tail finish label. -/
def affineValidityTailUntilFinishSteps
    (frame : AffineValidityTailFrame) : Nat :=
  affineStackFamilyUntilTerminatorSteps frame.stackFrames + 1 +
    affineConjunctionUntilFinishSteps frame.finalFrame

/-- Execute the full suffix, preserve an arbitrary unconsumed input tail,
and stop before the final halt instruction. -/
def affineValidityTail_runToFinish (frame : AffineValidityTailFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineValidityTailRevProgram)
      (affineValidityTailLoopCfg
        (encodeAffineValidityTailFrame frame ++ tail) output)
      (some (affineValidityTailFinishCfg tail
        ((affineValidityTailGateStream frame).reverse ++ output)))
      (affineValidityTailUntilFinishSteps frame) := by
  let stackOutput :=
    (affineStackFamilyGateStream frame.stackFrames).reverse ++ output
  have hstack := affineValidityTail_stack_runToFinish frame tail output
  have hbridge := affineValidityTail_bridge frame tail stackOutput
  have hconjunction := affineValidityTail_conjunction_runToFinish
    frame.finalFrame tail stackOutput
  let t₁ := EvalsToInTime.trans (step affineValidityTailRevProgram)
    (affineStackFamilyUntilTerminatorSteps frame.stackFrames) 1
    _ (liftStackCfg (affineStackFamilyTerminatorCfg
      (encodeAffineConjunctionFrame frame.finalFrame ++ tail) stackOutput))
    _ hstack hbridge
  let full := EvalsToInTime.trans (step affineValidityTailRevProgram)
    _ (affineConjunctionUntilFinishSteps frame.finalFrame)
    _ (liftConjunctionCfg (affineConjunctionLoopCfg
      (encodeAffineConjunctionFrame frame.finalFrame ++ tail) stackOutput))
    _ t₁ hconjunction
  convert full using 1
  · simp [affineValidityTailFinishCfg, affineValidityTailGateStream, stackOutput,
      List.reverse_append, List.append_assoc]
  · unfold affineValidityTailUntilFinishSteps
    omega

/-- Exact runtime of the continuous stack-family/conjunction controller. -/
def affineValidityTailRevSteps (frame : AffineValidityTailFrame) : Nat :=
  affineValidityTailUntilFinishSteps frame + 1

/-- Execute the complete post-halted row-validity suffix with no halt between
the stack family and final conjunction. -/
def affineValidityTail_run (frame : AffineValidityTailFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityTailRevProgram)
      (affineValidityTailLoopCfg
        (encodeAffineValidityTailFrame frame) output)
      (some (haltCfg affineValidityTailRevProgram
        ((affineValidityTailGateStream frame).reverse ++ output)))
      (affineValidityTailRevSteps frame) := by
  let gateOutput := (affineValidityTailGateStream frame).reverse ++ output
  have hfinish := affineValidityTail_runToFinish frame [] output
  have hhalt : EvalsToInTime (step affineValidityTailRevProgram)
      (affineValidityTailFinishCfg [] gateOutput)
      (some (haltCfg affineValidityTailRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineValidityTailRevProgram)
    (affineValidityTailUntilFinishSteps frame) 1
    _ (affineValidityTailFinishCfg [] gateOutput) _ hfinish hhalt
  convert full using 1
  · simp [gateOutput]
  · simp [affineValidityTailRevSteps, Nat.add_comm]

/-- The linked runtime is quadratic in the exact delimiter-bearing frame. -/
theorem affineValidityTailRev_steps_le
    (frame : AffineValidityTailFrame) :
    affineValidityTailRevSteps frame ≤
      1400 * (encodeAffineValidityTailFrame frame).length ^ 2 + 5 := by
  have hstack := affineStackFamilyUntilTerminatorSteps_le frame.stackFrames
  have hconjunction := affineConjunctionRev_steps_le frame.finalFrame
  have hstackLen : (encodeAffineStackFamily frame.stackFrames).length ≤
      (encodeAffineValidityTailFrame frame).length := by
    simp [encodeAffineValidityTailFrame]
  have hconjunctionLen :
      (encodeAffineConjunctionFrame frame.finalFrame).length ≤
        (encodeAffineValidityTailFrame frame).length := by
    simp [encodeAffineValidityTailFrame]
    omega
  have hstackSq := Nat.pow_le_pow_left hstackLen 2
  have hconjunctionSq := Nat.pow_le_pow_left hconjunctionLen 2
  have hstackScaled := Nat.mul_le_mul_left 400 hstackSq
  have hconjunctionScaled := Nat.mul_le_mul_left 1000 hconjunctionSq
  change affineStackFamilyUntilTerminatorSteps frame.stackFrames + 1 +
      affineConjunctionRevSteps frame.finalFrame ≤
    1400 * (encodeAffineValidityTailFrame frame).length ^ 2 + 5
  omega

end CLRS.Chapter34.Turing.PolyBuilder
