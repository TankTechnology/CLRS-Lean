import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneOutputFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineStackOutputFamilySource
import Mathlib.Tactic

/-!
# Runtime source for a validity row's final conjunction

This controller links the already verified exactly-one-output and stack-output
sources without an intermediate halt.  Its input contains only the compact
runtime operands; the emitted stream is precisely the reverse serialization
of the final conjunction frame.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Runtime operands for the final conjunction of one validity row. -/
structure AffineValidityFinalConjunctionSourceFrame where
  rawFrames : List AffineExactlyOneFrame
  haltedWire : Nat
  stackFrame : AffineStackOutputSourceFrame
  finalStart : Nat
deriving DecidableEq, Repr

/-- Public source wires, in the same order as the semantic conjunction. -/
def affineValidityFinalConjunctionWires (stackCount : Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame) : List Nat :=
  frame.rawFrames.map affineExactlyOneFrameOutputWire ++
    frame.haltedWire ::
      affineStackOutputWires stackCount
        frame.stackFrame.height frame.stackFrame.base

/-- The exact conjunction frame emitted by the linked source. -/
def affineValidityFinalConjunctionFrame (stackCount : Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame) :
    AffineConjunctionFrame :=
  { start := frame.finalStart
    wires := affineValidityFinalConjunctionWires stackCount frame }

/-- Compact operands in their consumption order.  The final `frameEnd`
terminates the exactly-one-output family. -/
def encodeAffineValidityFinalConjunctionSourceInvocation
    (frame : AffineValidityFinalConjunctionSourceFrame) :
    List UnaryFrameSym :=
  encodeUnaryFrameBlock frame.finalStart ++
    encodeAffineStackOutputSourceInvocation frame.stackFrame ++
    encodeUnaryFrameBlock frame.haltedWire ++
    encodeAffineExactlyOneOutputSourceInvocationFamily
      frame.rawFrames.reverse ++
    [.frameEnd]

/-- The two component phases plus two delimiter-preserving unary echoes. -/
inductive AffineValidityFinalConjunctionSourceLabel (stackCount : Nat)
  | startLoad | startPushTick | startClearTick
  | startPushSeparator | startClear
  | stack (label : AffineStackOutputFamilySourceLabel stackCount)
  | haltedLoad | haltedPushTick | haltedClearTick
  | haltedPushSeparator | haltedClear
  | outputs (label : AffineExactlyOneOutputFamilySourceLabel)
  | finish | invalid
deriving DecidableEq, Fintype

private def finalConjunctionRelabelOp {Γ Δ Λ Μ : Type}
    (tag : Λ → Μ) : Op Γ Δ Λ → Op Γ Δ Μ
  | .pushOutput symbol next => .pushOutput symbol (tag next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (tag next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (tag next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .inc₁ next => .inc₁ (tag next)
  | .inc₂ next => .inc₂ (tag next)
  | .inc₃ next => .inc₃ (tag next)
  | .dec₁ nextZero nextSucc => .dec₁ (tag nextZero) (tag nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (tag nextZero) (tag nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (tag nextZero) (tag nextSucc)
  | .jump next => .jump (tag next)
  | .halt => .halt

/-- One fixed linked controller for a fixed verifier stack count. -/
def affineValidityFinalConjunctionSourceRevProgram (stackCount : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineValidityFinalConjunctionSourceLabel stackCount
  main := .startLoad
  op
    | .startLoad => .popInput .invalid fun
        | .tick => .startPushTick
        | .separator => .startPushSeparator
        | .frameEnd => .invalid
    | .startPushTick => .pushOutput .tick .startClearTick
    | .startClearTick => .popWork₁ .startLoad (fun _ => .invalid)
    | .startPushSeparator => .pushOutput .separator .startClear
    | .startClear => .popWork₁
        (.stack (affineStackOutputFamilySourceRevProgram stackCount).main)
        (fun _ => .invalid)
    | .stack .finish => .jump .haltedLoad
    | .stack label => finalConjunctionRelabelOp .stack
        ((affineStackOutputFamilySourceRevProgram stackCount).op label)
    | .haltedLoad => .popInput .invalid fun
        | .tick => .haltedPushTick
        | .separator => .haltedPushSeparator
        | .frameEnd => .invalid
    | .haltedPushTick => .pushOutput .tick .haltedClearTick
    | .haltedClearTick => .popWork₁ .haltedLoad (fun _ => .invalid)
    | .haltedPushSeparator => .pushOutput .separator .haltedClear
    | .haltedClear => .popWork₁
        (.outputs affineExactlyOneOutputFamilySourceRevProgram.main)
        (fun _ => .invalid)
    | .outputs .finish => .pushOutput .frameEnd .finish
    | .outputs label => finalConjunctionRelabelOp .outputs
        (affineExactlyOneOutputFamilySourceRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

private def affineValidityFinalConjunctionSourceCfg {stackCount : Nat}
    (label : AffineValidityFinalConjunctionSourceLabel stackCount)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineValidityFinalConjunctionSourceRevProgram stackCount) where
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

/-- Clean entry of the linked source. -/
def affineValidityFinalConjunctionSourceLoopCfg (stackCount : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineValidityFinalConjunctionSourceRevProgram stackCount) :=
  affineValidityFinalConjunctionSourceCfg .startLoad none none false
    input output [] [] [] [] []

/-- Clean public exit after the emitted `frameEnd`. -/
def affineValidityFinalConjunctionSourceFinishCfg (stackCount : Nat)
    (tail output : List UnaryFrameSym) :
    BuilderCfg (affineValidityFinalConjunctionSourceRevProgram stackCount) :=
  affineValidityFinalConjunctionSourceCfg .finish (some .frameEnd) none false
    tail output [] [] [] [] []

private def finalConjunctionRelabelCfg {stackCount : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → AffineValidityFinalConjunctionSourceLabel stackCount)
    (c : BuilderCfg P) :
    BuilderCfg (affineValidityFinalConjunctionSourceRevProgram stackCount) where
  label := c.label.map tag
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

private theorem finalConjunctionRelabel_stepOp {stackCount : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → AffineValidityFinalConjunctionSourceLabel stackCount)
    (op : Op UnaryFrameSym UnaryFrameSym P.Label) (c : BuilderCfg P) :
    stepOp (finalConjunctionRelabelOp tag op)
        (finalConjunctionRelabelCfg tag c) =
      finalConjunctionRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [finalConjunctionRelabelOp, finalConjunctionRelabelCfg,
      stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineValidityFinalConjunctionSource_op_stack
    (stackCount : Nat)
    (label : AffineStackOutputFamilySourceLabel stackCount)
    (hexit : label ≠ .finish) :
    (affineValidityFinalConjunctionSourceRevProgram stackCount).op
        (.stack label) =
      finalConjunctionRelabelOp .stack
        ((affineStackOutputFamilySourceRevProgram stackCount).op label) := by
  cases label <;>
    simp_all [affineValidityFinalConjunctionSourceRevProgram] <;> rfl

private theorem affineValidityFinalConjunctionSource_op_outputs
    (stackCount : Nat)
    (label : AffineExactlyOneOutputFamilySourceLabel)
    (hexit : label ≠ .finish) :
    (affineValidityFinalConjunctionSourceRevProgram stackCount).op
        (.outputs label) =
      finalConjunctionRelabelOp .outputs
        (affineExactlyOneOutputFamilySourceRevProgram.op label) := by
  cases label <;>
    simp_all [affineValidityFinalConjunctionSourceRevProgram] <;> rfl

private theorem finalConjunction_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem finalConjunction_haltExit_no_return
    {P : Program UnaryFrameSym UnaryFrameSym}
    (exit : P.Label) (hop : P.op exit = .halt)
    (a b : BuilderCfg P) (ha : a.label = some exit)
    (hb : b.label = some exit) : ∀ n : Nat,
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
      rw [hnone, finalConjunction_iterate_bind_none]
      simp

private theorem finalConjunction_lift_step {stackCount : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (tag : P.Label → AffineValidityFinalConjunctionSourceLabel stackCount)
    (hopOuter : ∀ label, label ≠ exit →
      (affineValidityFinalConjunctionSourceRevProgram stackCount).op
          (tag label) = finalConjunctionRelabelOp tag (P.op label))
    (c : BuilderCfg P) (hexit : c.label ≠ some exit) :
    step (affineValidityFinalConjunctionSourceRevProgram stackCount)
        (finalConjunctionRelabelCfg tag c) =
      Option.map (finalConjunctionRelabelCfg tag) (step P c) := by
  unfold step
  rw [show (finalConjunctionRelabelCfg tag c).label = c.label.map tag by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ exit := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [hopOuter label hlabelExit]
      exact congrArg some
        (finalConjunctionRelabel_stepOp tag (P.op label) c)

private theorem finalConjunction_lift_iterations {stackCount : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tag : P.Label → AffineValidityFinalConjunctionSourceLabel stackCount)
    (hopOuter : ∀ label, label ≠ exit →
      (affineValidityFinalConjunctionSourceRevProgram stackCount).op
          (tag label) = finalConjunctionRelabelOp tag (P.op label))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineValidityFinalConjunctionSourceRevProgram stackCount)))^[n]
          (some (finalConjunctionRelabelCfg tag a)) =
            some (finalConjunctionRelabelCfg tag b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step P))^[n] (step P a) = some b at h
      change (flip Option.bind
        (step (affineValidityFinalConjunctionSourceRevProgram stackCount)))^[n]
          (step (affineValidityFinalConjunctionSourceRevProgram stackCount)
            (finalConjunctionRelabelCfg tag a)) =
            some (finalConjunctionRelabelCfg tag b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact finalConjunction_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, finalConjunction_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := finalConjunction_lift_step exit tag hopOuter a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem affineValidityFinalConjunctionSource_start_tick
    (stackCount : Nat) (input output : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount)))^[3]
        (some (affineValidityFinalConjunctionSourceLoopCfg stackCount
          (.tick :: input) output)) =
      some (affineValidityFinalConjunctionSourceLoopCfg stackCount input
        (.tick :: output)) := by
  rfl

private def affineValidityFinalConjunctionSource_start_run
    (stackCount value : Nat) (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
      (affineValidityFinalConjunctionSourceLoopCfg stackCount
        (encodeUnaryFrameBlock value ++ tail) output)
      (some (finalConjunctionRelabelCfg .stack
        (affineStackOutputFamilySourceLoopCfg stackCount tail
          ((encodeUnaryFrameBlock value).reverse ++ output))))
      (3 * value + 3) := by
  induction value generalizing output with
  | zero => exact ⟨⟨3, rfl⟩, le_rfl⟩
  | succ value ih =>
      let next := affineValidityFinalConjunctionSourceLoopCfg stackCount
        (encodeUnaryFrameBlock value ++ tail) (.tick :: output)
      have hhead : EvalsToInTime
          (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
          (affineValidityFinalConjunctionSourceLoopCfg stackCount
            (encodeUnaryFrameBlock (value + 1) ++ tail) output)
          (some next) 3 := by
        refine ⟨⟨3, ?_⟩, le_rfl⟩
        simpa [next, encodeUnaryFrameBlock, List.replicate_succ] using
          affineValidityFinalConjunctionSource_start_tick stackCount
            (encodeUnaryFrameBlock value ++ tail) output
      have hrest := ih (.tick :: output)
      let full := EvalsToInTime.trans
        (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
        3 (3 * value + 3) _ next _ hhead hrest
      convert full using 1
      · simp [encodeUnaryFrameBlock, List.replicate_succ]
      · simp [encodeUnaryFrameBlock, List.replicate_succ,
          List.reverse_append, List.append_assoc] <;> omega

private def affineValidityFinalConjunctionSource_stack_run
    (stackCount : Nat) (frame : AffineStackOutputSourceFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
      (finalConjunctionRelabelCfg .stack
        (affineStackOutputFamilySourceLoopCfg stackCount
          (encodeAffineStackOutputSourceInvocation frame ++ tail) output))
      (some (finalConjunctionRelabelCfg .stack
        (affineStackOutputFamilySourceFinishCfg stackCount tail
          ((encodeAffineConjunctionSources
            (affineStackOutputWires stackCount frame.height frame.base).reverse
              ).reverse ++ output))))
      (affineStackOutputFamilySourceSteps stackCount frame) := by
  have sourceRun :=
    affineStackOutputFamilySource_runToFinish stackCount frame tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact finalConjunction_lift_iterations
    (AffineStackOutputFamilySourceLabel.finish) rfl .stack
    (affineValidityFinalConjunctionSource_op_stack stackCount)
    rfl sourceRun.steps sourceRun.evals_in_steps

private def affineValidityFinalConjunctionSource_haltedLoopCfg
    (stackCount : Nat) (input output : List UnaryFrameSym) :
    BuilderCfg (affineValidityFinalConjunctionSourceRevProgram stackCount) :=
  affineValidityFinalConjunctionSourceCfg .haltedLoad none none false
    input output [] [] [] [] []

private theorem affineValidityFinalConjunctionSource_halted_tick
    (stackCount : Nat) (input output : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount)))^[3]
        (some (affineValidityFinalConjunctionSource_haltedLoopCfg stackCount
          (.tick :: input) output)) =
      some (affineValidityFinalConjunctionSource_haltedLoopCfg stackCount input
        (.tick :: output)) := by
  rfl

private def affineValidityFinalConjunctionSource_halted_run
    (stackCount value : Nat) (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
      (affineValidityFinalConjunctionSource_haltedLoopCfg stackCount
        (encodeUnaryFrameBlock value ++ tail) output)
      (some (finalConjunctionRelabelCfg .outputs
        (affineExactlyOneOutputFamilySourceLoopCfg tail
          ((encodeUnaryFrameBlock value).reverse ++ output))))
      (3 * value + 3) := by
  induction value generalizing output with
  | zero => exact ⟨⟨3, rfl⟩, le_rfl⟩
  | succ value ih =>
      let next := affineValidityFinalConjunctionSource_haltedLoopCfg stackCount
        (encodeUnaryFrameBlock value ++ tail) (.tick :: output)
      have hhead : EvalsToInTime
          (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
          (affineValidityFinalConjunctionSource_haltedLoopCfg stackCount
            (encodeUnaryFrameBlock (value + 1) ++ tail) output)
          (some next) 3 := by
        refine ⟨⟨3, ?_⟩, le_rfl⟩
        simpa [next, encodeUnaryFrameBlock, List.replicate_succ] using
          affineValidityFinalConjunctionSource_halted_tick stackCount
            (encodeUnaryFrameBlock value ++ tail) output
      have hrest := ih (.tick :: output)
      let full := EvalsToInTime.trans
        (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
        3 (3 * value + 3) _ next _ hhead hrest
      convert full using 1
      · simp [encodeUnaryFrameBlock, List.replicate_succ]
      · simp [encodeUnaryFrameBlock, List.replicate_succ,
          List.reverse_append, List.append_assoc] <;> omega

private def affineValidityFinalConjunctionSource_outputs_run
    (stackCount : Nat) (frames : List AffineExactlyOneFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
      (finalConjunctionRelabelCfg .outputs
        (affineExactlyOneOutputFamilySourceLoopCfg
          (encodeAffineExactlyOneOutputSourceInvocationFamily frames ++
            .frameEnd :: tail) output))
      (some (finalConjunctionRelabelCfg .outputs
        (affineExactlyOneOutputFamilySourceFinishCfg tail
          ((affineExactlyOneOutputSourceFamilyStream frames).reverse ++
            output))))
      (affineExactlyOneOutputFamilySourceSteps frames) := by
  have sourceRun :=
    affineExactlyOneOutputFamilySource_runToFinish frames tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact finalConjunction_lift_iterations
    AffineExactlyOneOutputFamilySourceLabel.finish rfl .outputs
    (affineValidityFinalConjunctionSource_op_outputs stackCount)
    rfl sourceRun.steps sourceRun.evals_in_steps

/-- Exact runtime of the linked final-conjunction source. -/
def affineValidityFinalConjunctionSourceSteps (stackCount : Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame) : Nat :=
  (3 * frame.finalStart + 3) +
    affineStackOutputFamilySourceSteps stackCount frame.stackFrame + 1 +
    (3 * frame.haltedWire + 3) +
    affineExactlyOneOutputFamilySourceSteps frame.rawFrames.reverse + 1

/-- The linked machine emits exactly the reverse of the public conjunction
frame and preserves the following invocation. -/
def affineValidityFinalConjunctionSource_runToFinish
    (stackCount : Nat) (frame : AffineValidityFinalConjunctionSourceFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
      (affineValidityFinalConjunctionSourceLoopCfg stackCount
        (encodeAffineValidityFinalConjunctionSourceInvocation frame ++ tail)
        output)
      (some (affineValidityFinalConjunctionSourceFinishCfg stackCount tail
        ((encodeAffineConjunctionFrame
          (affineValidityFinalConjunctionFrame stackCount frame)).reverse ++
            output)))
      (affineValidityFinalConjunctionSourceSteps stackCount frame) := by
  let outputFrames := frame.rawFrames.reverse
  let outputInput :=
    encodeAffineExactlyOneOutputSourceInvocationFamily outputFrames ++
      .frameEnd :: tail
  let haltedInput := encodeUnaryFrameBlock frame.haltedWire ++ outputInput
  let stackInput :=
    encodeAffineStackOutputSourceInvocation frame.stackFrame ++ haltedInput
  let startOutput :=
    (encodeUnaryFrameBlock frame.finalStart).reverse ++ output
  let stackOutput :=
    (encodeAffineConjunctionSources
      (affineStackOutputWires stackCount frame.stackFrame.height
        frame.stackFrame.base).reverse).reverse ++ startOutput
  let haltedOutput :=
    (encodeUnaryFrameBlock frame.haltedWire).reverse ++ stackOutput
  let familyOutput :=
    (affineExactlyOneOutputSourceFamilyStream outputFrames).reverse ++
      haltedOutput
  have hstart := affineValidityFinalConjunctionSource_start_run
    stackCount frame.finalStart stackInput output
  have hstack := affineValidityFinalConjunctionSource_stack_run
    stackCount frame.stackFrame haltedInput startOutput
  have hstackBridge : EvalsToInTime
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
      (finalConjunctionRelabelCfg .stack
        (affineStackOutputFamilySourceFinishCfg stackCount haltedInput
          stackOutput))
      (some (affineValidityFinalConjunctionSource_haltedLoopCfg stackCount
        haltedInput stackOutput)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hhalted := affineValidityFinalConjunctionSource_halted_run
    stackCount frame.haltedWire outputInput stackOutput
  have houtputs := affineValidityFinalConjunctionSource_outputs_run
    stackCount outputFrames tail haltedOutput
  have hfinish : EvalsToInTime
      (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
      (finalConjunctionRelabelCfg .outputs
        (affineExactlyOneOutputFamilySourceFinishCfg tail familyOutput))
      (some (affineValidityFinalConjunctionSourceFinishCfg stackCount tail
        (.frameEnd :: familyOutput))) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
    (3 * frame.finalStart + 3)
    (affineStackOutputFamilySourceSteps stackCount frame.stackFrame)
    _ _ _ hstart hstack
  let h₂ := EvalsToInTime.trans
    (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
    _ 1 _ _ _ h₁ hstackBridge
  let h₃ := EvalsToInTime.trans
    (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
    _ (3 * frame.haltedWire + 3) _ _ _ h₂ hhalted
  let h₄ := EvalsToInTime.trans
    (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
    _ (affineExactlyOneOutputFamilySourceSteps outputFrames)
    _ _ _ h₃ houtputs
  let full := EvalsToInTime.trans
    (step (affineValidityFinalConjunctionSourceRevProgram stackCount))
    _ 1 _ _ _ h₄ hfinish
  convert full using 1
  · simp [encodeAffineValidityFinalConjunctionSourceInvocation,
      stackInput, haltedInput, outputInput, outputFrames,
      List.append_assoc]
  · simp [affineValidityFinalConjunctionFrame,
      affineValidityFinalConjunctionWires, encodeAffineConjunctionFrame,
      encodeAffineConjunctionSources,
      affineExactlyOneOutputSourceFamilyStream, encodeUnaryFrame,
      outputFrames, familyOutput, haltedOutput, stackOutput, startOutput,
      List.reverse_append, List.append_assoc]
  · simp [affineValidityFinalConjunctionSourceSteps, outputFrames]
    omega

/-- A verifier-dependent coefficient for the uniform quadratic bound. -/
def affineValidityFinalConjunctionSourceStepCoeff
    (stackCount : Nat) : Nat :=
  1000 * (stackCount + 1) ^ 2 + 500

/-- The complete linked source is quadratic in its compact invocation. -/
theorem affineValidityFinalConjunctionSource_steps_le
    (stackCount : Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame) :
    affineValidityFinalConjunctionSourceSteps stackCount frame ≤
      affineValidityFinalConjunctionSourceStepCoeff stackCount *
        (encodeAffineValidityFinalConjunctionSourceInvocation frame).length ^
          2 + 50 := by
  let n :=
    (encodeAffineValidityFinalConjunctionSourceInvocation frame).length
  let a := (stackCount + 1) ^ 2
  have hn : 1 ≤ n := by
    simp [n, encodeAffineValidityFinalConjunctionSourceInvocation,
      encodeUnaryFrameBlock]
    omega
  have hnSquare : n ≤ n ^ 2 := by
    nlinarith
  have honeSquare : 1 ≤ n ^ 2 := le_trans hn hnSquare
  have hstart : frame.finalStart ≤ n := by
    simp [n, encodeAffineValidityFinalConjunctionSourceInvocation,
      encodeUnaryFrameBlock]
  have hhalted : frame.haltedWire ≤ n := by
    simp [n, encodeAffineValidityFinalConjunctionSourceInvocation,
      encodeUnaryFrameBlock]
    omega
  have hstackLength :
      (encodeAffineStackOutputSourceInvocation frame.stackFrame).length ≤
        n := by
    simp [n, encodeAffineValidityFinalConjunctionSourceInvocation]
    omega
  have houtputLength :
      (encodeAffineExactlyOneOutputSourceInvocationFamily
          frame.rawFrames.reverse).length + 1 ≤ n := by
    simp [n, encodeAffineValidityFinalConjunctionSourceInvocation]
    omega
  have hstackSquare := Nat.pow_le_pow_left hstackLength 2
  have houtputSquare := Nat.pow_le_pow_left houtputLength 2
  have hstack := affineStackOutputFamilySource_steps_le
    stackCount frame.stackFrame
  have hstack' :
      affineStackOutputFamilySourceSteps stackCount frame.stackFrame ≤
        400 * a * n ^ 2 + 100 := by
    exact hstack.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left (400 * a) hstackSquare) 100)
  have houtputs := affineExactlyOneOutputFamilySourceSteps_le
    frame.rawFrames.reverse
  have houtputs' :
      affineExactlyOneOutputFamilySourceSteps frame.rawFrames.reverse ≤
        25 * n ^ 2 :=
    houtputs.trans (Nat.mul_le_mul_left 25 houtputSquare)
  have htotal :
      affineValidityFinalConjunctionSourceSteps stackCount frame ≤
        400 * a * n ^ 2 + 25 * n ^ 2 + 6 * n + 108 := by
    simp only [affineValidityFinalConjunctionSourceSteps]
    omega
  have h400 : 400 * a * n ^ 2 ≤ 1000 * a * n ^ 2 := by
    exact Nat.mul_le_mul_right (n ^ 2) (Nat.mul_le_mul_right a (by omega))
  have h6 : 6 * n ≤ 6 * n ^ 2 := Nat.mul_le_mul_left 6 hnSquare
  have h108 : 108 ≤ 108 * n ^ 2 := Nat.mul_le_mul_left 108 honeSquare
  have hrest : 25 * n ^ 2 + 6 * n + 108 ≤ 500 * n ^ 2 + 50 := by
    omega
  change affineValidityFinalConjunctionSourceSteps stackCount frame ≤
    (1000 * a + 500) * n ^ 2 + 50
  rw [Nat.add_mul]
  omega

end CLRS.Chapter34.Turing.PolyBuilder
