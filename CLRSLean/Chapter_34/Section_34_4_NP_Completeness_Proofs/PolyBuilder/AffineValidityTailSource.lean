import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityFinalConjunctionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailStackFamilySource
import Mathlib.Tactic

/-!
# Continuous source for a complete validity-row tail

This module joins the runtime stack-family source to the final-conjunction
source without an intermediate halt.  The input is still the compact runtime
operand stream; the machine emits exactly the reverse serialization consumed
by the already verified `AffineValidityTail` gate controller.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Compact source operands for one complete post-halted validity tail. -/
structure AffineValidityTailSourceFrame where
  stackSeeds : List AffineRuntimeStackSourceSeed
  finalFrame : AffineValidityFinalConjunctionSourceFrame
deriving DecidableEq, Repr

/-- Explicit invocation consumed by the linked source. -/
def encodeAffineValidityTailSourceInvocation
    (frame : AffineValidityTailSourceFrame) : List UnaryFrameSym :=
  encodeAffineRuntimeStackStandaloneInvocationFamily frame.stackSeeds ++
    encodeAffineValidityFinalConjunctionSourceInvocation frame.finalFrame

/-- Runtime frame denoted by the compact source operands. -/
def affineValidityTailSourceFrame (blankSteps : List Nat)
    (frame : AffineValidityTailSourceFrame) : AffineValidityTailFrame :=
  { stackFrames :=
      affineRuntimeStackSourceFamilyFrames blankSteps frame.stackSeeds
    finalFrame := affineValidityFinalConjunctionFrame
      blankSteps.length frame.finalFrame }

private def validityTailSourceRelabelOp {Γ Δ Λ Μ : Type}
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

/-- Fixed finite-control composition of the stack-family and conjunction
sources.  The verifier-dependent stack widths occur only as parameters of
finite control. -/
abbrev affineValidityTailSourceRevProgram (blankSteps : List Nat) :
    Program UnaryFrameSym UnaryFrameSym :=
  let stackProgram := affineRuntimeStackFamilySourceRevProgram blankSteps
  let finalProgram :=
    affineValidityFinalConjunctionSourceRevProgram blankSteps.length
  letI := stackProgram.labelDecidableEq
  letI := stackProgram.labelFintype
  letI := finalProgram.labelDecidableEq
  letI := finalProgram.labelFintype
  { Label := Sum stackProgram.Label finalProgram.Label
    main := .inl stackProgram.main
    op := fun
      | .inl label =>
          if label = affineRuntimeStackFamilySourceFinishLabel blankSteps then
            .jump (.inr finalProgram.main)
          else
            validityTailSourceRelabelOp .inl (stackProgram.op label)
      | .inr label =>
          validityTailSourceRelabelOp .inr (finalProgram.op label) }

private def affineValidityTailSourceCfg {blankSteps : List Nat}
    (label : (affineValidityTailSourceRevProgram blankSteps).Label)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineValidityTailSourceRevProgram blankSteps) where
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

/-- Clean entry of the linked tail source. -/
def affineValidityTailSourceLoopCfg (blankSteps : List Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineValidityTailSourceRevProgram blankSteps) :=
  affineValidityTailSourceCfg
    (affineValidityTailSourceRevProgram blankSteps).main
    none none false input output [] [] [] [] []

/-- Clean redirectable exit inherited from the final-conjunction source. -/
def affineValidityTailSourceFinishCfg (blankSteps : List Nat)
    (tail output : List UnaryFrameSym) :
    BuilderCfg (affineValidityTailSourceRevProgram blankSteps) :=
  affineValidityTailSourceCfg
    (.inr (.finish : AffineValidityFinalConjunctionSourceLabel
      blankSteps.length))
    (some .frameEnd) none false tail output [] [] [] [] []

private def validityTailSourceRelabelCfg {blankSteps : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → (affineValidityTailSourceRevProgram blankSteps).Label)
    (c : BuilderCfg P) :
    BuilderCfg (affineValidityTailSourceRevProgram blankSteps) where
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

private theorem validityTailSourceRelabel_stepOp {blankSteps : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → (affineValidityTailSourceRevProgram blankSteps).Label)
    (op : Op UnaryFrameSym UnaryFrameSym P.Label) (c : BuilderCfg P) :
    stepOp (validityTailSourceRelabelOp tag op)
        (validityTailSourceRelabelCfg tag c) =
      validityTailSourceRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [validityTailSourceRelabelOp, validityTailSourceRelabelCfg,
      stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineValidityTailSource_op_stacks (blankSteps : List Nat)
    (label : (affineRuntimeStackFamilySourceRevProgram blankSteps).Label)
    (hexit : label ≠ affineRuntimeStackFamilySourceFinishLabel blankSteps) :
    (affineValidityTailSourceRevProgram blankSteps).op (.inl label) =
      validityTailSourceRelabelOp .inl
        ((affineRuntimeStackFamilySourceRevProgram blankSteps).op label) := by
  simp [affineValidityTailSourceRevProgram, hexit]

private theorem affineValidityTailSource_op_stacks_finish
    (blankSteps : List Nat) :
    (affineValidityTailSourceRevProgram blankSteps).op
        (.inl (affineRuntimeStackFamilySourceFinishLabel blankSteps)) =
      .jump (.inr
        (affineValidityFinalConjunctionSourceRevProgram
          blankSteps.length).main) := by
  simp [affineValidityTailSourceRevProgram]

private theorem affineValidityTailSource_op_final (blankSteps : List Nat)
    (label : AffineValidityFinalConjunctionSourceLabel blankSteps.length)
    (_hexit : label ≠ .finish) :
    (affineValidityTailSourceRevProgram blankSteps).op (.inr label) =
      validityTailSourceRelabelOp .inr
        ((affineValidityFinalConjunctionSourceRevProgram
          blankSteps.length).op label) := by
  rfl

private theorem validityTailSource_left_loop_eq (blankSteps : List Nat)
    (input output : List UnaryFrameSym) :
    validityTailSourceRelabelCfg .inl
        (affineRuntimeStackFamilySourceLoopCfg blankSteps input output) =
      affineValidityTailSourceLoopCfg blankSteps input output := by
  rfl

private theorem validityTailSource_right_loop_eq (blankSteps : List Nat)
    (input output : List UnaryFrameSym) :
    validityTailSourceRelabelCfg .inr
        (affineValidityFinalConjunctionSourceLoopCfg blankSteps.length
          input output) =
      affineValidityTailSourceCfg
        (.inr (affineValidityFinalConjunctionSourceRevProgram
          blankSteps.length).main)
        none none false input output [] [] [] [] [] := by
  rfl

private theorem validityTailSource_right_finish_eq (blankSteps : List Nat)
    (tail output : List UnaryFrameSym) :
    validityTailSourceRelabelCfg .inr
        (affineValidityFinalConjunctionSourceFinishCfg blankSteps.length
          tail output) =
      affineValidityTailSourceFinishCfg blankSteps tail output := by
  rfl

private theorem validityTailSource_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem validityTailSource_haltExit_no_return
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
      rw [hnone, validityTailSource_iterate_bind_none]
      simp

private theorem validityTailSource_lift_step {blankSteps : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (tag : P.Label → (affineValidityTailSourceRevProgram blankSteps).Label)
    (hopOuter : ∀ label, label ≠ exit →
      (affineValidityTailSourceRevProgram blankSteps).op (tag label) =
        validityTailSourceRelabelOp tag (P.op label))
    (c : BuilderCfg P) (hexit : c.label ≠ some exit) :
    step (affineValidityTailSourceRevProgram blankSteps)
        (validityTailSourceRelabelCfg tag c) =
      Option.map (validityTailSourceRelabelCfg tag) (step P c) := by
  unfold step
  rw [show (validityTailSourceRelabelCfg tag c).label =
      c.label.map tag by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ exit := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      change some (stepOp
        ((affineValidityTailSourceRevProgram blankSteps).op (tag label))
        (validityTailSourceRelabelCfg tag c)) = _
      rw [hopOuter label hlabelExit]
      exact congrArg some
        (validityTailSourceRelabel_stepOp tag (P.op label) c)

private theorem validityTailSource_lift_iterations {blankSteps : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tag : P.Label → (affineValidityTailSourceRevProgram blankSteps).Label)
    (hopOuter : ∀ label, label ≠ exit →
      (affineValidityTailSourceRevProgram blankSteps).op (tag label) =
        validityTailSourceRelabelOp tag (P.op label))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineValidityTailSourceRevProgram blankSteps)))^[n]
          (some (validityTailSourceRelabelCfg tag a)) =
            some (validityTailSourceRelabelCfg tag b) := by
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
        (step (affineValidityTailSourceRevProgram blankSteps)))^[n]
          (step (affineValidityTailSourceRevProgram blankSteps)
            (validityTailSourceRelabelCfg tag a)) =
            some (validityTailSourceRelabelCfg tag b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact validityTailSource_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, validityTailSource_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := validityTailSource_lift_step
            exit tag hopOuter a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineValidityTailSource_stacks_run (blankSteps : List Nat)
    (seeds : List AffineRuntimeStackSourceSeed)
    (tail output : List UnaryFrameSym)
    (hlength : seeds.length = blankSteps.length) :
    EvalsToInTime
      (step (affineValidityTailSourceRevProgram blankSteps))
      (validityTailSourceRelabelCfg .inl
        (affineRuntimeStackFamilySourceLoopCfg blankSteps
          (encodeAffineRuntimeStackStandaloneInvocationFamily seeds ++ tail)
          output))
      (some (validityTailSourceRelabelCfg .inl
        (affineRuntimeStackFamilySourceFinishCfg blankSteps tail
          ((encodeAffineStackFamily
            (affineRuntimeStackSourceFamilyFrames blankSteps seeds) ++
              [UnaryFrameSym.frameEnd]).reverse ++ output))))
      (affineRuntimeStackFamilySourceSteps blankSteps seeds) := by
  have sourceRun := affineRuntimeStackFamilySource_runToFinish
    blankSteps seeds tail output hlength
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact validityTailSource_lift_iterations
    (blankSteps := blankSteps)
    (P := affineRuntimeStackFamilySourceRevProgram blankSteps)
    (affineRuntimeStackFamilySourceFinishLabel blankSteps)
    (affineRuntimeStackFamilySource_op_finish blankSteps) .inl
    (affineValidityTailSource_op_stacks blankSteps) rfl
    sourceRun.steps sourceRun.evals_in_steps

private def affineValidityTailSource_final_run (blankSteps : List Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineValidityTailSourceRevProgram blankSteps))
      (validityTailSourceRelabelCfg .inr
        (affineValidityFinalConjunctionSourceLoopCfg blankSteps.length
          (encodeAffineValidityFinalConjunctionSourceInvocation frame ++ tail)
          output))
      (some (validityTailSourceRelabelCfg .inr
        (affineValidityFinalConjunctionSourceFinishCfg blankSteps.length tail
          ((encodeAffineConjunctionFrame
            (affineValidityFinalConjunctionFrame blankSteps.length frame)
              ).reverse ++ output))))
      (affineValidityFinalConjunctionSourceSteps blankSteps.length frame) := by
  have sourceRun := affineValidityFinalConjunctionSource_runToFinish
    blankSteps.length frame tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact validityTailSource_lift_iterations
    (blankSteps := blankSteps)
    (P := affineValidityFinalConjunctionSourceRevProgram blankSteps.length)
    (AffineValidityFinalConjunctionSourceLabel.finish) rfl .inr
    (affineValidityTailSource_op_final blankSteps) rfl
    sourceRun.steps sourceRun.evals_in_steps

/-- Exact runtime of the linked complete-tail source. -/
def affineValidityTailSourceSteps (blankSteps : List Nat)
    (frame : AffineValidityTailSourceFrame) : Nat :=
  affineRuntimeStackFamilySourceSteps blankSteps frame.stackSeeds + 1 +
    affineValidityFinalConjunctionSourceSteps
      blankSteps.length frame.finalFrame

/-- The linked source emits the precise reverse serialization of the public
tail frame and leaves the following invocation untouched. -/
def affineValidityTailSource_runToFinish (blankSteps : List Nat)
    (frame : AffineValidityTailSourceFrame)
    (tail output : List UnaryFrameSym)
    (hlength : frame.stackSeeds.length = blankSteps.length) :
    EvalsToInTime
      (step (affineValidityTailSourceRevProgram blankSteps))
      (affineValidityTailSourceLoopCfg blankSteps
        (encodeAffineValidityTailSourceInvocation frame ++ tail) output)
      (some (affineValidityTailSourceFinishCfg blankSteps tail
        ((encodeAffineValidityTailFrame
          (affineValidityTailSourceFrame blankSteps frame)).reverse ++
            output)))
      (affineValidityTailSourceSteps blankSteps frame) := by
  let finalInput :=
    encodeAffineValidityFinalConjunctionSourceInvocation frame.finalFrame ++
      tail
  let stackOutput :=
    (encodeAffineStackFamily
      (affineRuntimeStackSourceFamilyFrames blankSteps frame.stackSeeds) ++
        [UnaryFrameSym.frameEnd]).reverse ++ output
  have hstacks := affineValidityTailSource_stacks_run
    blankSteps frame.stackSeeds finalInput output hlength
  have hbridge : EvalsToInTime
      (step (affineValidityTailSourceRevProgram blankSteps))
      (validityTailSourceRelabelCfg .inl
        (affineRuntimeStackFamilySourceFinishCfg blankSteps finalInput
          stackOutput))
      (some (validityTailSourceRelabelCfg .inr
        (affineValidityFinalConjunctionSourceLoopCfg blankSteps.length
          finalInput stackOutput))) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step (affineValidityTailSourceRevProgram blankSteps)
      (validityTailSourceRelabelCfg .inl
        (affineRuntimeStackFamilySourceFinishCfg blankSteps finalInput
          stackOutput)) = _
    unfold step
    change some (stepOp
      ((affineValidityTailSourceRevProgram blankSteps).op
        (.inl (affineRuntimeStackFamilySourceFinishLabel blankSteps)))
      (validityTailSourceRelabelCfg .inl
        (affineRuntimeStackFamilySourceFinishCfg blankSteps finalInput
          stackOutput))) = _
    rw [affineValidityTailSource_op_stacks_finish]
    rfl
  have hfinal := affineValidityTailSource_final_run
    blankSteps frame.finalFrame tail stackOutput
  let h₁ := EvalsToInTime.trans
    (step (affineValidityTailSourceRevProgram blankSteps)) _ 1 _ _ _
      hstacks hbridge
  let full := EvalsToInTime.trans
    (step (affineValidityTailSourceRevProgram blankSteps)) _ _ _ _ _
      h₁ hfinal
  convert full using 1
  · rw [validityTailSource_left_loop_eq]
    simp only [encodeAffineValidityTailSourceInvocation, finalInput,
      List.append_assoc]
  · rw [validityTailSource_right_finish_eq]
    congr 1
    simp [affineValidityTailSourceFrame, encodeAffineValidityTailFrame,
      stackOutput, List.reverse_append, List.append_assoc]
  · simp [affineValidityTailSourceSteps]
    omega

/-- Fixed coefficient for the complete compact-tail source. -/
def affineValidityTailSourceStepCoeff (blankSteps : List Nat) : Nat :=
  affineRuntimeStackFamilySourceStepCoeff blankSteps +
    affineValidityFinalConjunctionSourceStepCoeff blankSteps.length + 52

/-- The complete linked source is quadratic in its explicit compact
invocation. -/
theorem affineValidityTailSource_steps_le (blankSteps : List Nat)
    (frame : AffineValidityTailSourceFrame)
    (hlength : frame.stackSeeds.length = blankSteps.length) :
    affineValidityTailSourceSteps blankSteps frame ≤
      affineValidityTailSourceStepCoeff blankSteps *
        ((encodeAffineValidityTailSourceInvocation frame).length + 1) ^ 2 := by
  let stackLength :=
    (encodeAffineRuntimeStackStandaloneInvocationFamily
      frame.stackSeeds).length
  let finalLength :=
    (encodeAffineValidityFinalConjunctionSourceInvocation
      frame.finalFrame).length
  let total := stackLength + finalLength + 1
  have htotal : 1 ≤ total := by simp [total]
  have hstackSquare : (stackLength + 1) ^ 2 ≤ total ^ 2 := by
    exact Nat.pow_le_pow_left (by simp [total]) 2
  have hfinalSquare : finalLength ^ 2 ≤ total ^ 2 := by
    exact Nat.pow_le_pow_left (by dsimp only [total]; omega) 2
  have hstack := affineRuntimeStackFamilySourceSteps_le
    blankSteps frame.stackSeeds hlength
  have hstack' : affineRuntimeStackFamilySourceSteps
      blankSteps frame.stackSeeds ≤
      affineRuntimeStackFamilySourceStepCoeff blankSteps * total ^ 2 :=
    hstack.trans (Nat.mul_le_mul_left _ hstackSquare)
  have hfinal := affineValidityFinalConjunctionSource_steps_le
    blankSteps.length frame.finalFrame
  have hfinal' : affineValidityFinalConjunctionSourceSteps
      blankSteps.length frame.finalFrame ≤
      (affineValidityFinalConjunctionSourceStepCoeff blankSteps.length + 50) *
        total ^ 2 := by
    calc
      affineValidityFinalConjunctionSourceSteps
          blankSteps.length frame.finalFrame ≤
          affineValidityFinalConjunctionSourceStepCoeff blankSteps.length *
            finalLength ^ 2 + 50 := by
        simpa [finalLength] using hfinal
      _ ≤ affineValidityFinalConjunctionSourceStepCoeff blankSteps.length *
            total ^ 2 + 50 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hfinalSquare) 50
      _ ≤ (affineValidityFinalConjunctionSourceStepCoeff blankSteps.length +
            50) * total ^ 2 := by nlinarith
  have hone : 1 ≤ 2 * total ^ 2 := by nlinarith
  calc
    affineValidityTailSourceSteps blankSteps frame =
        affineRuntimeStackFamilySourceSteps blankSteps frame.stackSeeds + 1 +
          affineValidityFinalConjunctionSourceSteps
            blankSteps.length frame.finalFrame := rfl
    _ ≤ affineRuntimeStackFamilySourceStepCoeff blankSteps * total ^ 2 +
          2 * total ^ 2 +
          (affineValidityFinalConjunctionSourceStepCoeff blankSteps.length +
            50) * total ^ 2 := by
      omega
    _ = affineValidityTailSourceStepCoeff blankSteps * total ^ 2 := by
      simp [affineValidityTailSourceStepCoeff]
      ring
    _ = affineValidityTailSourceStepCoeff blankSteps *
          ((encodeAffineValidityTailSourceInvocation frame).length + 1) ^ 2 := by
      simp [encodeAffineValidityTailSourceInvocation, stackLength,
        finalLength, total]

end CLRS.Chapter34.Turing.PolyBuilder
