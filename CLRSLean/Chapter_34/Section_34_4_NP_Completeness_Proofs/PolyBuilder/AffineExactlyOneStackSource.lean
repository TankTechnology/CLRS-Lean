import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneHeightSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneCellProgressionSource
import Mathlib.Tactic

/-!
# Continuous compact exactly-one source for one verifier stack

This module connects the dynamic stack-height source to the fixed-width cell
progression source inside one finite controller.  The component exit labels
are redirected to explicit bridge instructions, so the result is one
continuous `Program`, rather than a meta-level composition of two runs.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite control of one height-plus-cells stack block. -/
inductive AffineExactlyOneStackLabel (cellCount : Nat)
  | height (label : AffineExactlyOneHeightLabel)
  | cells (label : AffineExactlyOneCellProgressionLabel cellCount)
  | finish
deriving DecidableEq, Fintype

private def stackRelabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
    Op Γ Δ Λ → Op Γ Δ Μ
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

/-- One fixed controller emits a complete stack block.  Only the alphabet
width is finite-control data; the height and both affine offsets are runtime
unary counters. -/
def affineExactlyOneStackRevProgram (cellCount : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneStackLabel cellCount
  main := .height affineExactlyOneHeightRevProgram.main
  op
    | .height .finish =>
        .jump (.cells (affineExactlyOneCellProgressionRevProgram cellCount).main)
    | .height label => stackRelabelOp .height
        (affineExactlyOneHeightRevProgram.op label)
    | .cells .finish => .jump .finish
    | .cells label => stackRelabelOp .cells
        ((affineExactlyOneCellProgressionRevProgram cellCount).op label)
    | .finish => .halt

/-- The compact frames emitted by one continuous stack controller. -/
def affineExactlyOneStackFrames
    (cellCount height start rowBase : Nat) : List AffineExactlyOneFrame :=
  affineExactlyOneHeightFrame height start rowBase ::
    affineExactlyOneFramesOfTripleProgression
      (affineExactlyOneCellProgression cellCount height
        (start + (3 * (height + 1) + 4))
        (rowBase + (height + 1)))

private def affineExactlyOneStackCfg {cellCount : Nat}
    (label : AffineExactlyOneStackLabel cellCount)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg (affineExactlyOneStackRevProgram cellCount) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := height
  counter₂ := start
  counter₃ := rowBase

/-- Clean loaded entry for one stack block. -/
def affineExactlyOneStackLoadedCfg
    (cellCount height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneStackRevProgram cellCount) :=
  affineExactlyOneStackCfg (.height affineExactlyOneHeightRevProgram.main)
    none none false input output [] []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())

/-- Public continuation after both the height frame and all cell frames. -/
def affineExactlyOneStackFinishCfg
    (cellCount height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneStackRevProgram cellCount) :=
  affineExactlyOneStackCfg .finish none none false input output [] []
    (List.replicate height ())
    (List.replicate
      (start + (3 * (height + 1) + 4) +
        height * (3 * cellCount + 4)) ())
    (List.replicate
      (rowBase + (height + 1) + height * cellCount) ())

private def stackRelabelCfg {cellCount : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → AffineExactlyOneStackLabel cellCount)
    (c : BuilderCfg P) :
    BuilderCfg (affineExactlyOneStackRevProgram cellCount) where
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

private def liftStackHeightCfg {cellCount : Nat}
    (c : BuilderCfg affineExactlyOneHeightRevProgram) :
    BuilderCfg (affineExactlyOneStackRevProgram cellCount) :=
  stackRelabelCfg .height c

private def liftStackCellsCfg {cellCount : Nat}
    (c : BuilderCfg (affineExactlyOneCellProgressionRevProgram cellCount)) :
    BuilderCfg (affineExactlyOneStackRevProgram cellCount) :=
  stackRelabelCfg .cells c

private theorem stackRelabel_stepOp {cellCount : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → AffineExactlyOneStackLabel cellCount)
    (op : Op UnaryFrameSym UnaryFrameSym P.Label) (c : BuilderCfg P) :
    stepOp (stackRelabelOp tag op) (stackRelabelCfg tag c) =
      stackRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [stackRelabelOp, stackRelabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneStack_op_height {cellCount : Nat}
    (label : AffineExactlyOneHeightLabel) (hexit : label ≠ .finish) :
    (affineExactlyOneStackRevProgram cellCount).op (.height label) =
      stackRelabelOp .height (affineExactlyOneHeightRevProgram.op label) := by
  cases label <;>
    simp_all [affineExactlyOneStackRevProgram] <;> rfl

private theorem affineExactlyOneStack_op_cells {cellCount : Nat}
    (label : AffineExactlyOneCellProgressionLabel cellCount)
    (hexit : label ≠ .finish) :
    (affineExactlyOneStackRevProgram cellCount).op (.cells label) =
      stackRelabelOp .cells
        ((affineExactlyOneCellProgressionRevProgram cellCount).op label) := by
  cases label <;>
    simp_all [affineExactlyOneStackRevProgram] <;> rfl

private theorem liftStackHeight_step {cellCount : Nat}
    (c : BuilderCfg affineExactlyOneHeightRevProgram)
    (hexit : c.label ≠ some .finish) :
    step (affineExactlyOneStackRevProgram cellCount) (liftStackHeightCfg c) =
      Option.map liftStackHeightCfg (step affineExactlyOneHeightRevProgram c) := by
  unfold step
  rw [show (liftStackHeightCfg c).label = c.label.map .height by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneStack_op_height label hlabelExit]
      exact congrArg some
        (stackRelabel_stepOp .height
          (affineExactlyOneHeightRevProgram.op label) c)

private theorem liftStackCells_step {cellCount : Nat}
    (c : BuilderCfg (affineExactlyOneCellProgressionRevProgram cellCount))
    (hexit : c.label ≠ some .finish) :
    step (affineExactlyOneStackRevProgram cellCount) (liftStackCellsCfg c) =
      Option.map liftStackCellsCfg
        (step (affineExactlyOneCellProgressionRevProgram cellCount) c) := by
  unfold step
  rw [show (liftStackCellsCfg c).label = c.label.map .cells by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneStack_op_cells label hlabelExit]
      exact congrArg some
        (stackRelabel_stepOp .cells
          ((affineExactlyOneCellProgressionRevProgram cellCount).op label) c)

private theorem stack_iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem stack_haltExit_no_return
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
      rw [hnone, stack_iterate_bind_none]
      simp

private theorem stack_lift_iterations_to_haltExit {cellCount : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P →
      BuilderCfg (affineExactlyOneStackRevProgram cellCount))
    (hstep : ∀ c, c.label ≠ some exit →
      step (affineExactlyOneStackRevProgram cellCount) (tr c) =
        Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineExactlyOneStackRevProgram cellCount)))^[n]
        (some (tr a)) = some (tr b) := by
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
        (step (affineExactlyOneStackRevProgram cellCount)))^[n]
          (step (affineExactlyOneStackRevProgram cellCount) (tr a)) =
            some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact stack_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, stack_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineExactlyOneStack_height_run {cellCount : Nat}
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    EvalsToInTime (step (affineExactlyOneStackRevProgram cellCount))
      (liftStackHeightCfg
        (affineExactlyOneHeightLoadedCfg height start rowBase input output))
      (some (liftStackHeightCfg
        (affineExactlyOneHeightFinishCfg height start rowBase input
          ((encodeAffineExactlyOneCompactFrame
            (affineExactlyOneHeightFrame height start rowBase)).reverse ++
            output))))
      (affineExactlyOneHeightSteps height start rowBase) := by
  have sourceRun := affineExactlyOneHeight_runToFinish
    height start rowBase input output
  have htarget : (affineExactlyOneHeightFinishCfg height start rowBase input
      ((encodeAffineExactlyOneCompactFrame
        (affineExactlyOneHeightFrame height start rowBase)).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact stack_lift_iterations_to_haltExit AffineExactlyOneHeightLabel.finish
    rfl liftStackHeightCfg liftStackHeight_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineExactlyOneStack_cells_run {cellCount : Nat}
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    EvalsToInTime (step (affineExactlyOneStackRevProgram cellCount))
      (liftStackCellsCfg
        (affineExactlyOneCellProgressionLoadedCfg cellCount height start rowBase
          input output))
      (some (liftStackCellsCfg
        (affineExactlyOneCellProgressionFinishCfg cellCount height start
          rowBase input
          ((encodeAffineExactlyOneCompactFamily
            (affineExactlyOneFramesOfTripleProgression
              (affineExactlyOneCellProgression cellCount height start rowBase))
            ).reverse ++ output))))
      (affineExactlyOneCellProgressionSteps cellCount height start rowBase) := by
  have sourceRun := affineExactlyOneCellProgression_runToFinish
    cellCount height start rowBase input output
  have htarget :
      (affineExactlyOneCellProgressionFinishCfg cellCount height start rowBase
        input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneFramesOfTripleProgression
            (affineExactlyOneCellProgression cellCount height start rowBase))
          ).reverse ++ output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact stack_lift_iterations_to_haltExit
    (AffineExactlyOneCellProgressionLabel.finish (cellCount := cellCount)) rfl
    liftStackCellsCfg liftStackCells_step htarget sourceRun.steps
      sourceRun.evals_in_steps

/-- Exact runtime of one continuous stack block, including both bridge
instructions. -/
def affineExactlyOneStackSteps
    (cellCount height start rowBase : Nat) : Nat :=
  affineExactlyOneHeightSteps height start rowBase + 1 +
    affineExactlyOneCellProgressionSteps cellCount height
      (start + (3 * (height + 1) + 4))
      (rowBase + (height + 1)) + 1

/-- A fixed-width stack block is quadratic in its three unary runtime
operands. -/
theorem affineExactlyOneStackSteps_le
    (cellCount height start rowBase : Nat) :
    affineExactlyOneStackSteps cellCount height start rowBase ≤
      4100 * (cellCount + 1) *
        (height + start + rowBase + 1) ^ 2 := by
  let payload := height + start + rowBase + 1
  let cellPayload := height +
    (start + (3 * (height + 1) + 4)) +
    (rowBase + (height + 1)) + 1
  have hpayload : 1 ≤ payload := by simp [payload]
  have hcellPayload : cellPayload ≤ 9 * payload := by
    dsimp only [cellPayload, payload]
    omega
  have hsquare : cellPayload ^ 2 ≤ 81 * payload ^ 2 := by
    nlinarith
  have hcellSource := affineExactlyOneCellProgressionSteps_le
    cellCount height (start + (3 * (height + 1) + 4))
      (rowBase + (height + 1))
  have hcell :
      affineExactlyOneCellProgressionSteps cellCount height
          (start + (3 * (height + 1) + 4))
          (rowBase + (height + 1)) ≤
        4050 * (cellCount + 1) * payload ^ 2 := by
    calc
      affineExactlyOneCellProgressionSteps cellCount height
          (start + (3 * (height + 1) + 4))
          (rowBase + (height + 1)) ≤
          50 * (cellCount + 1) * cellPayload ^ 2 := by
        simpa [cellPayload] using hcellSource
      _ ≤ 50 * (cellCount + 1) * (81 * payload ^ 2) :=
        Nat.mul_le_mul_left (50 * (cellCount + 1)) hsquare
      _ = 4050 * (cellCount + 1) * payload ^ 2 := by ring
  have hheight : affineExactlyOneHeightSteps height start rowBase + 2 ≤
      50 * (cellCount + 1) * payload ^ 2 := by
    simp only [affineExactlyOneHeightSteps]
    dsimp only [payload]
    nlinarith
  calc
    affineExactlyOneStackSteps cellCount height start rowBase =
        (affineExactlyOneHeightSteps height start rowBase + 2) +
          affineExactlyOneCellProgressionSteps cellCount height
            (start + (3 * (height + 1) + 4))
            (rowBase + (height + 1)) := by
      simp [affineExactlyOneStackSteps]
      omega
    _ ≤ 50 * (cellCount + 1) * payload ^ 2 +
          4050 * (cellCount + 1) * payload ^ 2 :=
      Nat.add_le_add hheight hcell
    _ = 4100 * (cellCount + 1) * payload ^ 2 := by ring

/-- The single fixed controller emits the exact compact height-plus-cells
family, preserves `H`, advances both offsets, and reaches its public exit. -/
def affineExactlyOneStack_runToFinish
    (cellCount height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneStackRevProgram cellCount))
      (affineExactlyOneStackLoadedCfg cellCount height start rowBase
        input output)
      (some (affineExactlyOneStackFinishCfg cellCount height start rowBase
        input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStackFrames cellCount height start rowBase)).reverse ++
          output)))
      (affineExactlyOneStackSteps cellCount height start rowBase) := by
  let heightOutput :=
    (encodeAffineExactlyOneCompactFrame
      (affineExactlyOneHeightFrame height start rowBase)).reverse ++ output
  let afterHeightStart := start + (3 * (height + 1) + 4)
  let afterHeightBase := rowBase + (height + 1)
  let cellFrames := affineExactlyOneFramesOfTripleProgression
    (affineExactlyOneCellProgression cellCount height afterHeightStart
      afterHeightBase)
  let finalOutput :=
    (encodeAffineExactlyOneCompactFamily cellFrames).reverse ++ heightOutput
  let heightStart := liftStackHeightCfg (cellCount := cellCount)
    (affineExactlyOneHeightLoadedCfg height start rowBase input output)
  let heightDone := liftStackHeightCfg (cellCount := cellCount)
    (affineExactlyOneHeightFinishCfg height start rowBase input heightOutput)
  let cellStart := liftStackCellsCfg
    (affineExactlyOneCellProgressionLoadedCfg cellCount height
      afterHeightStart afterHeightBase input heightOutput)
  let cellDone := liftStackCellsCfg
    (affineExactlyOneCellProgressionFinishCfg cellCount height
      afterHeightStart afterHeightBase input finalOutput)
  have hheight : EvalsToInTime
      (step (affineExactlyOneStackRevProgram cellCount)) heightStart
      (some heightDone) (affineExactlyOneHeightSteps height start rowBase) := by
    simpa [heightStart, heightDone, heightOutput] using
      affineExactlyOneStack_height_run (cellCount := cellCount)
        height start rowBase input output
  have hheightBridge : EvalsToInTime
      (step (affineExactlyOneStackRevProgram cellCount)) heightDone
      (some cellStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hcells : EvalsToInTime
      (step (affineExactlyOneStackRevProgram cellCount)) cellStart
      (some cellDone)
      (affineExactlyOneCellProgressionSteps cellCount height
        afterHeightStart afterHeightBase) := by
    simpa [cellStart, cellDone, cellFrames, finalOutput] using
      affineExactlyOneStack_cells_run (cellCount := cellCount) height afterHeightStart
        afterHeightBase input heightOutput
  have hfinish : EvalsToInTime
      (step (affineExactlyOneStackRevProgram cellCount)) cellDone
      (some (affineExactlyOneStackFinishCfg cellCount height start rowBase
        input finalOutput)) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneStackRevProgram cellCount)) _ 1 _ heightDone _
      hheight hheightBridge
  let h₂ := EvalsToInTime.trans
    (step (affineExactlyOneStackRevProgram cellCount)) _ _ _ cellStart _
      h₁ hcells
  let full := EvalsToInTime.trans
    (step (affineExactlyOneStackRevProgram cellCount)) _ 1 _ cellDone _
      h₂ hfinish
  convert full using 1
  · rfl
  · simp [affineExactlyOneStackFrames, finalOutput, cellFrames,
      heightOutput, afterHeightStart, afterHeightBase,
      encodeAffineExactlyOneCompactFamily, List.reverse_append,
      List.append_assoc]
  · simp [affineExactlyOneStackSteps, afterHeightStart, afterHeightBase]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
