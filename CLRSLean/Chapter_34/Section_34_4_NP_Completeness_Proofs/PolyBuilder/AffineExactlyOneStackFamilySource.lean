import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackSource
import Mathlib.Tactic

/-!
# Continuous compact exactly-one source for every fixed stack

A verifier has a fixed finite list of stacks, but their common height is a
runtime quantity.  This module recursively assembles one already-verified
stack controller per fixed reachable-alphabet width.  The resulting program
keeps the complete width list in finite control and threads only the runtime
height and affine offsets through the counters.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Sole label of the empty fixed stack family. -/
inductive AffineExactlyOneEmptyStackFamilyLabel
  | finish
deriving DecidableEq, Fintype

/-- Nested sum of the fixed per-stack label types. -/
abbrev AffineExactlyOneStackFamilyLabel : List Nat → Type
  | [] => AffineExactlyOneEmptyStackFamilyLabel
  | cellCount :: rest =>
      Sum (affineExactlyOneStackRevProgram cellCount).Label
        (AffineExactlyOneStackFamilyLabel rest)

private instance affineExactlyOneStackFamilyLabelDecidableEq
    (cellCounts : List Nat) :
    DecidableEq (AffineExactlyOneStackFamilyLabel cellCounts) := by
  induction cellCounts with
  | nil =>
      simp only [AffineExactlyOneStackFamilyLabel]
      infer_instance
  | cons cellCount rest ih =>
      simp only [AffineExactlyOneStackFamilyLabel]
      letI := ih
      letI := (affineExactlyOneStackRevProgram cellCount).labelDecidableEq
      infer_instance

private instance affineExactlyOneStackFamilyLabelFintype
    (cellCounts : List Nat) :
    Fintype (AffineExactlyOneStackFamilyLabel cellCounts) := by
  induction cellCounts with
  | nil =>
      simp only [AffineExactlyOneStackFamilyLabel]
      infer_instance
  | cons cellCount rest ih =>
      simp only [AffineExactlyOneStackFamilyLabel]
      letI := ih
      letI := (affineExactlyOneStackRevProgram cellCount).labelFintype
      infer_instance

private def stackFamilyRelabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
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

private def affineExactlyOneStackFamilyMain :
    (cellCounts : List Nat) → AffineExactlyOneStackFamilyLabel cellCounts
  | [] => .finish
  | cellCount :: _ =>
      .inl (affineExactlyOneStackRevProgram cellCount).main

private def affineExactlyOneStackFamilyOp :
    (cellCounts : List Nat) →
      AffineExactlyOneStackFamilyLabel cellCounts →
        Op UnaryFrameSym UnaryFrameSym
          (AffineExactlyOneStackFamilyLabel cellCounts)
  | [], .finish => .halt
  | _cellCount :: rest, .inl (.finish) =>
      .jump (.inr (affineExactlyOneStackFamilyMain rest))
  | cellCount :: _, .inl label => stackFamilyRelabelOp .inl
      ((affineExactlyOneStackRevProgram cellCount).op label)
  | _ :: rest, .inr label => stackFamilyRelabelOp .inr
      (affineExactlyOneStackFamilyOp rest label)

/-- Recursive finite-control assembly of all stack controllers. -/
abbrev affineExactlyOneStackFamilyRevProgram
    (cellCounts : List Nat) : Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneStackFamilyLabel cellCounts
  main := affineExactlyOneStackFamilyMain cellCounts
  op := affineExactlyOneStackFamilyOp cellCounts

/-- Public terminal label, nested through the fixed stack list. -/
def affineExactlyOneStackFamilyFinishLabel :
    (cellCounts : List Nat) →
      (affineExactlyOneStackFamilyRevProgram cellCounts).Label
  | [] => .finish
  | _ :: rest => .inr (affineExactlyOneStackFamilyFinishLabel rest)

/-- The public terminal label of every fixed stack-family controller really is
the inherited halt boundary.  Outer controllers use this fact when replacing
that halt by their own continuation. -/
@[simp] theorem affineExactlyOneStackFamily_op_finish
    (cellCounts : List Nat) :
    (affineExactlyOneStackFamilyRevProgram cellCounts).op
        (affineExactlyOneStackFamilyFinishLabel cellCounts) = Op.halt := by
  induction cellCounts with
  | nil => rfl
  | cons cellCount rest ih =>
      change affineExactlyOneStackFamilyOp rest
        (affineExactlyOneStackFamilyFinishLabel rest) = Op.halt at ih
      simp [affineExactlyOneStackFamilyRevProgram,
        affineExactlyOneStackFamilyFinishLabel,
        affineExactlyOneStackFamilyOp, stackFamilyRelabelOp, ih]

/-- Gate offset after one complete height-plus-cells stack block. -/
def affineExactlyOneStackEndStart
    (cellCount height start : Nat) : Nat :=
  start + (3 * (height + 1) + 4) +
    height * (3 * cellCount + 4)

/-- Source offset after one complete height-plus-cells stack block. -/
def affineExactlyOneStackEndBase
    (cellCount height rowBase : Nat) : Nat :=
  rowBase + (height + 1) + height * cellCount

/-- Ordered compact frames for all fixed stack widths. -/
def affineExactlyOneStackFamilyFrames :
    List Nat → Nat → Nat → Nat → List AffineExactlyOneFrame
  | [], _, _, _ => []
  | cellCount :: rest, height, start, rowBase =>
      affineExactlyOneStackFrames cellCount height start rowBase ++
        affineExactlyOneStackFamilyFrames rest height
          (affineExactlyOneStackEndStart cellCount height start)
          (affineExactlyOneStackEndBase cellCount height rowBase)

private theorem encodeAffineExactlyOneCompactFamily_append
    (left right : List AffineExactlyOneFrame) :
    encodeAffineExactlyOneCompactFamily (left ++ right) =
      encodeAffineExactlyOneCompactFamily left ++
        encodeAffineExactlyOneCompactFamily right := by
  induction left with
  | nil => rfl
  | cons frame rest ih =>
      simp [encodeAffineExactlyOneCompactFamily, ih, List.append_assoc]

/-- Final gate offset after all fixed stacks. -/
def affineExactlyOneStackFamilyEndStart :
    List Nat → Nat → Nat → Nat
  | [], _, start => start
  | cellCount :: rest, height, start =>
      affineExactlyOneStackFamilyEndStart rest height
        (affineExactlyOneStackEndStart cellCount height start)

/-- Final source offset after all fixed stacks. -/
def affineExactlyOneStackFamilyEndBase :
    List Nat → Nat → Nat → Nat
  | [], _, rowBase => rowBase
  | cellCount :: rest, height, rowBase =>
      affineExactlyOneStackFamilyEndBase rest height
        (affineExactlyOneStackEndBase cellCount height rowBase)

/-- Fixed multiplicative envelope for the affine-offset growth across a
finite stack family. -/
def affineExactlyOneStackFamilyScale : List Nat → Nat
  | [] => 1
  | cellCount :: rest =>
      affineExactlyOneStackFamilyScale rest * (4 * cellCount + 10)

/-- Both final offsets, together with the preserved height, remain linearly
bounded by the initial unary payload. -/
theorem affineExactlyOneStackFamily_endPayload_le
    (cellCounts : List Nat) (height start rowBase : Nat) :
    height + affineExactlyOneStackFamilyEndStart cellCounts height start +
        affineExactlyOneStackFamilyEndBase cellCounts height rowBase + 1 ≤
      affineExactlyOneStackFamilyScale cellCounts *
        (height + start + rowBase + 1) := by
  induction cellCounts generalizing start rowBase with
  | nil =>
      simp [affineExactlyOneStackFamilyEndStart,
        affineExactlyOneStackFamilyEndBase,
        affineExactlyOneStackFamilyScale]
  | cons cellCount rest ih =>
      let nextStart := affineExactlyOneStackEndStart
        cellCount height start
      let nextBase := affineExactlyOneStackEndBase
        cellCount height rowBase
      have hnext : height + nextStart + nextBase + 1 ≤
          (4 * cellCount + 10) * (height + start + rowBase + 1) := by
        dsimp only [nextStart, nextBase]
        simp only [affineExactlyOneStackEndStart,
          affineExactlyOneStackEndBase]
        nlinarith
      have htail := ih nextStart nextBase
      calc
        height + affineExactlyOneStackFamilyEndStart
              (cellCount :: rest) height start +
            affineExactlyOneStackFamilyEndBase
              (cellCount :: rest) height rowBase + 1 =
            height + affineExactlyOneStackFamilyEndStart
              rest height nextStart +
            affineExactlyOneStackFamilyEndBase rest height nextBase + 1 := by
          rfl
        _ ≤ affineExactlyOneStackFamilyScale rest *
              (height + nextStart + nextBase + 1) := htail
        _ ≤ affineExactlyOneStackFamilyScale rest *
              ((4 * cellCount + 10) *
                (height + start + rowBase + 1)) :=
          Nat.mul_le_mul_left _ hnext
        _ = affineExactlyOneStackFamilyScale (cellCount :: rest) *
              (height + start + rowBase + 1) := by
          simp [affineExactlyOneStackFamilyScale]
          ring

/-- Fully explicit configuration constructor used by row-level controllers. -/
def affineExactlyOneStackFamilyCfg {cellCounts : List Nat}
    (label : (affineExactlyOneStackFamilyRevProgram cellCounts).Label)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg (affineExactlyOneStackFamilyRevProgram cellCounts) where
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

/-- Clean entry for a fixed stack-width family. -/
def affineExactlyOneStackFamilyLoadedCfg
    (cellCounts : List Nat) (height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneStackFamilyRevProgram cellCounts) :=
  affineExactlyOneStackFamilyCfg
    (affineExactlyOneStackFamilyRevProgram cellCounts).main
    none none false input output [] []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())

/-- Clean terminal configuration after all fixed stacks. -/
def affineExactlyOneStackFamilyFinishCfg
    (cellCounts : List Nat) (height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneStackFamilyRevProgram cellCounts) :=
  affineExactlyOneStackFamilyCfg
    (affineExactlyOneStackFamilyFinishLabel cellCounts)
    none none false input output [] []
    (List.replicate height ())
    (List.replicate
      (affineExactlyOneStackFamilyEndStart cellCounts height start) ())
    (List.replicate
      (affineExactlyOneStackFamilyEndBase cellCounts height rowBase) ())

private def stackFamilyRelabelCfg {cellCount : Nat} {rest : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label →
      (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)).Label)
    (c : BuilderCfg P) :
    BuilderCfg
      (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)) where
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

private def liftStackFamilyHeadCfg {cellCount : Nat} {rest : List Nat}
    (c : BuilderCfg (affineExactlyOneStackRevProgram cellCount)) :
    BuilderCfg
      (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)) :=
  stackFamilyRelabelCfg .inl c

private def liftStackFamilyTailCfg {cellCount : Nat} {rest : List Nat}
    (c : BuilderCfg (affineExactlyOneStackFamilyRevProgram rest)) :
    BuilderCfg
      (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)) :=
  stackFamilyRelabelCfg .inr c

private theorem stackFamilyRelabel_stepOp {cellCount : Nat}
    {rest : List Nat} {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label →
      (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)).Label)
    (op : Op UnaryFrameSym UnaryFrameSym P.Label) (c : BuilderCfg P) :
    stepOp (stackFamilyRelabelOp tag op) (stackFamilyRelabelCfg tag c) =
      stackFamilyRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [stackFamilyRelabelOp, stackFamilyRelabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneStackFamily_op_head
    {cellCount : Nat} {rest : List Nat}
    (label : AffineExactlyOneStackLabel cellCount)
    (hexit : label ≠ .finish) :
    affineExactlyOneStackFamilyOp (cellCount :: rest) (.inl label) =
      stackFamilyRelabelOp .inl
        ((affineExactlyOneStackRevProgram cellCount).op label) := by
  cases label <;>
    simp_all [affineExactlyOneStackFamilyOp]

private theorem affineExactlyOneStackFamily_op_tail
    {cellCount : Nat} {rest : List Nat}
    (label : (affineExactlyOneStackFamilyRevProgram rest).Label) :
    affineExactlyOneStackFamilyOp (cellCount :: rest) (.inr label) =
      stackFamilyRelabelOp .inr
        (affineExactlyOneStackFamilyOp rest label) := by
  rfl

private theorem liftStackFamilyHead_step {cellCount : Nat}
    {rest : List Nat}
    (c : BuilderCfg (affineExactlyOneStackRevProgram cellCount))
    (hexit : c.label ≠ some .finish) :
    step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest))
        (liftStackFamilyHeadCfg c) =
      Option.map liftStackFamilyHeadCfg
        (step (affineExactlyOneStackRevProgram cellCount) c) := by
  unfold step
  rw [show (liftStackFamilyHeadCfg c).label = c.label.map .inl by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneStackFamily_op_head label hlabelExit]
      exact congrArg some
        (stackFamilyRelabel_stepOp .inl
          ((affineExactlyOneStackRevProgram cellCount).op label) c)

private theorem liftStackFamilyTail_step {cellCount : Nat}
    {rest : List Nat}
    (c : BuilderCfg (affineExactlyOneStackFamilyRevProgram rest)) :
    step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest))
        (liftStackFamilyTailCfg c) =
      Option.map liftStackFamilyTailCfg
        (step (affineExactlyOneStackFamilyRevProgram rest) c) := by
  unfold step
  rw [show (liftStackFamilyTailCfg c).label = c.label.map .inr by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      rw [affineExactlyOneStackFamily_op_tail label]
      exact congrArg some
        (stackFamilyRelabel_stepOp .inr
          ((affineExactlyOneStackFamilyRevProgram rest).op label) c)

private theorem stackFamily_iterate_bind_none {σ : Type}
    (f : σ → Option σ) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem stackFamily_haltExit_no_return
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
      rw [hnone, stackFamily_iterate_bind_none]
      simp

private theorem stackFamily_lift_iterations_to_haltExit
    {cellCount : Nat} {rest : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg
      (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)))
    (hstep : ∀ c, c.label ≠ some exit →
      step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest))
          (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineExactlyOneStackFamilyRevProgram
          (cellCount :: rest))))^[n]
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
        (step (affineExactlyOneStackFamilyRevProgram
          (cellCount :: rest))))^[n]
          (step (affineExactlyOneStackFamilyRevProgram
            (cellCount :: rest)) (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact stackFamily_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, stackFamily_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem stackFamily_lift_iterations
    {cellCount : Nat} {rest : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tr : BuilderCfg P → BuilderCfg
      (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)))
    (hstep : ∀ c,
      step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest))
          (tr c) = Option.map tr (step P c)) :
    ∀ {a b : BuilderCfg P} (n : Nat),
      (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineExactlyOneStackFamilyRevProgram
          (cellCount :: rest))))^[n]
        (some (tr a)) = some (tr b) := by
  intro a b n
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
        (step (affineExactlyOneStackFamilyRevProgram
          (cellCount :: rest))))^[n]
          (step (affineExactlyOneStackFamilyRevProgram
            (cellCount :: rest)) (tr a)) = some (tr b)
      rw [hstep]
      cases hsource : step P a with
      | none =>
          rw [hsource, stackFamily_iterate_bind_none] at h
          contradiction
      | some c =>
          simp only [Option.map_some]
          rw [hsource] at h
          exact ih h

private def affineExactlyOneStackFamily_head_run
    {cellCount : Nat} {rest : List Nat}
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)))
      (liftStackFamilyHeadCfg
        (affineExactlyOneStackLoadedCfg cellCount height start rowBase
          input output))
      (some (liftStackFamilyHeadCfg
        (affineExactlyOneStackFinishCfg cellCount height start rowBase input
          ((encodeAffineExactlyOneCompactFamily
            (affineExactlyOneStackFrames cellCount height start rowBase)
            ).reverse ++ output))))
      (affineExactlyOneStackSteps cellCount height start rowBase) := by
  have sourceRun := affineExactlyOneStack_runToFinish
    cellCount height start rowBase input output
  have htarget :
      (affineExactlyOneStackFinishCfg cellCount height start rowBase input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStackFrames cellCount height start rowBase)
          ).reverse ++ output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact stackFamily_lift_iterations_to_haltExit
    (AffineExactlyOneStackLabel.finish (cellCount := cellCount)) rfl
    liftStackFamilyHeadCfg liftStackFamilyHead_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineExactlyOneStackFamily_tail_run
    {cellCount : Nat} {rest : List Nat}
    {a b : BuilderCfg (affineExactlyOneStackFamilyRevProgram rest)}
    {steps : Nat}
    (sourceRun : EvalsToInTime
      (step (affineExactlyOneStackFamilyRevProgram rest)) a (some b) steps) :
    EvalsToInTime
      (step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)))
      (liftStackFamilyTailCfg a) (some (liftStackFamilyTailCfg b)) steps := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact stackFamily_lift_iterations liftStackFamilyTailCfg
    liftStackFamilyTail_step sourceRun.steps sourceRun.evals_in_steps

/-- Exact recursive runtime of the fixed stack family. -/
def affineExactlyOneStackFamilySteps :
    List Nat → Nat → Nat → Nat → Nat
  | [], _, _, _ => 0
  | cellCount :: rest, height, start, rowBase =>
      affineExactlyOneStackSteps cellCount height start rowBase + 1 +
        affineExactlyOneStackFamilySteps rest height
          (affineExactlyOneStackEndStart cellCount height start)
          (affineExactlyOneStackEndBase cellCount height rowBase)

/-- Fixed coefficient for the quadratic runtime bound of a stack family. -/
def affineExactlyOneStackFamilyStepCoeff : List Nat → Nat
  | [] => 0
  | cellCount :: rest =>
      4100 * (cellCount + 1) + 1 +
        affineExactlyOneStackFamilyStepCoeff rest *
          (4 * cellCount + 10) ^ 2

/-- The recursively assembled fixed stack family is quadratic in the three
runtime unary operands. -/
theorem affineExactlyOneStackFamilySteps_le
    (cellCounts : List Nat) (height start rowBase : Nat) :
    affineExactlyOneStackFamilySteps cellCounts height start rowBase ≤
      affineExactlyOneStackFamilyStepCoeff cellCounts *
        (height + start + rowBase + 1) ^ 2 := by
  induction cellCounts generalizing start rowBase with
  | nil =>
      simp [affineExactlyOneStackFamilySteps,
        affineExactlyOneStackFamilyStepCoeff]
  | cons cellCount rest ih =>
      let payload := height + start + rowBase + 1
      let nextStart := affineExactlyOneStackEndStart
        cellCount height start
      let nextBase := affineExactlyOneStackEndBase
        cellCount height rowBase
      let nextPayload := height + nextStart + nextBase + 1
      have hpayload : 1 ≤ payload := by simp [payload]
      have hnext : nextPayload ≤ (4 * cellCount + 10) * payload := by
        dsimp only [nextPayload, nextStart, nextBase, payload]
        simp only [affineExactlyOneStackEndStart,
          affineExactlyOneStackEndBase]
        nlinarith
      have hsquare : nextPayload ^ 2 ≤
          (4 * cellCount + 10) ^ 2 * payload ^ 2 := by
        nlinarith
      have hhead := affineExactlyOneStackSteps_le
        cellCount height start rowBase
      have htailSource := ih nextStart nextBase
      have htail : affineExactlyOneStackFamilySteps rest height
          nextStart nextBase ≤
          affineExactlyOneStackFamilyStepCoeff rest *
            ((4 * cellCount + 10) ^ 2 * payload ^ 2) := by
        exact htailSource.trans
          (Nat.mul_le_mul_left
            (affineExactlyOneStackFamilyStepCoeff rest) hsquare)
      have hbridge : 1 ≤ payload ^ 2 := by nlinarith
      calc
        affineExactlyOneStackFamilySteps
            (cellCount :: rest) height start rowBase =
            affineExactlyOneStackSteps cellCount height start rowBase + 1 +
              affineExactlyOneStackFamilySteps rest height
                nextStart nextBase := by rfl
        _ ≤ 4100 * (cellCount + 1) * payload ^ 2 + payload ^ 2 +
              affineExactlyOneStackFamilyStepCoeff rest *
                ((4 * cellCount + 10) ^ 2 * payload ^ 2) :=
          Nat.add_le_add
            (Nat.add_le_add (by simpa [payload] using hhead) hbridge) htail
        _ = affineExactlyOneStackFamilyStepCoeff (cellCount :: rest) *
              payload ^ 2 := by
          simp [affineExactlyOneStackFamilyStepCoeff]
          ring

/-- The recursively assembled fixed controller emits every stack block in
order and reaches its clean nested exit in the exact stated time. -/
def affineExactlyOneStackFamily_runToFinish :
    (cellCounts : List Nat) → (height start rowBase : Nat) →
      (input output : List UnaryFrameSym) →
      EvalsToInTime
        (step (affineExactlyOneStackFamilyRevProgram cellCounts))
        (affineExactlyOneStackFamilyLoadedCfg cellCounts height start rowBase
          input output)
        (some (affineExactlyOneStackFamilyFinishCfg cellCounts height start
          rowBase input
          ((encodeAffineExactlyOneCompactFamily
            (affineExactlyOneStackFamilyFrames cellCounts height start rowBase)
            ).reverse ++ output)))
        (affineExactlyOneStackFamilySteps cellCounts height start rowBase)
  | [], height, start, rowBase, input, output => by
      exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cellCount :: rest, height, start, rowBase, input, output => by
      let nextStart := affineExactlyOneStackEndStart cellCount height start
      let nextBase := affineExactlyOneStackEndBase cellCount height rowBase
      let headFrames :=
        affineExactlyOneStackFrames cellCount height start rowBase
      let tailFrames :=
        affineExactlyOneStackFamilyFrames rest height nextStart nextBase
      let headOutput :=
        (encodeAffineExactlyOneCompactFamily headFrames).reverse ++ output
      let finalOutput :=
        (encodeAffineExactlyOneCompactFamily tailFrames).reverse ++ headOutput
      let headStart := liftStackFamilyHeadCfg (rest := rest)
        (affineExactlyOneStackLoadedCfg cellCount height start rowBase
          input output)
      let headDone := liftStackFamilyHeadCfg (rest := rest)
        (affineExactlyOneStackFinishCfg cellCount height start rowBase input
          headOutput)
      let tailStart := liftStackFamilyTailCfg (cellCount := cellCount)
        (affineExactlyOneStackFamilyLoadedCfg rest height nextStart nextBase
          input headOutput)
      let tailDone := liftStackFamilyTailCfg (cellCount := cellCount)
        (affineExactlyOneStackFamilyFinishCfg rest height nextStart nextBase
          input finalOutput)
      have hhead : EvalsToInTime
          (step (affineExactlyOneStackFamilyRevProgram
            (cellCount :: rest))) headStart (some headDone)
          (affineExactlyOneStackSteps cellCount height start rowBase) := by
        simpa [headStart, headDone, headFrames, headOutput] using
          affineExactlyOneStackFamily_head_run (rest := rest)
            height start rowBase input output
      have hbridge : EvalsToInTime
          (step (affineExactlyOneStackFamilyRevProgram
            (cellCount :: rest))) headDone (some tailStart) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        rfl
      have htailSource := affineExactlyOneStackFamily_runToFinish rest height
        nextStart nextBase input headOutput
      have htail : EvalsToInTime
          (step (affineExactlyOneStackFamilyRevProgram
            (cellCount :: rest))) tailStart (some tailDone)
          (affineExactlyOneStackFamilySteps rest height nextStart nextBase) := by
        simpa [tailStart, tailDone, tailFrames, finalOutput] using
          affineExactlyOneStackFamily_tail_run (cellCount := cellCount)
            htailSource
      let h₁ := EvalsToInTime.trans
        (step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)))
        _ 1 _ headDone _ hhead hbridge
      let full := EvalsToInTime.trans
        (step (affineExactlyOneStackFamilyRevProgram (cellCount :: rest)))
        _ _ _ tailStart _ h₁ htail
      convert full using 1
      · rfl
      · simp [tailDone, liftStackFamilyTailCfg, stackFamilyRelabelCfg,
          affineExactlyOneStackFamilyFinishCfg,
          affineExactlyOneStackFamilyCfg,
          affineExactlyOneStackFamilyFinishLabel,
          affineExactlyOneStackFamilyEndStart,
          affineExactlyOneStackFamilyEndBase,
          affineExactlyOneStackFamilyFrames, finalOutput, tailFrames,
          headOutput, headFrames,
          encodeAffineExactlyOneCompactFamily_append,
          List.reverse_append, List.append_assoc, nextStart, nextBase]
      · simp [affineExactlyOneStackFamilySteps, nextStart, nextBase]
        omega

end CLRS.Chapter34.Turing.PolyBuilder
