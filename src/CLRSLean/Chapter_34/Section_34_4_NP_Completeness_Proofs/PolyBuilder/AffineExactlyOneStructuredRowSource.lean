import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOnePrefixSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackFamilySource
import Mathlib.Tactic

/-!
# Continuous compact exactly-one source for one structured row

This is the row-level composition boundary.  One fixed controller emits the
label and state groups, bridges directly to every fixed stack block, and
stops at the stack-family exit.  The common height and affine offsets remain
runtime unary counters throughout the complete run.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private def structuredRowRelabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
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

/-- Fixed controller for the prefix followed by a fixed stack-width family. -/
abbrev affineExactlyOneStructuredRowRevProgram
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    Program UnaryFrameSym UnaryFrameSym :=
  let prefixProgram := affineExactlyOnePrefixRevProgram labelWidth stateWidth
  let stacksProgram := affineExactlyOneStackFamilyRevProgram cellCounts
  letI := prefixProgram.labelDecidableEq
  letI := prefixProgram.labelFintype
  letI := stacksProgram.labelDecidableEq
  letI := stacksProgram.labelFintype
  { Label := Sum prefixProgram.Label stacksProgram.Label
    main := .inl prefixProgram.main
    op := fun
      | .inl (.finish) => .jump (.inr stacksProgram.main)
      | .inl label => structuredRowRelabelOp .inl (prefixProgram.op label)
      | .inr label => structuredRowRelabelOp .inr (stacksProgram.op label) }

/-- Gate offset at the beginning of the first stack. -/
def affineExactlyOneStructuredRowStackStart
    (labelWidth stateWidth start : Nat) : Nat :=
  start + (3 * labelWidth + 4) + (3 * stateWidth + 4)

/-- Source offset at the beginning of the first stack. -/
def affineExactlyOneStructuredRowStackBase
    (labelWidth stateWidth rowBase : Nat) : Nat :=
  rowBase + 1 + labelWidth + stateWidth

/-- Exact compact frame sequence emitted for one row. -/
def affineExactlyOneStructuredRowFrames
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) : List AffineExactlyOneFrame :=
  affineExactlyOnePrefixFrames labelWidth stateWidth start rowBase ++
    affineExactlyOneStackFamilyFrames cellCounts height
      (affineExactlyOneStructuredRowStackStart labelWidth stateWidth start)
      (affineExactlyOneStructuredRowStackBase labelWidth stateWidth rowBase)

private def affineExactlyOneStructuredRowCfg
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (label : (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts).Label)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts) where
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

/-- Clean entry for one structured row. -/
def affineExactlyOneStructuredRowLoadedCfg
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts) :=
  affineExactlyOneStructuredRowCfg
    (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts).main
    none none false input output [] []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())

/-- Public row exit, inherited from the complete stack family. -/
def affineExactlyOneStructuredRowFinishCfg
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts) :=
  affineExactlyOneStructuredRowCfg
    (.inr (affineExactlyOneStackFamilyFinishLabel cellCounts))
    none none false input output [] []
    (List.replicate height ())
    (List.replicate (affineExactlyOneStackFamilyEndStart cellCounts height
      (affineExactlyOneStructuredRowStackStart labelWidth stateWidth start)) ())
    (List.replicate (affineExactlyOneStackFamilyEndBase cellCounts height
      (affineExactlyOneStructuredRowStackBase labelWidth stateWidth rowBase)) ())

/-- Explicit public shape of the row exit.  This lets an outer controller
replace the halt while retaining the exact persistent counter values. -/
theorem affineExactlyOneStructuredRowFinishCfg_eq
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    affineExactlyOneStructuredRowFinishCfg labelWidth stateWidth cellCounts
        height start rowBase input output =
      { label := some (.inr
          (affineExactlyOneStackFamilyFinishLabel cellCounts))
        buffer₁ := none
        buffer₂ := none
        test := false
        input := input
        output := output
        work₁ := []
        work₂ := []
        counter₁ := List.replicate height ()
        counter₂ := List.replicate
          (affineExactlyOneStackFamilyEndStart cellCounts height
            (affineExactlyOneStructuredRowStackStart
              labelWidth stateWidth start)) ()
        counter₃ := List.replicate
          (affineExactlyOneStackFamilyEndBase cellCounts height
            (affineExactlyOneStructuredRowStackBase
              labelWidth stateWidth rowBase)) () } := rfl

/-- The public row exit is the embedded stack-family halt boundary. -/
@[simp] theorem affineExactlyOneStructuredRow_op_finish
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts).op
        (.inr (affineExactlyOneStackFamilyFinishLabel cellCounts)) =
      Op.halt := by
  change structuredRowRelabelOp Sum.inr
    ((affineExactlyOneStackFamilyRevProgram cellCounts).op
      (affineExactlyOneStackFamilyFinishLabel cellCounts)) = Op.halt
  rw [affineExactlyOneStackFamily_op_finish]
  rfl

private def structuredRowRelabelCfg
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts).Label)
    (c : BuilderCfg P) :
    BuilderCfg (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts) where
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

private def liftStructuredRowPrefixCfg
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (c : BuilderCfg
      (affineExactlyOnePrefixRevProgram labelWidth stateWidth)) :
    BuilderCfg (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts) :=
  structuredRowRelabelCfg .inl c

private def liftStructuredRowStacksCfg
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (c : BuilderCfg (affineExactlyOneStackFamilyRevProgram cellCounts)) :
    BuilderCfg (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts) :=
  structuredRowRelabelCfg .inr c

private theorem structuredRowRelabel_stepOp
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts).Label)
    (op : Op UnaryFrameSym UnaryFrameSym P.Label) (c : BuilderCfg P) :
    stepOp (structuredRowRelabelOp tag op) (structuredRowRelabelCfg tag c) =
      structuredRowRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [structuredRowRelabelOp, structuredRowRelabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneStructuredRow_op_prefix
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (label : AffineExactlyOnePrefixLabel labelWidth stateWidth)
    (hexit : label ≠ .finish) :
    (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts).op (.inl label) =
      structuredRowRelabelOp .inl
        ((affineExactlyOnePrefixRevProgram labelWidth stateWidth).op label) := by
  cases label <;>
    simp_all [affineExactlyOneStructuredRowRevProgram]

private theorem affineExactlyOneStructuredRow_op_stacks
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (label : (affineExactlyOneStackFamilyRevProgram cellCounts).Label) :
    (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts).op (.inr label) =
      structuredRowRelabelOp .inr
        ((affineExactlyOneStackFamilyRevProgram cellCounts).op label) := by
  rfl

private theorem liftStructuredRowPrefix_step
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (c : BuilderCfg
      (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    (hexit : c.label ≠ some .finish) :
    step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts) (liftStructuredRowPrefixCfg c) =
      Option.map liftStructuredRowPrefixCfg
        (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth) c) := by
  unfold step
  rw [show (liftStructuredRowPrefixCfg c).label =
    c.label.map .inl by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      exact congrArg some
        (structuredRowRelabel_stepOp .inl
          ((affineExactlyOnePrefixRevProgram labelWidth stateWidth).op label) c)

private theorem liftStructuredRowStacks_step
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (c : BuilderCfg (affineExactlyOneStackFamilyRevProgram cellCounts)) :
    step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts) (liftStructuredRowStacksCfg c) =
      Option.map liftStructuredRowStacksCfg
        (step (affineExactlyOneStackFamilyRevProgram cellCounts) c) := by
  unfold step
  rw [show (liftStructuredRowStacksCfg c).label =
    c.label.map .inr by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      exact congrArg some
        (structuredRowRelabel_stepOp .inr
          ((affineExactlyOneStackFamilyRevProgram cellCounts).op label) c)

private theorem structuredRow_iterate_bind_none {σ : Type}
    (f : σ → Option σ) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem structuredRow_haltExit_no_return
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
      rw [hnone, structuredRow_iterate_bind_none]
      simp

private theorem structuredRow_lift_iterations_to_haltExit
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg
      (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts))
    (hstep : ∀ c, c.label ≠ some exit →
      step (affineExactlyOneStructuredRowRevProgram
          labelWidth stateWidth cellCounts) (tr c) =
        Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineExactlyOneStructuredRowRevProgram
          labelWidth stateWidth cellCounts)))^[n]
        (some (tr a)) = some (tr b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step P))^[n] (step P a) = some b at h
      change (flip Option.bind
        (step (affineExactlyOneStructuredRowRevProgram
          labelWidth stateWidth cellCounts)))^[n]
          (step (affineExactlyOneStructuredRowRevProgram
            labelWidth stateWidth cellCounts) (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact structuredRow_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, structuredRow_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem structuredRow_lift_iterations
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tr : BuilderCfg P → BuilderCfg
      (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts))
    (hstep : ∀ c,
      step (affineExactlyOneStructuredRowRevProgram
          labelWidth stateWidth cellCounts) (tr c) =
        Option.map tr (step P c)) :
    ∀ {a b : BuilderCfg P} (n : Nat),
      (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineExactlyOneStructuredRowRevProgram
          labelWidth stateWidth cellCounts)))^[n]
        (some (tr a)) = some (tr b) := by
  intro a b n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step P))^[n] (step P a) = some b at h
      change (flip Option.bind
        (step (affineExactlyOneStructuredRowRevProgram
          labelWidth stateWidth cellCounts)))^[n]
          (step (affineExactlyOneStructuredRowRevProgram
            labelWidth stateWidth cellCounts) (tr a)) = some (tr b)
      rw [hstep]
      cases hsource : step P a with
      | none =>
          rw [hsource, structuredRow_iterate_bind_none] at h
          contradiction
      | some c =>
          simp only [Option.map_some]
          rw [hsource] at h
          exact ih h

private def affineExactlyOneStructuredRow_prefix_run
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts))
      (liftStructuredRowPrefixCfg
        (affineExactlyOnePrefixLoadedCfg labelWidth stateWidth height start
          rowBase input output))
      (some (liftStructuredRowPrefixCfg
        (affineExactlyOnePrefixFinishCfg labelWidth stateWidth height start
          rowBase input
          ((encodeAffineExactlyOneCompactFamily
            (affineExactlyOnePrefixFrames labelWidth stateWidth start rowBase)
            ).reverse ++ output))))
      (affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase) := by
  have sourceRun := affineExactlyOnePrefix_runToFinish
    labelWidth stateWidth height start rowBase input output
  have htarget :
      (affineExactlyOnePrefixFinishCfg labelWidth stateWidth height start
        rowBase input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOnePrefixFrames labelWidth stateWidth start rowBase)
          ).reverse ++ output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact structuredRow_lift_iterations_to_haltExit
    (AffineExactlyOnePrefixLabel.finish
      (labelWidth := labelWidth) (stateWidth := stateWidth)) rfl
    liftStructuredRowPrefixCfg liftStructuredRowPrefix_step htarget
      sourceRun.steps sourceRun.evals_in_steps

private def affineExactlyOneStructuredRow_stacks_run
    {labelWidth stateWidth : Nat} {cellCounts : List Nat}
    {a b : BuilderCfg (affineExactlyOneStackFamilyRevProgram cellCounts)}
    {steps : Nat}
    (sourceRun : EvalsToInTime
      (step (affineExactlyOneStackFamilyRevProgram cellCounts))
      a (some b) steps) :
    EvalsToInTime
      (step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts))
      (liftStructuredRowStacksCfg a)
      (some (liftStructuredRowStacksCfg b)) steps := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact structuredRow_lift_iterations liftStructuredRowStacksCfg
    liftStructuredRowStacks_step sourceRun.steps sourceRun.evals_in_steps

/-- Exact runtime of the complete structured-row source. -/
def affineExactlyOneStructuredRowSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) : Nat :=
  affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase + 1 +
    affineExactlyOneStackFamilySteps cellCounts height
      (affineExactlyOneStructuredRowStackStart labelWidth stateWidth start)
      (affineExactlyOneStructuredRowStackBase labelWidth stateWidth rowBase)

/-- Fixed coefficient for a complete structured-row quadratic bound. -/
def affineExactlyOneStructuredRowStepCoeff
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) : Nat :=
  31 * (labelWidth + stateWidth + 2) +
    affineExactlyOneStackFamilyStepCoeff cellCounts *
      (5 * (labelWidth + stateWidth + 2)) ^ 2

/-- A complete structured row is quadratic in the loaded runtime height and
two affine offsets. -/
theorem affineExactlyOneStructuredRowSteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) :
    affineExactlyOneStructuredRowSteps labelWidth stateWidth cellCounts
        height start rowBase ≤
      affineExactlyOneStructuredRowStepCoeff
        labelWidth stateWidth cellCounts *
          (height + start + rowBase + 1) ^ 2 := by
  let payload := height + start + rowBase + 1
  let stackStart := affineExactlyOneStructuredRowStackStart
    labelWidth stateWidth start
  let stackBase := affineExactlyOneStructuredRowStackBase
    labelWidth stateWidth rowBase
  let stackPayload := height + stackStart + stackBase + 1
  let scale := 5 * (labelWidth + stateWidth + 2)
  have hpayload : 1 ≤ payload := by simp [payload]
  have hprefSource := affineExactlyOnePrefixSteps_le
    labelWidth stateWidth start rowBase
  have hpref :
      affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase + 1 ≤
        31 * (labelWidth + stateWidth + 2) * payload ^ 2 := by
    have hsourcePayload : start + rowBase + 1 ≤ payload := by
      dsimp only [payload]
      omega
    have hpayloadSquare : payload ≤ payload ^ 2 := by nlinarith
    have hmain :
        affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase ≤
          30 * (labelWidth + stateWidth + 2) * payload ^ 2 :=
      hprefSource.trans <| (Nat.mul_le_mul_left
        (30 * (labelWidth + stateWidth + 2)) hsourcePayload).trans <|
          Nat.mul_le_mul_left
            (30 * (labelWidth + stateWidth + 2)) hpayloadSquare
    have hone : 1 ≤ (labelWidth + stateWidth + 2) * payload ^ 2 := by
      nlinarith
    calc
      affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase + 1 ≤
          30 * (labelWidth + stateWidth + 2) * payload ^ 2 +
            (labelWidth + stateWidth + 2) * payload ^ 2 :=
        Nat.add_le_add hmain hone
      _ = 31 * (labelWidth + stateWidth + 2) * payload ^ 2 := by ring
  have hstackPayload : stackPayload ≤ scale * payload := by
    dsimp only [stackPayload, stackStart, stackBase, scale, payload]
    simp only [affineExactlyOneStructuredRowStackStart,
      affineExactlyOneStructuredRowStackBase]
    nlinarith
  have hsquare : stackPayload ^ 2 ≤ scale ^ 2 * payload ^ 2 := by
    nlinarith
  have hstackSource := affineExactlyOneStackFamilySteps_le
    cellCounts height stackStart stackBase
  have hstack : affineExactlyOneStackFamilySteps cellCounts height
      stackStart stackBase ≤
      affineExactlyOneStackFamilyStepCoeff cellCounts *
        (scale ^ 2 * payload ^ 2) := by
    exact hstackSource.trans
      (Nat.mul_le_mul_left
        (affineExactlyOneStackFamilyStepCoeff cellCounts) hsquare)
  calc
    affineExactlyOneStructuredRowSteps labelWidth stateWidth cellCounts
        height start rowBase =
        (affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase + 1) +
          affineExactlyOneStackFamilySteps cellCounts height
            stackStart stackBase := by
      simp [affineExactlyOneStructuredRowSteps, stackStart, stackBase]
    _ ≤ 31 * (labelWidth + stateWidth + 2) * payload ^ 2 +
          affineExactlyOneStackFamilyStepCoeff cellCounts *
            (scale ^ 2 * payload ^ 2) := Nat.add_le_add hpref hstack
    _ = affineExactlyOneStructuredRowStepCoeff
          labelWidth stateWidth cellCounts * payload ^ 2 := by
      simp [affineExactlyOneStructuredRowStepCoeff, scale]
      ring

private theorem structuredRow_encode_append
    (left right : List AffineExactlyOneFrame) :
    encodeAffineExactlyOneCompactFamily (left ++ right) =
      encodeAffineExactlyOneCompactFamily left ++
        encodeAffineExactlyOneCompactFamily right := by
  induction left with
  | nil => rfl
  | cons frame rest ih =>
      simp [encodeAffineExactlyOneCompactFamily, ih, List.append_assoc]

/-- The single row controller emits the prefix and every stack block in exact
canonical structured order, preserving the runtime height. -/
def affineExactlyOneStructuredRow_runToFinish
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts))
      (affineExactlyOneStructuredRowLoadedCfg labelWidth stateWidth cellCounts
        height start rowBase input output)
      (some (affineExactlyOneStructuredRowFinishCfg labelWidth stateWidth
        cellCounts height start rowBase input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowFrames labelWidth stateWidth
            cellCounts height start rowBase)).reverse ++ output)))
      (affineExactlyOneStructuredRowSteps labelWidth stateWidth cellCounts
        height start rowBase) := by
  let stackStart :=
    affineExactlyOneStructuredRowStackStart labelWidth stateWidth start
  let stackBase :=
    affineExactlyOneStructuredRowStackBase labelWidth stateWidth rowBase
  let prefixFrames :=
    affineExactlyOnePrefixFrames labelWidth stateWidth start rowBase
  let stackFrames :=
    affineExactlyOneStackFamilyFrames cellCounts height stackStart stackBase
  let prefixOutput :=
    (encodeAffineExactlyOneCompactFamily prefixFrames).reverse ++ output
  let finalOutput :=
    (encodeAffineExactlyOneCompactFamily stackFrames).reverse ++ prefixOutput
  let prefixStart := liftStructuredRowPrefixCfg (cellCounts := cellCounts)
    (affineExactlyOnePrefixLoadedCfg labelWidth stateWidth height start
      rowBase input output)
  let prefixDone := liftStructuredRowPrefixCfg (cellCounts := cellCounts)
    (affineExactlyOnePrefixFinishCfg labelWidth stateWidth height start
      rowBase input prefixOutput)
  let stacksStart := liftStructuredRowStacksCfg
    (labelWidth := labelWidth) (stateWidth := stateWidth)
    (affineExactlyOneStackFamilyLoadedCfg cellCounts height stackStart
      stackBase input prefixOutput)
  let stacksDone := liftStructuredRowStacksCfg
    (labelWidth := labelWidth) (stateWidth := stateWidth)
    (affineExactlyOneStackFamilyFinishCfg cellCounts height stackStart
      stackBase input finalOutput)
  have hprefix : EvalsToInTime
      (step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts)) prefixStart (some prefixDone)
      (affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase) := by
    simpa [prefixStart, prefixDone, prefixFrames, prefixOutput] using
      affineExactlyOneStructuredRow_prefix_run (cellCounts := cellCounts)
        height start rowBase input output
  have hbridge : EvalsToInTime
      (step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts)) prefixDone (some stacksStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hstacksSource := affineExactlyOneStackFamily_runToFinish cellCounts
    height stackStart stackBase input prefixOutput
  have hstacks : EvalsToInTime
      (step (affineExactlyOneStructuredRowRevProgram
        labelWidth stateWidth cellCounts)) stacksStart (some stacksDone)
      (affineExactlyOneStackFamilySteps cellCounts height stackStart
        stackBase) := by
    simpa [stacksStart, stacksDone, stackFrames, finalOutput] using
      affineExactlyOneStructuredRow_stacks_run
        (labelWidth := labelWidth) (stateWidth := stateWidth) hstacksSource
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts)) _ 1 _ prefixDone _ hprefix hbridge
  let full := EvalsToInTime.trans
    (step (affineExactlyOneStructuredRowRevProgram
      labelWidth stateWidth cellCounts)) _ _ _ stacksStart _ h₁ hstacks
  convert full using 1
  · rfl
  · simp [stacksDone, liftStructuredRowStacksCfg, structuredRowRelabelCfg,
      affineExactlyOneStructuredRowFinishCfg,
      affineExactlyOneStackFamilyFinishCfg,
      affineExactlyOneStackFamilyCfg,
      affineExactlyOneStructuredRowCfg, affineExactlyOneStructuredRowFrames,
      structuredRow_encode_append, finalOutput, stackFrames, prefixOutput,
      prefixFrames, List.reverse_append, List.append_assoc,
      stackStart, stackBase]
  · simp [affineExactlyOneStructuredRowSteps, stackStart, stackBase]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
