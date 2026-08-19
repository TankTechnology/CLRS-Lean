import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityTail

/-!
# Continuous single-row validity serialization

This controller links the raw affine exactly-one family, one halted/label
Boolean equality, and the already continuous stack/conjunction tail.  All
runtime-sized indices live in delimiter-bearing unary input; the finite
control contains only phase tags and the fixed component programs.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Runtime data for all phases of one canonical row-validity suffix. -/
structure AffineValidityRowFrame where
  oneHotFrames : List AffineExactlyOneFrame
  haltedStart : Nat
  haltedLeft : Nat
  haltedRight : Nat
  tailFrame : AffineValidityTailFrame
deriving DecidableEq, Repr

/-- Exact delimiter-bearing input owned by the whole-row controller.  The two
`frameEnd` bytes separate the one-hot family from the equality triple and the
equality kernel from the remaining validity tail. -/
def encodeAffineValidityRowFrame
    (frame : AffineValidityRowFrame) : List UnaryFrameSym :=
  encodeAffineExactlyOneFamily frame.oneHotFrames ++
    .frameEnd ::
      (encodeUnaryFrame
        [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
          .frameEnd :: encodeAffineValidityTailFrame frame.tailFrame)

/-- Exact forward byte stream of all three row-validity phases. -/
def affineValidityRowGateStream
    (frame : AffineValidityRowFrame) : List CircuitSym :=
  affineExactlyOneFamilyGateStream frame.oneHotFrames ++
    affineBoolEqGateStream
      frame.haltedStart frame.haltedLeft frame.haltedRight ++
    affineValidityTailGateStream frame.tailFrame

/-- A structural relabeling of one builder operation. -/
private def relabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
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

/-- Disjoint finite-control phases of the continuous row controller. -/
inductive AffineValidityRowLabel
  | oneHot (label : AffineExactlyOneFamilyLabel)
  | loader (label : UnaryTripleLoaderLabel)
  | boolEq (label : AffineExactlyOneFamilyLabel)
  | tail (label : AffineValidityTailLabel)
  | invalid
deriving DecidableEq, Fintype

/-- One fixed controller for every runtime row-validity frame. -/
def affineValidityRowRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineValidityRowLabel
  main := .oneHot affineExactlyOneFamilyRevProgram.main
  op
    | .oneHot .finish =>
        .popWork₁ (.loader unaryTripleLoaderProgram.main) (fun _ => .invalid)
    | .oneHot label =>
        relabelOp .oneHot (affineExactlyOneFamilyRevProgram.op label)
    | .loader .ready =>
        .popWork₁ (.boolEq (.kernel (.boolEq .notLeft))) (fun _ => .invalid)
    | .loader label => relabelOp .loader (unaryTripleLoaderProgram.op label)
    | .boolEq .finish =>
        .popWork₁ (.tail affineValidityTailRevProgram.main) (fun _ => .invalid)
    | .boolEq label =>
        relabelOp .boolEq (affineExactlyOneFamilyRevProgram.op label)
    | .tail label => relabelOp .tail (affineValidityTailRevProgram.op label)
    | .invalid => .halt

/-- Fieldwise relabeling of a component configuration into the row program. -/
private def relabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineValidityRowLabel) (c : BuilderCfg P) :
    BuilderCfg affineValidityRowRevProgram where
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

private def liftOneHotCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineValidityRowRevProgram :=
  relabelCfg .oneHot c

private def liftLoaderCfg (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineValidityRowRevProgram :=
  relabelCfg .loader c

private def liftBoolEqCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineValidityRowRevProgram :=
  relabelCfg .boolEq c

private def liftTailCfg (c : BuilderCfg affineValidityTailRevProgram) :
    BuilderCfg affineValidityRowRevProgram :=
  relabelCfg .tail c

/-- Redirectable clean exit after one complete row-validity frame. -/
def affineValidityRowFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineValidityRowRevProgram :=
  liftTailCfg (affineValidityTailFinishCfg tail output)

/-- Clean public entry for one complete runtime row. -/
def affineValidityRowLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineValidityRowRevProgram :=
  liftOneHotCfg (affineExactlyOneFamilyLoopCfg input output)

private theorem relabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineValidityRowLabel)
    (op : Op UnaryFrameSym CircuitSym P.Label) (c : BuilderCfg P) :
    stepOp (relabelOp tag op) (relabelCfg tag c) =
      relabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [relabelOp, relabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineValidityRow_op_oneHot
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineValidityRowRevProgram.op (.oneHot label) =
      relabelOp .oneHot (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineValidityRowRevProgram]
    <;> rfl

private theorem affineValidityRow_op_loader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineValidityRowRevProgram.op (.loader label) =
      relabelOp .loader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineValidityRowRevProgram]
    <;> rfl

private theorem affineValidityRow_op_boolEq
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineValidityRowRevProgram.op (.boolEq label) =
      relabelOp .boolEq (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineValidityRowRevProgram]
    <;> rfl

private theorem liftOneHot_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineValidityRowRevProgram (liftOneHotCfg c) =
      Option.map liftOneHotCfg
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftOneHotCfg c).label = c.label.map .oneHot by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineValidityRow_op_oneHot label hlabelExit]
      exact congrArg some
        (relabel_stepOp .oneHot
          (affineExactlyOneFamilyRevProgram.op label) c)

private theorem liftLoader_step (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineValidityRowRevProgram (liftLoaderCfg c) =
      Option.map liftLoaderCfg (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftLoaderCfg c).label = c.label.map .loader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineValidityRow_op_loader label hlabelExit]
      exact congrArg some
        (relabel_stepOp .loader (unaryTripleLoaderProgram.op label) c)

private theorem liftBoolEq_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineValidityRowRevProgram (liftBoolEqCfg c) =
      Option.map liftBoolEqCfg
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftBoolEqCfg c).label = c.label.map .boolEq by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineValidityRow_op_boolEq label hlabelExit]
      exact congrArg some
        (relabel_stepOp .boolEq
          (affineExactlyOneFamilyRevProgram.op label) c)

private theorem liftTail_step (c : BuilderCfg affineValidityTailRevProgram) :
    step affineValidityRowRevProgram (liftTailCfg c) =
      Option.map liftTailCfg (step affineValidityTailRevProgram c) := by
  unfold step
  rw [show (liftTailCfg c).label = c.label.map .tail by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      change some (stepOp
          (relabelOp AffineValidityRowLabel.tail
            (affineValidityTailRevProgram.op label))
          (relabelCfg AffineValidityRowLabel.tail c)) =
        some (relabelCfg AffineValidityRowLabel.tail
          (stepOp (affineValidityTailRevProgram.op label) c))
      exact congrArg some
        (relabel_stepOp .tail (affineValidityTailRevProgram.op label) c)

private theorem iterate_bind_none {σ : Type} (f : σ → Option σ)
    (n : Nat) :
    (flip Option.bind f)^[n] (none : Option σ) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem haltExit_no_return
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (a b : BuilderCfg P) (ha : a.label = some exit)
    (hb : b.label = some exit) (n : Nat) :
    (flip Option.bind (step P))^[n] (step P a) ≠ some b := by
  rcases a with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at ha
  subst label
  let halted : BuilderCfg P :=
    { label := none
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
  have hstep : step P
      { label := some exit, buffer₁ := buffer₁, buffer₂ := buffer₂,
        test := test, input := input, output := output, work₁ := work₁,
        work₂ := work₂, counter₁ := counter₁, counter₂ := counter₂,
        counter₃ := counter₃ } = some halted := by
    simp [step, hop, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step P))^[n]
        (step P halted) ≠ some b
      have hnone : step P halted = none := rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem lift_iterations_to_haltExit
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg affineValidityRowRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineValidityRowRevProgram (tr c) =
        Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineValidityRowRevProgram))^[n]
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
      change (flip Option.bind (step affineValidityRowRevProgram))^[n]
        (step affineValidityRowRevProgram (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineValidityRow_oneHot_run
    (frame : AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (affineValidityRowLoopCfg
        (encodeAffineValidityRowFrame frame ++ tail) output)
      (some (liftOneHotCfg (affineExactlyOneFamilyFinishCfg
        (encodeUnaryFrame
            [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
          .frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
        ((affineExactlyOneFamilyGateStream
          frame.oneHotFrames).reverse ++ output))))
      (affineExactlyOneFamilyUntilEndSteps frame.oneHotFrames) := by
  have sourceRun := affineExactlyOneFamily_runToFinish frame.oneHotFrames
    (encodeUnaryFrame
        [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
      .frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail)) output
  have htarget : (affineExactlyOneFamilyFinishCfg
      (encodeUnaryFrame
          [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
        .frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
      ((affineExactlyOneFamilyGateStream frame.oneHotFrames).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have lifted := lift_iterations_to_haltExit
    AffineExactlyOneFamilyLabel.finish rfl liftOneHotCfg
    liftOneHot_step htarget sourceRun.steps sourceRun.evals_in_steps
  have hsource : liftOneHotCfg (affineExactlyOneFamilyLoopCfg
      (encodeAffineExactlyOneFamily frame.oneHotFrames ++
        .frameEnd ::
          (encodeUnaryFrame
              [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
            .frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail)))
      output) = affineValidityRowLoopCfg
        (encodeAffineValidityRowFrame frame ++ tail) output := by
    simp [liftOneHotCfg, relabelCfg, affineExactlyOneFamilyLoopCfg,
      affineValidityRowLoopCfg, encodeAffineValidityRowFrame,
      List.append_assoc]
  rw [hsource] at lifted
  exact lifted

private def affineValidityRow_oneHot_bridge
    (frame : AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (liftOneHotCfg (affineExactlyOneFamilyFinishCfg
        (encodeUnaryFrame
            [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
          .frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
        output))
      (some (liftLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame
            [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
          .frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
        output [] [] [] [] []))) 1 :=
  ⟨⟨1, rfl⟩, le_rfl⟩

private def affineValidityRow_loader_run
    (frame : AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (liftLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame
            [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
          .frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
        output [] [] [] [] []))
      (some (liftLoaderCfg (unaryTripleLoaderReadyCfg
        frame.haltedStart frame.haltedLeft frame.haltedRight
        (.frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
        output [] [])))
      (unaryTripleLoaderSteps
        frame.haltedStart frame.haltedLeft frame.haltedRight) := by
  have sourceRun := unaryTripleLoader_run
    frame.haltedStart frame.haltedLeft frame.haltedRight
    (.frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
    output [] []
  have htarget : (unaryTripleLoaderReadyCfg
      frame.haltedStart frame.haltedLeft frame.haltedRight
      (.frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
      output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl liftLoaderCfg
    liftLoader_step htarget sourceRun.steps sourceRun.evals_in_steps

private def affineValidityRow_loader_bridge
    (frame : AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (liftLoaderCfg (unaryTripleLoaderReadyCfg
        frame.haltedStart frame.haltedLeft frame.haltedRight
        (.frameEnd :: (encodeAffineValidityTailFrame frame.tailFrame ++ tail))
        output [] []))
      (some (liftBoolEqCfg (affineExactlyOneFamilyBoolEqReadyCfg
        frame.haltedStart frame.haltedLeft frame.haltedRight
        (encodeAffineValidityTailFrame frame.tailFrame ++ tail) output))) 1 :=
  ⟨⟨1, rfl⟩, le_rfl⟩

private def affineValidityRow_boolEq_run
    (frame : AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (liftBoolEqCfg (affineExactlyOneFamilyBoolEqReadyCfg
        frame.haltedStart frame.haltedLeft frame.haltedRight
        (encodeAffineValidityTailFrame frame.tailFrame ++ tail) output))
      (some (liftBoolEqCfg (affineExactlyOneFamilyFinishCfg
        (encodeAffineValidityTailFrame frame.tailFrame ++ tail)
        ((affineBoolEqGateStream frame.haltedStart
          frame.haltedLeft frame.haltedRight).reverse ++ output))))
      (affineExactlyOneFamilyBoolEqUntilFinishSteps
        frame.haltedStart frame.haltedLeft frame.haltedRight) := by
  have sourceRun := affineExactlyOneFamily_boolEq_runToFinish
    frame.haltedStart frame.haltedLeft frame.haltedRight
    (encodeAffineValidityTailFrame frame.tailFrame ++ tail) output
  have htarget : (affineExactlyOneFamilyFinishCfg
      (encodeAffineValidityTailFrame frame.tailFrame ++ tail)
      ((affineBoolEqGateStream frame.haltedStart
        frame.haltedLeft frame.haltedRight).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftBoolEqCfg
    liftBoolEq_step htarget sourceRun.steps sourceRun.evals_in_steps

private def affineValidityRow_boolEq_bridge
    (frame : AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (liftBoolEqCfg (affineExactlyOneFamilyFinishCfg
        (encodeAffineValidityTailFrame frame.tailFrame ++ tail) output))
      (some (liftTailCfg (affineValidityTailLoopCfg
        (encodeAffineValidityTailFrame frame.tailFrame ++ tail) output))) 1 :=
  ⟨⟨1, rfl⟩, le_rfl⟩

private def affineValidityRow_tail_runToFinish
    (frame : AffineValidityRowFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (liftTailCfg (affineValidityTailLoopCfg
        (encodeAffineValidityTailFrame frame.tailFrame ++ tail) output))
      (some (affineValidityRowFinishCfg tail
        ((affineValidityTailGateStream frame.tailFrame).reverse ++ output)))
      (affineValidityTailUntilFinishSteps frame.tailFrame) := by
  have sourceRun := affineValidityTail_runToFinish
    frame.tailFrame tail output
  have htarget : (affineValidityTailFinishCfg tail
      ((affineValidityTailGateStream frame.tailFrame).reverse ++ output)).label =
        some (.conjunction .finish) := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have lifted := lift_iterations_to_haltExit
    (AffineValidityTailLabel.conjunction AffineConjunctionLabel.finish)
    rfl liftTailCfg (fun c _ => liftTail_step c) htarget
    sourceRun.steps sourceRun.evals_in_steps
  simpa [affineValidityRowFinishCfg] using lifted

/-- Exact contextual runtime through the redirectable row finish label. -/
def affineValidityRowUntilFinishSteps (frame : AffineValidityRowFrame) : Nat :=
  affineExactlyOneFamilyUntilEndSteps frame.oneHotFrames + 1 +
    unaryTripleLoaderSteps
      frame.haltedStart frame.haltedLeft frame.haltedRight + 1 +
    affineExactlyOneFamilyBoolEqUntilFinishSteps
      frame.haltedStart frame.haltedLeft frame.haltedRight + 1 +
    affineValidityTailUntilFinishSteps frame.tailFrame

/-- Standalone runtime, including the final halt instruction. -/
def affineValidityRowRevSteps (frame : AffineValidityRowFrame) : Nat :=
  affineValidityRowUntilFinishSteps frame + 1

/-- Execute one complete row, preserve an arbitrary unconsumed input tail,
and stop before the final halt instruction. -/
def affineValidityRow_runToFinish (frame : AffineValidityRowFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (affineValidityRowLoopCfg
        (encodeAffineValidityRowFrame frame ++ tail) output)
      (some (affineValidityRowFinishCfg tail
        ((affineValidityRowGateStream frame).reverse ++ output)))
      (affineValidityRowUntilFinishSteps frame) := by
  let oneHotOutput :=
    (affineExactlyOneFamilyGateStream frame.oneHotFrames).reverse ++ output
  let boolEqOutput :=
    (affineBoolEqGateStream frame.haltedStart
      frame.haltedLeft frame.haltedRight).reverse ++ oneHotOutput
  have honeHot := affineValidityRow_oneHot_run frame tail output
  have hbridge₁ := affineValidityRow_oneHot_bridge frame tail oneHotOutput
  have hloader := affineValidityRow_loader_run frame tail oneHotOutput
  have hbridge₂ := affineValidityRow_loader_bridge frame tail oneHotOutput
  have hboolEq := affineValidityRow_boolEq_run frame tail oneHotOutput
  have hbridge₃ := affineValidityRow_boolEq_bridge frame tail boolEqOutput
  have htail := affineValidityRow_tail_runToFinish frame tail boolEqOutput
  let t₁ := EvalsToInTime.trans (step affineValidityRowRevProgram)
    (affineExactlyOneFamilyUntilEndSteps frame.oneHotFrames) 1 _ _ _
    honeHot (by simpa [oneHotOutput] using hbridge₁)
  let t₂ := EvalsToInTime.trans (step affineValidityRowRevProgram) _
    (unaryTripleLoaderSteps
      frame.haltedStart frame.haltedLeft frame.haltedRight) _ _ _ t₁
    (by simpa [oneHotOutput] using hloader)
  let t₃ := EvalsToInTime.trans (step affineValidityRowRevProgram) _ 1
    _ _ _ t₂ (by simpa [oneHotOutput] using hbridge₂)
  let t₄ := EvalsToInTime.trans (step affineValidityRowRevProgram) _
    (affineExactlyOneFamilyBoolEqUntilFinishSteps
      frame.haltedStart frame.haltedLeft frame.haltedRight) _ _ _ t₃
    (by simpa [oneHotOutput] using hboolEq)
  let t₅ := EvalsToInTime.trans (step affineValidityRowRevProgram) _ 1
    _ _ _ t₄ (by simpa [boolEqOutput] using hbridge₃)
  let full := EvalsToInTime.trans (step affineValidityRowRevProgram) _
    (affineValidityTailUntilFinishSteps frame.tailFrame) _ _ _ t₅
    (by simpa [boolEqOutput] using htail)
  convert full using 1
  · simp [affineValidityRowFinishCfg, affineValidityRowGateStream,
      oneHotOutput, boolEqOutput, List.reverse_append, List.append_assoc]
  · unfold affineValidityRowUntilFinishSteps
    omega

/-- Execute all canonical row-validity phases in one fixed program, with no
intermediate halt and exact byte-for-byte output. -/
def affineValidityRow_run (frame : AffineValidityRowFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowRevProgram)
      (affineValidityRowLoopCfg
        (encodeAffineValidityRowFrame frame) output)
      (some (haltCfg affineValidityRowRevProgram
        ((affineValidityRowGateStream frame).reverse ++ output)))
      (affineValidityRowRevSteps frame) := by
  let gateOutput := (affineValidityRowGateStream frame).reverse ++ output
  have hfinish := affineValidityRow_runToFinish frame [] output
  have hhalt : EvalsToInTime (step affineValidityRowRevProgram)
      (affineValidityRowFinishCfg [] gateOutput)
      (some (haltCfg affineValidityRowRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineValidityRowRevProgram)
    (affineValidityRowUntilFinishSteps frame) 1
    _ (affineValidityRowFinishCfg [] gateOutput) _ hfinish hhalt
  convert full using 1
  · simp
  · simp [affineValidityRowRevSteps, Nat.add_comm]

/-- The linked row controller is quadratic in its exact delimiter-bearing
runtime frame. -/
theorem affineValidityRowRev_steps_le (frame : AffineValidityRowFrame) :
    affineValidityRowRevSteps frame ≤
      2500 * (encodeAffineValidityRowFrame frame).length ^ 2 + 20 := by
  let total := (encodeAffineValidityRowFrame frame).length
  have htotal : 1 ≤ total := by
    simp [total, encodeAffineValidityRowFrame]
    omega
  have honeHot := affineExactlyOneFamilyUntilEnd_steps_le frame.oneHotFrames
  have htail := affineValidityTailRev_steps_le frame.tailFrame
  have honeHotLen : (encodeAffineExactlyOneFamily
      frame.oneHotFrames).length ≤ total := by
    simp [total, encodeAffineValidityRowFrame]
  have htailLen : (encodeAffineValidityTailFrame
      frame.tailFrame).length ≤ total := by
    simp [total, encodeAffineValidityRowFrame]
    omega
  have htriple : frame.haltedStart + frame.haltedLeft +
      frame.haltedRight + 3 ≤ total := by
    simp [total, encodeAffineValidityRowFrame, encodeUnaryFrame_length]
    omega
  have honeHotSq := Nat.pow_le_pow_left honeHotLen 2
  have htailSq := Nat.pow_le_pow_left htailLen 2
  have hboolArg : frame.haltedStart + frame.haltedLeft +
      frame.haltedRight + 1 ≤ total := by omega
  have hboolSq := Nat.pow_le_pow_left hboolArg 2
  have hbool := affineBoolEqRev_steps_le
    frame.haltedStart frame.haltedLeft frame.haltedRight
  have hloader : unaryTripleLoaderSteps frame.haltedStart
      frame.haltedLeft frame.haltedRight ≤ 2 * total + 3 := by
    simp [unaryTripleLoaderSteps]
    omega
  have hboolFinish : affineExactlyOneFamilyBoolEqUntilFinishSteps
      frame.haltedStart frame.haltedLeft frame.haltedRight ≤
        100 * total ^ 2 + 1 := by
    have hstepEq : affineExactlyOneFamilyBoolEqUntilFinishSteps
        frame.haltedStart frame.haltedLeft frame.haltedRight =
      affineBoolEqRevSteps
        frame.haltedStart frame.haltedLeft frame.haltedRight + 1 := by
      simp [affineExactlyOneFamilyBoolEqUntilFinishSteps,
        affineBoolEqRevCoreSteps, affineBoolEqRevSteps]
    rw [hstepEq]
    exact Nat.add_le_add_right
      (hbool.trans (Nat.mul_le_mul_left 100 hboolSq)) 1
  change affineExactlyOneFamilyUntilEndSteps frame.oneHotFrames + 1 +
      unaryTripleLoaderSteps
        frame.haltedStart frame.haltedLeft frame.haltedRight + 1 +
      affineExactlyOneFamilyBoolEqUntilFinishSteps
        frame.haltedStart frame.haltedLeft frame.haltedRight + 1 +
      affineValidityTailRevSteps frame.tailFrame ≤
    2500 * (encodeAffineValidityRowFrame frame).length ^ 2 + 20
  have honeHotBound : affineExactlyOneFamilyUntilEndSteps
      frame.oneHotFrames ≤ 400 * total ^ 2 + 1 :=
    honeHot.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 400 honeHotSq) 1)
  have htailBound : affineValidityTailRevSteps frame.tailFrame ≤
      1400 * total ^ 2 + 5 :=
    htail.trans (Nat.add_le_add_right
      (Nat.mul_le_mul_left 1400 htailSq) 5)
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
