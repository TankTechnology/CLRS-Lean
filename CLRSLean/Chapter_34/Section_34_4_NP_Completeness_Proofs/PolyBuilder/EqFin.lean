import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.FiniteFamily

/-!
# Runtime finite-family equality serialization

One fixed controller reads a runtime list of coordinate frames.  For every
coordinate it loads and executes the established five-gate Boolean equality,
then loads and executes the one-gate aggregate conjunction.  The controller
therefore emits the exact ordered `eqFinGateTrace`, not merely a stream with
the same length.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Runtime data for one equality coordinate.  `matched` is the output wire
of the preceding Boolean equality and `previous` is the aggregate seed/carry
wire. -/
structure AffineEqFinPairFrame where
  eqStart : Nat
  left : Nat
  right : Nat
  matched : Nat
  previous : Nat
deriving DecidableEq, Repr

/-- Delimiter-bearing input for one coordinate.  A leading `frameEnd` marks
the presence of a pair; the two later `frameEnd`s delimit the Boolean-equality
and conjunction component calls. -/
def encodeAffineEqFinPairFrame (frame : AffineEqFinPairFrame) :
    List UnaryFrameSym :=
  [.frameEnd] ++
    encodeUnaryFrame [frame.eqStart, frame.left, frame.right] ++
    [.frameEnd] ++
    encodeUnaryFrame [frame.matched, 0, frame.previous] ++
    [.frameEnd]

/-- Runtime input for a finite coordinate family. -/
def encodeAffineEqFinFrames (frames : List AffineEqFinPairFrame) :
    List UnaryFrameSym :=
  frames.flatMap encodeAffineEqFinPairFrame

/-- Exact forward gate stream for arbitrary explicit coordinate frames. -/
def affineEqFinGateStream (frames : List AffineEqFinPairFrame) :
    List CircuitSym :=
  .constTrueMark :: frames.flatMap fun frame =>
    affineBoolEqGateStream frame.eqStart frame.left frame.right ++
      affineAndGateStream frame.matched frame.previous

/-- Structural relabeling of a component instruction. -/
private def eqFinRelabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
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

/-- Fixed finite-control phases of the complete finite-family equality
serializer. -/
inductive AffineEqFinLabel
  | seed | check | clearMarker
  | boolLoader (label : UnaryTripleLoaderLabel)
  | boolEq (label : AffineExactlyOneFamilyLabel)
  | andLoader (label : UnaryTripleLoaderLabel)
  | andCore (label : AffineExactlyOneFamilyLabel)
  | finish | invalid
deriving DecidableEq, Fintype

/-- One program handles every family length and every wire index; all such
values are supplied by the runtime frame. -/
def affineEqFinRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineEqFinLabel
  main := .seed
  op
    | .seed => .pushOutput .constTrueMark .check
    | .check => .popInput .finish fun
        | .frameEnd => .clearMarker
        | _ => .invalid
    | .clearMarker =>
        .popWork₁ (.boolLoader unaryTripleLoaderProgram.main) (fun _ => .invalid)
    | .boolLoader .ready =>
        .popWork₁ (.boolEq (.kernel (.boolEq .notLeft))) (fun _ => .invalid)
    | .boolLoader label => eqFinRelabelOp .boolLoader
        (unaryTripleLoaderProgram.op label)
    | .boolEq .finish =>
        .popWork₁ (.andLoader unaryTripleLoaderProgram.main) (fun _ => .invalid)
    | .boolEq label => eqFinRelabelOp .boolEq
        (affineExactlyOneFamilyRevProgram.op label)
    | .andLoader .ready =>
        .popWork₁ (.andCore (.kernel (.conjunction .push))) (fun _ => .invalid)
    | .andLoader label => eqFinRelabelOp .andLoader
        (unaryTripleLoaderProgram.op label)
    | .andCore .finish => .popWork₁ .check (fun _ => .invalid)
    | .andCore label => eqFinRelabelOp .andCore
        (affineExactlyOneFamilyRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

/-- Fieldwise configuration surface for the equality controller. -/
def affineEqFinCfg (label : AffineEqFinLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineEqFinRevProgram where
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

/-- Clean public entry for one complete runtime family. -/
def affineEqFinLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineEqFinRevProgram :=
  affineEqFinCfg .seed none none false input output [] [] [] [] []

/-- Clean family loop after the true seed has been emitted. -/
def affineEqFinCheckCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineEqFinRevProgram :=
  affineEqFinCfg .check none none false input output [] [] [] [] []

/-- Redirectable clean exit after the last coordinate. -/
def affineEqFinFinishCfg (output : List CircuitSym) :
    BuilderCfg affineEqFinRevProgram :=
  affineEqFinCfg .finish none none false [] output [] [] [] [] []

private def relabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineEqFinLabel) (c : BuilderCfg P) :
    BuilderCfg affineEqFinRevProgram where
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

private def liftBoolLoaderCfg (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineEqFinRevProgram := relabelCfg .boolLoader c

private def liftBoolEqCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineEqFinRevProgram := relabelCfg .boolEq c

private def liftAndLoaderCfg (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineEqFinRevProgram := relabelCfg .andLoader c

private def liftAndCfg
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineEqFinRevProgram := relabelCfg .andCore c

private theorem relabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineEqFinLabel)
    (op : Op UnaryFrameSym CircuitSym P.Label) (c : BuilderCfg P) :
    stepOp (eqFinRelabelOp tag op) (relabelCfg tag c) =
      relabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [eqFinRelabelOp, relabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineEqFin_op_boolLoader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineEqFinRevProgram.op (.boolLoader label) =
      eqFinRelabelOp .boolLoader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineEqFinRevProgram] <;> rfl

private theorem affineEqFin_op_boolEq
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineEqFinRevProgram.op (.boolEq label) =
      eqFinRelabelOp .boolEq (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineEqFinRevProgram] <;> rfl

private theorem affineEqFin_op_andLoader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineEqFinRevProgram.op (.andLoader label) =
      eqFinRelabelOp .andLoader (unaryTripleLoaderProgram.op label) := by
  cases label <;> simp_all [affineEqFinRevProgram] <;> rfl

private theorem affineEqFin_op_andCore
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineEqFinRevProgram.op (.andCore label) =
      eqFinRelabelOp .andCore (affineExactlyOneFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineEqFinRevProgram] <;> rfl

private theorem liftBoolLoader_step
    (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineEqFinRevProgram (liftBoolLoaderCfg c) =
      Option.map liftBoolLoaderCfg (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftBoolLoaderCfg c).label = c.label.map .boolLoader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineEqFin_op_boolLoader label hlabelExit]
      exact congrArg some
        (relabel_stepOp .boolLoader (unaryTripleLoaderProgram.op label) c)

private theorem liftBoolEq_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineEqFinRevProgram (liftBoolEqCfg c) =
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
      rw [affineEqFin_op_boolEq label hlabelExit]
      exact congrArg some
        (relabel_stepOp .boolEq
          (affineExactlyOneFamilyRevProgram.op label) c)

private theorem liftAndLoader_step
    (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineEqFinRevProgram (liftAndLoaderCfg c) =
      Option.map liftAndLoaderCfg (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftAndLoaderCfg c).label = c.label.map .andLoader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineEqFin_op_andLoader label hlabelExit]
      exact congrArg some
        (relabel_stepOp .andLoader (unaryTripleLoaderProgram.op label) c)

private theorem liftAnd_step
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineEqFinRevProgram (liftAndCfg c) =
      Option.map liftAndCfg
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftAndCfg c).label = c.label.map .andCore by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineEqFin_op_andCore label hlabelExit]
      exact congrArg some
        (relabel_stepOp .andCore
          (affineExactlyOneFamilyRevProgram.op label) c)

private theorem iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem haltExit_no_return
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
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
      rw [hnone, iterate_bind_none]
      simp

private theorem lift_iterations_to_haltExit
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg affineEqFinRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineEqFinRevProgram (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineEqFinRevProgram))^[n]
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
      change (flip Option.bind (step affineEqFinRevProgram))^[n]
        (step affineEqFinRevProgram (tr a)) = some (tr b)
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

private def affineEqFin_boolLoader_run (frame : AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (liftBoolLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [frame.eqStart, frame.left, frame.right] ++
          .frameEnd :: tail) output [] [] [] [] []))
      (some (liftBoolLoaderCfg (unaryTripleLoaderReadyCfg
        frame.eqStart frame.left frame.right (.frameEnd :: tail)
        output [] [])))
      (unaryTripleLoaderSteps frame.eqStart frame.left frame.right) := by
  have sourceRun := unaryTripleLoader_run
    frame.eqStart frame.left frame.right (.frameEnd :: tail) output [] []
  have htarget : (unaryTripleLoaderReadyCfg
      frame.eqStart frame.left frame.right (.frameEnd :: tail)
      output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    liftBoolLoaderCfg liftBoolLoader_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineEqFin_andLoader_run (frame : AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (liftAndLoaderCfg (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [frame.matched, 0, frame.previous] ++
          .frameEnd :: tail) output [] [] [] [] []))
      (some (liftAndLoaderCfg (unaryTripleLoaderReadyCfg
        frame.matched 0 frame.previous (.frameEnd :: tail)
        output [] [])))
      (unaryTripleLoaderSteps frame.matched 0 frame.previous) := by
  have sourceRun := unaryTripleLoader_run
    frame.matched 0 frame.previous (.frameEnd :: tail) output [] []
  have htarget : (unaryTripleLoaderReadyCfg
      frame.matched 0 frame.previous (.frameEnd :: tail)
      output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    liftAndLoaderCfg liftAndLoader_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineEqFin_boolEq_run (frame : AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (liftBoolEqCfg (affineExactlyOneFamilyBoolEqReadyCfg
        frame.eqStart frame.left frame.right tail output))
      (some (liftBoolEqCfg (affineExactlyOneFamilyFinishCfg tail
        ((affineBoolEqGateStream frame.eqStart frame.left frame.right).reverse ++
          output))))
      (affineExactlyOneFamilyBoolEqUntilFinishSteps
        frame.eqStart frame.left frame.right) := by
  have sourceRun := affineExactlyOneFamily_boolEq_runToFinish
    frame.eqStart frame.left frame.right tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineBoolEqGateStream frame.eqStart frame.left frame.right).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftBoolEqCfg liftBoolEq_step htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineEqFin_and_run (frame : AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (liftAndCfg (affineExactlyOneFamilyAndReadyCfg
        frame.matched frame.previous tail output))
      (some (liftAndCfg (affineExactlyOneFamilyFinishCfg tail
        ((affineAndGateStream frame.matched frame.previous).reverse ++
          output))))
      (affineExactlyOneFamilyAndUntilFinishSteps
        frame.matched frame.previous) := by
  have sourceRun := affineExactlyOneFamily_and_runToFinish
    frame.matched frame.previous tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineAndGateStream frame.matched frame.previous).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    liftAndCfg liftAnd_step htarget sourceRun.steps sourceRun.evals_in_steps

/-- Exact cost of one marked coordinate frame, including both loaders,
component calls, and the six fixed bridge instructions. -/
def affineEqFinPairSteps (frame : AffineEqFinPairFrame) : Nat :=
  6 + unaryTripleLoaderSteps frame.eqStart frame.left frame.right +
    affineExactlyOneFamilyBoolEqUntilFinishSteps
      frame.eqStart frame.left frame.right +
    unaryTripleLoaderSteps frame.matched 0 frame.previous +
    affineExactlyOneFamilyAndUntilFinishSteps frame.matched frame.previous

private def affineEqFinPair_run (frame : AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinCheckCfg (encodeAffineEqFinPairFrame frame ++ tail) output)
      (some (affineEqFinCheckCfg tail
        (((affineBoolEqGateStream frame.eqStart frame.left frame.right ++
          affineAndGateStream frame.matched frame.previous)).reverse ++ output)))
      (affineEqFinPairSteps frame) := by
  let andInput :=
    encodeUnaryFrame [frame.matched, 0, frame.previous] ++ .frameEnd :: tail
  let boolInput :=
    encodeUnaryFrame [frame.eqStart, frame.left, frame.right] ++
      .frameEnd :: andInput
  let boolOutput :=
    (affineBoolEqGateStream frame.eqStart frame.left frame.right).reverse ++
      output
  let finalOutput :=
    (affineAndGateStream frame.matched frame.previous).reverse ++ boolOutput
  let boolLoaderStart := liftBoolLoaderCfg
    (unaryTripleLoaderCfg .load₁ none boolInput output [] [] [] [] [])
  let boolLoaderReady := liftBoolLoaderCfg
    (unaryTripleLoaderReadyCfg frame.eqStart frame.left frame.right
      (.frameEnd :: andInput) output [] [])
  let boolEqStart := liftBoolEqCfg
    (affineExactlyOneFamilyBoolEqReadyCfg
      frame.eqStart frame.left frame.right andInput output)
  let boolEqDone := liftBoolEqCfg
    (affineExactlyOneFamilyFinishCfg andInput boolOutput)
  let andLoaderStart := liftAndLoaderCfg
    (unaryTripleLoaderCfg .load₁ none andInput boolOutput [] [] [] [] [])
  let andLoaderReady := liftAndLoaderCfg
    (unaryTripleLoaderReadyCfg frame.matched 0 frame.previous
      (.frameEnd :: tail) boolOutput [] [])
  let andStart := liftAndCfg
    (affineExactlyOneFamilyAndReadyCfg
      frame.matched frame.previous tail boolOutput)
  let andDone := liftAndCfg
    (affineExactlyOneFamilyFinishCfg tail finalOutput)
  have hmarker : EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinCheckCfg (.frameEnd :: boolInput) output)
      (some boolLoaderStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hboolLoader : EvalsToInTime (step affineEqFinRevProgram)
      boolLoaderStart (some boolLoaderReady)
      (unaryTripleLoaderSteps frame.eqStart frame.left frame.right) := by
    simpa [boolLoaderStart, boolLoaderReady, boolInput] using
      affineEqFin_boolLoader_run frame andInput output
  have hboolBridge : EvalsToInTime (step affineEqFinRevProgram)
      boolLoaderReady (some boolEqStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hbool : EvalsToInTime (step affineEqFinRevProgram)
      boolEqStart (some boolEqDone)
      (affineExactlyOneFamilyBoolEqUntilFinishSteps
        frame.eqStart frame.left frame.right) := by
    simpa [boolEqStart, boolEqDone, boolOutput] using
      affineEqFin_boolEq_run frame andInput output
  have htoAndLoader : EvalsToInTime (step affineEqFinRevProgram)
      boolEqDone (some andLoaderStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have handLoader : EvalsToInTime (step affineEqFinRevProgram)
      andLoaderStart (some andLoaderReady)
      (unaryTripleLoaderSteps frame.matched 0 frame.previous) := by
    simpa [andLoaderStart, andLoaderReady, andInput] using
      affineEqFin_andLoader_run frame tail boolOutput
  have handBridge : EvalsToInTime (step affineEqFinRevProgram)
      andLoaderReady (some andStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hand : EvalsToInTime (step affineEqFinRevProgram)
      andStart (some andDone)
      (affineExactlyOneFamilyAndUntilFinishSteps
        frame.matched frame.previous) := by
    simpa [andStart, andDone, finalOutput] using
      affineEqFin_and_run frame tail boolOutput
  have hloop : EvalsToInTime (step affineEqFinRevProgram)
      andDone (some (affineEqFinCheckCfg tail finalOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineEqFinRevProgram) 2 _ _
    boolLoaderStart _ hmarker hboolLoader
  let t₂ := EvalsToInTime.trans (step affineEqFinRevProgram) _ 1 _
    boolLoaderReady _ t₁ hboolBridge
  let t₃ := EvalsToInTime.trans (step affineEqFinRevProgram) _ _ _
    boolEqStart _ t₂ hbool
  let t₄ := EvalsToInTime.trans (step affineEqFinRevProgram) _ 1 _
    boolEqDone _ t₃ htoAndLoader
  let t₅ := EvalsToInTime.trans (step affineEqFinRevProgram) _ _ _
    andLoaderStart _ t₄ handLoader
  let t₆ := EvalsToInTime.trans (step affineEqFinRevProgram) _ 1 _
    andLoaderReady _ t₅ handBridge
  let t₇ := EvalsToInTime.trans (step affineEqFinRevProgram) _ _ _
    andStart _ t₆ hand
  let full := EvalsToInTime.trans (step affineEqFinRevProgram) _ 1 _
    andDone _ t₇ hloop
  convert full using 1
  · simp [encodeAffineEqFinPairFrame, boolInput, andInput,
      List.append_assoc]
  · simp [finalOutput, boolOutput, List.reverse_append, List.append_assoc]
  · unfold affineEqFinPairSteps
    omega

/-- Exact body runtime that consumes only the encoded equality frames and
stops before inspecting an arbitrary following suffix. -/
def affineEqFinBodySteps : List AffineEqFinPairFrame → Nat
  | [] => 0
  | frame :: rest => affineEqFinPairSteps frame + affineEqFinBodySteps rest

/-- Execute equality frames while preserving an arbitrary unary suffix and
return to the clean coordinate check. -/
def affineEqFinFrames_runToCheck (frames : List AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinCheckCfg (encodeAffineEqFinFrames frames ++ tail) output)
      (some (affineEqFinCheckCfg tail
        (((frames.flatMap fun frame =>
          affineBoolEqGateStream frame.eqStart frame.left frame.right ++
            affineAndGateStream frame.matched frame.previous)).reverse ++
          output)))
      (affineEqFinBodySteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        ((affineBoolEqGateStream frame.eqStart frame.left frame.right ++
          affineAndGateStream frame.matched frame.previous)).reverse ++ output
      have hframe := affineEqFinPair_run frame
        (encodeAffineEqFinFrames rest ++ tail) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineEqFinRevProgram)
        (affineEqFinPairSteps frame) (affineEqFinBodySteps rest) _
        (affineEqFinCheckCfg
          (encodeAffineEqFinFrames rest ++ tail) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [encodeAffineEqFinFrames, List.append_assoc]
      · simp [frameOutput, List.reverse_append, List.append_assoc]
      · simp [affineEqFinBodySteps]
        omega

/-- Execute a complete equality phase while preserving an arbitrary unary
suffix at the clean coordinate check. -/
def affineEqFin_runToCheck (frames : List AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinLoopCfg
        (encodeAffineEqFinFrames frames ++ tail) output)
      (some (affineEqFinCheckCfg tail
        ((affineEqFinGateStream frames).reverse ++ output)))
      (1 + affineEqFinBodySteps frames) := by
  let seeded := .constTrueMark :: output
  have hseed : EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinLoopCfg
        (encodeAffineEqFinFrames frames ++ tail) output)
      (some (affineEqFinCheckCfg
        (encodeAffineEqFinFrames frames ++ tail) seeded)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hframes := affineEqFinFrames_runToCheck frames tail seeded
  let full := EvalsToInTime.trans (step affineEqFinRevProgram)
    1 (affineEqFinBodySteps frames) _
    (affineEqFinCheckCfg
      (encodeAffineEqFinFrames frames ++ tail) seeded) _
    hseed hframes
  convert full using 1
  · simp [affineEqFinGateStream, seeded, List.reverse_append,
      List.append_assoc]
  · omega

/-- Exact recursive runtime after the initial true seed. -/
def affineEqFinFoldSteps : List AffineEqFinPairFrame → Nat
  | [] => 1
  | frame :: rest => affineEqFinPairSteps frame + affineEqFinFoldSteps rest

private def affineEqFinFrames_run (frames : List AffineEqFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinCheckCfg (encodeAffineEqFinFrames frames) output)
      (some (affineEqFinFinishCfg
        (((frames.flatMap fun frame =>
          affineBoolEqGateStream frame.eqStart frame.left frame.right ++
            affineAndGateStream frame.matched frame.previous)).reverse ++
          output)))
      (affineEqFinFoldSteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        ((affineBoolEqGateStream frame.eqStart frame.left frame.right ++
          affineAndGateStream frame.matched frame.previous)).reverse ++ output
      have hframe := affineEqFinPair_run frame
        (encodeAffineEqFinFrames rest) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineEqFinRevProgram)
        (affineEqFinPairSteps frame) (affineEqFinFoldSteps rest) _
        (affineEqFinCheckCfg (encodeAffineEqFinFrames rest) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [encodeAffineEqFinFrames, List.append_assoc]
      · simp [frameOutput, List.reverse_append, List.append_assoc]
      · simp [affineEqFinFoldSteps]
        omega

/-- Exact contextual runtime through the public finish label. -/
def affineEqFinUntilFinishSteps (frames : List AffineEqFinPairFrame) : Nat :=
  affineEqFinFoldSteps frames + 1

/-- Execute an arbitrary explicit equality family with one fixed program. -/
def affineEqFin_runToFinish (frames : List AffineEqFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinLoopCfg (encodeAffineEqFinFrames frames) output)
      (some (affineEqFinFinishCfg
        ((affineEqFinGateStream frames).reverse ++ output)))
      (affineEqFinUntilFinishSteps frames) := by
  let seeded := .constTrueMark :: output
  have hseed : EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinLoopCfg (encodeAffineEqFinFrames frames) output)
      (some (affineEqFinCheckCfg (encodeAffineEqFinFrames frames) seeded)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hframes := affineEqFinFrames_run frames seeded
  let full := EvalsToInTime.trans (step affineEqFinRevProgram)
    1 (affineEqFinFoldSteps frames) _
    (affineEqFinCheckCfg (encodeAffineEqFinFrames frames) seeded) _
    hseed hframes
  convert full using 1
  · simp [affineEqFinGateStream, seeded, List.reverse_append,
      List.append_assoc]
  · simp [affineEqFinUntilFinishSteps]

/-! ## Canonical frames and semantic trace agreement -/

/-- Canonical runtime frames for the recursive semantic `eqFin` trace. -/
def affineEqFinCanonicalFrames (start : Nat) :
    (n : Nat) →
      (left right : Fin n → CookLevin.CircuitBuilder.Wire) →
        List AffineEqFinPairFrame
  | 0, _, _ => []
  | n + 1, left, right =>
      affineEqFinCanonicalFrames start n
          (fun i => left i.castSucc) (fun i => right i.castSucc) ++
        [{ eqStart := start + 1 + 6 * n
           left := left (Fin.last n)
           right := right (Fin.last n)
           matched := start + 5 + 6 * n
           previous := start + 6 * n }]

private theorem eqFinBodyGateTrace_wire_canonical (start : Nat) :
    (n : Nat) →
      (left right : Fin n → CookLevin.CircuitBuilder.Wire) →
      (CircuitBuilder.eqFinBodyGateTrace (start + 1) start n left right).wire =
        start + 6 * n := by
  intro n
  induction n with
  | zero =>
      intro left right
      rfl
  | succ n ih =>
      intro left right
      simp only [CircuitBuilder.eqFinBodyGateTrace]
      simp only [CircuitBuilder.eqFinBodyGateTrace_length,
        CircuitBuilder.boolEqGateTrace_length,
        CircuitBuilder.boolEqGateTrace]
      simp only [List.length_cons, List.length_nil]
      norm_num
      ring

private theorem affineEqFinCanonicalBodyStream_eq_trace (start : Nat) :
    (n : Nat) →
      (left right : Fin n → CookLevin.CircuitBuilder.Wire) →
      (affineEqFinCanonicalFrames start n left right).flatMap (fun frame =>
        affineBoolEqGateStream frame.eqStart frame.left frame.right ++
          affineAndGateStream frame.matched frame.previous) =
      (CircuitBuilder.eqFinBodyGateTrace
        (start + 1) start n left right).gates.flatMap encodeCircuitGate := by
  intro n
  induction n with
  | zero =>
      intro left right
      rfl
  | succ n ih =>
      intro left right
      rw [show affineEqFinCanonicalFrames start (n + 1) left right =
        affineEqFinCanonicalFrames start n
            (fun i => left i.castSucc) (fun i => right i.castSucc) ++
          [{ eqStart := start + 1 + 6 * n
             left := left (Fin.last n)
             right := right (Fin.last n)
             matched := start + 5 + 6 * n
             previous := start + 6 * n }] by rfl]
      rw [List.flatMap_append, ih]
      simp only [CircuitBuilder.eqFinBodyGateTrace,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.flatMap_append]
      rw [eqFinBodyGateTrace_wire_canonical]
      simp only [CircuitBuilder.eqFinBodyGateTrace_length]
      simp [affineBoolEqGateStream, affineAndGateStream,
        CircuitBuilder.boolEqGateTrace, List.append_assoc]
      congr 2 <;> omega

/-- The fixed runtime program's canonical output is byte-for-byte the exact
ordered semantic finite-family equality trace. -/
theorem affineEqFinCanonicalGateStream_eq_trace (start : Nat) {n : Nat}
    (left right : Fin n → CookLevin.CircuitBuilder.Wire) :
    affineEqFinGateStream (affineEqFinCanonicalFrames start n left right) =
      (CircuitBuilder.eqFinGateTrace start left right).gates.flatMap
        encodeCircuitGate := by
  unfold affineEqFinGateStream CircuitBuilder.eqFinGateTrace
  rw [affineEqFinCanonicalBodyStream_eq_trace]
  rfl

/-- Standalone exact execution, including the final halt instruction. -/
def affineEqFinRevSteps (frames : List AffineEqFinPairFrame) : Nat :=
  affineEqFinUntilFinishSteps frames + 1

def affineEqFin_run (frames : List AffineEqFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinLoopCfg (encodeAffineEqFinFrames frames) output)
      (some (haltCfg affineEqFinRevProgram
        ((affineEqFinGateStream frames).reverse ++ output)))
      (affineEqFinRevSteps frames) := by
  let gateOutput := (affineEqFinGateStream frames).reverse ++ output
  have hfinish := affineEqFin_runToFinish frames output
  have hhalt : EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinFinishCfg gateOutput)
      (some (haltCfg affineEqFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineEqFinRevProgram)
    (affineEqFinUntilFinishSteps frames) 1 _
    (affineEqFinFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  convert full using 1 <;> simp [affineEqFinRevSteps, gateOutput] <;> omega

/-- Canonical fixed-controller execution specialized to the semantic
finite-family equality trace. -/
def affineEqFinCanonical_run (start : Nat) {n : Nat}
    (left right : Fin n → CookLevin.CircuitBuilder.Wire)
    (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinLoopCfg
        (encodeAffineEqFinFrames
          (affineEqFinCanonicalFrames start n left right)) output)
      (some (haltCfg affineEqFinRevProgram
        (((CircuitBuilder.eqFinGateTrace start left right).gates.flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineEqFinRevSteps
        (affineEqFinCanonicalFrames start n left right)) := by
  simpa [affineEqFinCanonicalGateStream_eq_trace] using
    affineEqFin_run (affineEqFinCanonicalFrames start n left right) output

/-- Exact unary size of one explicit coordinate frame. -/
@[simp] theorem encodeAffineEqFinPairFrame_length
    (frame : AffineEqFinPairFrame) :
    (encodeAffineEqFinPairFrame frame).length =
      frame.eqStart + frame.left + frame.right + frame.matched +
        frame.previous + 9 := by
  simp [encodeAffineEqFinPairFrame, encodeUnaryFrame_length]
  omega

/-- One coordinate runs linearly in its own delimiter-bearing unary frame. -/
theorem affineEqFinPair_steps_le (frame : AffineEqFinPairFrame) :
    affineEqFinPairSteps frame ≤
      113 * (encodeAffineEqFinPairFrame frame).length := by
  simp [affineEqFinPairSteps, unaryTripleLoaderSteps,
    affineExactlyOneFamilyBoolEqUntilFinishSteps,
    affineBoolEqRevCoreSteps,
    affineExactlyOneFamilyAndUntilFinishSteps, affineAndRevCoreSteps,
    encodeAffineEqFinPairFrame_length]
  omega

/-- The full explicit family run is linear—and hence polynomial—in its
runtime unary input length. -/
theorem affineEqFinFold_steps_le (frames : List AffineEqFinPairFrame) :
    affineEqFinFoldSteps frames ≤
      113 * (encodeAffineEqFinFrames frames).length + 1 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have hframe := affineEqFinPair_steps_le frame
      simp only [encodeAffineEqFinFrames] at ih
      simp only [affineEqFinFoldSteps, encodeAffineEqFinFrames,
        List.flatMap_cons, List.length_append]
      omega

theorem affineEqFinRev_steps_le (frames : List AffineEqFinPairFrame) :
    affineEqFinRevSteps frames ≤
      113 * (encodeAffineEqFinFrames frames).length + 3 := by
  have h := affineEqFinFold_steps_le frames
  simp [affineEqFinRevSteps, affineEqFinUntilFinishSteps]
  omega

end CLRS.Chapter34.Turing.PolyBuilder
