import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.FiniteFamily

/-!
# Runtime finite-family multiplexer serialization

One fixed controller reads a shared-selector header and a runtime list of
coordinate frames.  It emits the selector negation once, then three gates per
coordinate: the selected true arm, the selected false arm, and their
disjunction.  The output is the exact ordered `muxFinGateTrace`.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Runtime data for one multiplexer coordinate.  The last four fields make
the shared negation and the two fresh arm wires explicit in unary runtime
data, so the fixed finite controller never depends on a wire value. -/
structure AffineMuxFinPairFrame where
  whenTrue : Nat
  whenFalse : Nat
  selector : Nat
  selectorNot : Nat
  trueArm : Nat
  falseArm : Nat
deriving DecidableEq, Repr

/-- The selector header is a unary triple whose third counter feeds the NOT
kernel, followed by the kernel delimiter. -/
def encodeAffineMuxFinHeader (selector : Nat) : List UnaryFrameSym :=
  encodeUnaryFrame [0, 0, selector] ++ [.frameEnd]

/-- Delimiter-bearing input for one coordinate.  A leading marker records
the presence of a coordinate; the three later delimiters terminate the two
AND calls and the final OR call. -/
def encodeAffineMuxFinPairFrame (frame : AffineMuxFinPairFrame) :
    List UnaryFrameSym :=
  [.frameEnd] ++
    encodeUnaryFrame [frame.whenTrue, 0, frame.selector] ++
    [.frameEnd] ++
    encodeUnaryFrame [frame.whenFalse, 0, frame.selectorNot] ++
    [.frameEnd] ++
    encodeUnaryFrame [frame.trueArm, 0, frame.falseArm + 1] ++
    [.frameEnd]

/-- Runtime input for a finite coordinate family. -/
def encodeAffineMuxFinFrames (selector : Nat)
    (frames : List AffineMuxFinPairFrame) :
    List UnaryFrameSym :=
  encodeAffineMuxFinHeader selector ++
    frames.flatMap encodeAffineMuxFinPairFrame

/-- Exact forward gate stream for arbitrary explicit coordinate frames. -/
def affineMuxFinGateStream (selector : Nat)
    (frames : List AffineMuxFinPairFrame) :
    List CircuitSym :=
  affineNotGateStream selector ++ frames.flatMap fun frame =>
    affineAndGateStream frame.whenTrue frame.selector ++
      affineAndGateStream frame.whenFalse frame.selectorNot ++
      affineOrGateStream frame.trueArm frame.falseArm

/-- Structural relabeling of a component instruction. -/
private def muxFinRelabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
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

/-- Fixed finite-control phases of the complete finite-family multiplexer
serializer. -/
inductive AffineMuxFinStage
  | selectorNot | trueArm | falseArm | combine
deriving DecidableEq, Fintype

inductive AffineMuxFinLabel
  | check | clearMarker | orSeed
  | loader (stage : AffineMuxFinStage) (label : UnaryTripleLoaderLabel)
  | core (stage : AffineMuxFinStage)
      (label : AffineExactlyOneFamilyLabel)
  | finish | invalid
deriving DecidableEq, Fintype

/-- One program handles every family length and every wire index; all such
values are supplied by the runtime frame. -/
def affineMuxFinRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineMuxFinLabel
  main := .loader .selectorNot unaryTripleLoaderProgram.main
  op
    | .check => .popInput .finish fun
        | .frameEnd => .clearMarker
        | _ => .invalid
    | .clearMarker =>
        .popWork₁ (.loader .trueArm unaryTripleLoaderProgram.main)
          (fun _ => .invalid)
    | .loader .selectorNot .ready =>
        .popWork₁ (.core .selectorNot (.kernel (.singleNot .push)))
          (fun _ => .invalid)
    | .loader .trueArm .ready =>
        .popWork₁ (.core .trueArm (.kernel (.conjunction .push)))
          (fun _ => .invalid)
    | .loader .falseArm .ready =>
        .popWork₁ (.core .falseArm (.kernel (.conjunction .push)))
          (fun _ => .invalid)
    | .loader .combine .ready =>
        .popWork₁ .orSeed (fun _ => .invalid)
    | .loader stage label => muxFinRelabelOp (.loader stage)
        (unaryTripleLoaderProgram.op label)
    | .core .selectorNot .finish => .popWork₁ .check (fun _ => .invalid)
    | .core .trueArm .finish =>
        .popWork₁ (.loader .falseArm unaryTripleLoaderProgram.main)
          (fun _ => .invalid)
    | .core .falseArm .finish =>
        .popWork₁ (.loader .combine unaryTripleLoaderProgram.main)
          (fun _ => .invalid)
    | .core .combine .finish => .popWork₁ .check (fun _ => .invalid)
    | .core stage label => muxFinRelabelOp (.core stage)
        (affineExactlyOneFamilyRevProgram.op label)
    | .orSeed =>
        .pushWork₁ .tick (.core .combine (.kernel (.suffixOr .next)))
    | .finish => .halt
    | .invalid => .halt

/-- Fieldwise configuration surface for the multiplexer controller. -/
def affineMuxFinCfg (label : AffineMuxFinLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineMuxFinRevProgram where
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
def affineMuxFinLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineMuxFinRevProgram :=
  affineMuxFinCfg (.loader .selectorNot unaryTripleLoaderProgram.main)
    none none false input output [] [] [] [] []

/-- Clean family loop after the true seed has been emitted. -/
def affineMuxFinCheckCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineMuxFinRevProgram :=
  affineMuxFinCfg .check none none false input output [] [] [] [] []

/-- Redirectable clean exit after the last coordinate. -/
def affineMuxFinFinishCfg (output : List CircuitSym) :
    BuilderCfg affineMuxFinRevProgram :=
  affineMuxFinCfg .finish none none false [] output [] [] [] [] []

private def relabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineMuxFinLabel) (c : BuilderCfg P) :
    BuilderCfg affineMuxFinRevProgram where
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

private def liftLoaderCfg (stage : AffineMuxFinStage)
    (c : BuilderCfg unaryTripleLoaderProgram) :
    BuilderCfg affineMuxFinRevProgram := relabelCfg (.loader stage) c

private def liftCoreCfg (stage : AffineMuxFinStage)
    (c : BuilderCfg affineExactlyOneFamilyRevProgram) :
    BuilderCfg affineMuxFinRevProgram := relabelCfg (.core stage) c

private theorem relabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineMuxFinLabel)
    (op : Op UnaryFrameSym CircuitSym P.Label) (c : BuilderCfg P) :
    stepOp (muxFinRelabelOp tag op) (relabelCfg tag c) =
      relabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [muxFinRelabelOp, relabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineMuxFin_op_loader (stage : AffineMuxFinStage)
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineMuxFinRevProgram.op (.loader stage label) =
      muxFinRelabelOp (.loader stage) (unaryTripleLoaderProgram.op label) := by
  cases stage <;> cases label <;>
    simp_all [affineMuxFinRevProgram] <;> rfl

private theorem affineMuxFin_op_core (stage : AffineMuxFinStage)
    (label : AffineExactlyOneFamilyLabel) (hexit : label ≠ .finish) :
    affineMuxFinRevProgram.op (.core stage label) =
      muxFinRelabelOp (.core stage)
        (affineExactlyOneFamilyRevProgram.op label) := by
  cases stage <;> cases label <;>
    simp_all [affineMuxFinRevProgram] <;> rfl

private theorem liftLoader_step (stage : AffineMuxFinStage)
    (c : BuilderCfg unaryTripleLoaderProgram)
    (hexit : c.label ≠ some .ready) :
    step affineMuxFinRevProgram (liftLoaderCfg stage c) =
      Option.map (liftLoaderCfg stage) (step unaryTripleLoaderProgram c) := by
  unfold step
  rw [show (liftLoaderCfg stage c).label =
    c.label.map (.loader stage) by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineMuxFin_op_loader stage label hlabelExit]
      exact congrArg some
        (relabel_stepOp (.loader stage)
          (unaryTripleLoaderProgram.op label) c)

private theorem liftCore_step (stage : AffineMuxFinStage)
    (c : BuilderCfg affineExactlyOneFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineMuxFinRevProgram (liftCoreCfg stage c) =
      Option.map (liftCoreCfg stage)
        (step affineExactlyOneFamilyRevProgram c) := by
  unfold step
  rw [show (liftCoreCfg stage c).label =
    c.label.map (.core stage) by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineMuxFin_op_core stage label hlabelExit]
      exact congrArg some
        (relabel_stepOp (.core stage)
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
    (tr : BuilderCfg P → BuilderCfg affineMuxFinRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineMuxFinRevProgram (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineMuxFinRevProgram))^[n]
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
      change (flip Option.bind (step affineMuxFinRevProgram))^[n]
        (step affineMuxFinRevProgram (tr a)) = some (tr b)
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


private def affineMuxFin_loader_run (stage : AffineMuxFinStage)
    (first second third : Nat) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (liftLoaderCfg stage (unaryTripleLoaderCfg .load₁ none
        (encodeUnaryFrame [first, second, third] ++ tail)
        output [] [] [] [] []))
      (some (liftLoaderCfg stage (unaryTripleLoaderReadyCfg
        first second third tail output [] [])))
      (unaryTripleLoaderSteps first second third) := by
  have sourceRun := unaryTripleLoader_run
    first second third tail output [] []
  have htarget : (unaryTripleLoaderReadyCfg first second third tail
      output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit UnaryTripleLoaderLabel.ready rfl
    (liftLoaderCfg stage) (liftLoader_step stage) htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineMuxFin_not_run (selector : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (liftCoreCfg .selectorNot
        (affineExactlyOneFamilyNotReadyCfg selector tail output))
      (some (liftCoreCfg .selectorNot
        (affineExactlyOneFamilyFinishCfg tail
          ((affineNotGateStream selector).reverse ++ output))))
      (affineExactlyOneFamilyNotUntilFinishSteps selector) := by
  have sourceRun := affineExactlyOneFamily_not_runToFinish
    selector tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineNotGateStream selector).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    (liftCoreCfg .selectorNot) (liftCore_step .selectorNot) htarget
      sourceRun.steps sourceRun.evals_in_steps

private def affineMuxFin_and_run (stage : AffineMuxFinStage)
    (carry source : Nat) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (liftCoreCfg stage
        (affineExactlyOneFamilyAndReadyCfg carry source tail output))
      (some (liftCoreCfg stage
        (affineExactlyOneFamilyFinishCfg tail
          ((affineAndGateStream carry source).reverse ++ output))))
      (affineExactlyOneFamilyAndUntilFinishSteps carry source) := by
  have sourceRun := affineExactlyOneFamily_and_runToFinish
    carry source tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineAndGateStream carry source).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    (liftCoreCfg stage) (liftCore_step stage) htarget sourceRun.steps
      sourceRun.evals_in_steps

private def affineMuxFin_or_run (left right : Nat)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (liftCoreCfg .combine
        (affineExactlyOneFamilyOrReadyCfg left right tail output))
      (some (liftCoreCfg .combine
        (affineExactlyOneFamilyFinishCfg tail
          ((affineOrGateStream left right).reverse ++ output))))
      (affineExactlyOneFamilyOrUntilFinishSteps left right) := by
  have sourceRun := affineExactlyOneFamily_or_runToFinish
    left right tail output
  have htarget : (affineExactlyOneFamilyFinishCfg tail
      ((affineOrGateStream left right).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineExactlyOneFamilyLabel.finish rfl
    (liftCoreCfg .combine) (liftCore_step .combine) htarget
      sourceRun.steps sourceRun.evals_in_steps

/-- Exact runtime of the shared selector header, including its loader and
both bridge instructions. -/
def affineMuxFinHeaderSteps (selector : Nat) : Nat :=
  unaryTripleLoaderSteps 0 0 selector +
    affineExactlyOneFamilyNotUntilFinishSteps selector + 2

private def affineMuxFinHeader_run (selector : Nat)
    (bodyInput : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinLoopCfg
        (encodeAffineMuxFinHeader selector ++ bodyInput) output)
      (some (affineMuxFinCheckCfg bodyInput
        ((affineNotGateStream selector).reverse ++ output)))
      (affineMuxFinHeaderSteps selector) := by
  let loaderStart := liftLoaderCfg .selectorNot
    (unaryTripleLoaderCfg .load₁ none
      (encodeUnaryFrame [0, 0, selector] ++ .frameEnd :: bodyInput)
      output [] [] [] [] [])
  let loaderReady := liftLoaderCfg .selectorNot
    (unaryTripleLoaderReadyCfg 0 0 selector
      (.frameEnd :: bodyInput) output [] [])
  let notStart := liftCoreCfg .selectorNot
    (affineExactlyOneFamilyNotReadyCfg selector bodyInput output)
  let gateOutput := (affineNotGateStream selector).reverse ++ output
  let notDone := liftCoreCfg .selectorNot
    (affineExactlyOneFamilyFinishCfg bodyInput gateOutput)
  have hloader : EvalsToInTime (step affineMuxFinRevProgram)
      loaderStart (some loaderReady)
      (unaryTripleLoaderSteps 0 0 selector) := by
    simpa [loaderStart, loaderReady] using
      affineMuxFin_loader_run .selectorNot 0 0 selector
        (.frameEnd :: bodyInput) output
  have hbridge : EvalsToInTime (step affineMuxFinRevProgram)
      loaderReady (some notStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hnot : EvalsToInTime (step affineMuxFinRevProgram)
      notStart (some notDone)
      (affineExactlyOneFamilyNotUntilFinishSteps selector) := by
    simpa [notStart, notDone, gateOutput] using
      affineMuxFin_not_run selector bodyInput output
  have hcheck : EvalsToInTime (step affineMuxFinRevProgram)
      notDone (some (affineMuxFinCheckCfg bodyInput gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineMuxFinRevProgram)
    (unaryTripleLoaderSteps 0 0 selector) 1 _ loaderReady _
    hloader hbridge
  let t₂ := EvalsToInTime.trans (step affineMuxFinRevProgram)
    _ (affineExactlyOneFamilyNotUntilFinishSteps selector) _
    notStart _ t₁ hnot
  let full := EvalsToInTime.trans (step affineMuxFinRevProgram)
    _ 1 _ notDone _ t₂ hcheck
  convert full using 1
  · simp [affineMuxFinLoopCfg, encodeAffineMuxFinHeader, loaderStart,
      liftLoaderCfg, relabelCfg, unaryTripleLoaderCfg,
      unaryTripleLoaderCfgFor, affineMuxFinCfg,
      unaryTripleLoaderProgram, unaryTripleLoaderProgramFor,
      List.append_assoc]
  · simp [affineMuxFinHeaderSteps]
    omega

/-- Exact cost of one marked coordinate frame, including three loaders,
three component calls, and nine fixed bridge/marker instructions. -/
def affineMuxFinPairSteps (frame : AffineMuxFinPairFrame) : Nat :=
  9 +
    unaryTripleLoaderSteps frame.whenTrue 0 frame.selector +
    affineExactlyOneFamilyAndUntilFinishSteps
      frame.whenTrue frame.selector +
    unaryTripleLoaderSteps frame.whenFalse 0 frame.selectorNot +
    affineExactlyOneFamilyAndUntilFinishSteps
      frame.whenFalse frame.selectorNot +
    unaryTripleLoaderSteps frame.trueArm 0 (frame.falseArm + 1) +
    affineExactlyOneFamilyOrUntilFinishSteps
      frame.trueArm frame.falseArm

private def affineMuxFinPair_run (frame : AffineMuxFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinCheckCfg
        (encodeAffineMuxFinPairFrame frame ++ tail) output)
      (some (affineMuxFinCheckCfg tail
        (((affineAndGateStream frame.whenTrue frame.selector ++
          affineAndGateStream frame.whenFalse frame.selectorNot ++
          affineOrGateStream frame.trueArm frame.falseArm)).reverse ++
          output)))
      (affineMuxFinPairSteps frame) := by
  let orInput :=
    encodeUnaryFrame [frame.trueArm, 0, frame.falseArm + 1] ++
      .frameEnd :: tail
  let falseInput :=
    encodeUnaryFrame [frame.whenFalse, 0, frame.selectorNot] ++
      .frameEnd :: orInput
  let trueInput :=
    encodeUnaryFrame [frame.whenTrue, 0, frame.selector] ++
      .frameEnd :: falseInput
  let trueOutput :=
    (affineAndGateStream frame.whenTrue frame.selector).reverse ++ output
  let falseOutput :=
    (affineAndGateStream frame.whenFalse frame.selectorNot).reverse ++
      trueOutput
  let finalOutput :=
    (affineOrGateStream frame.trueArm frame.falseArm).reverse ++ falseOutput
  let trueLoaderStart := liftLoaderCfg .trueArm
    (unaryTripleLoaderCfg .load₁ none trueInput output [] [] [] [] [])
  let trueLoaderReady := liftLoaderCfg .trueArm
    (unaryTripleLoaderReadyCfg frame.whenTrue 0 frame.selector
      (.frameEnd :: falseInput) output [] [])
  let trueStart := liftCoreCfg .trueArm
    (affineExactlyOneFamilyAndReadyCfg
      frame.whenTrue frame.selector falseInput output)
  let trueDone := liftCoreCfg .trueArm
    (affineExactlyOneFamilyFinishCfg falseInput trueOutput)
  let falseLoaderStart := liftLoaderCfg .falseArm
    (unaryTripleLoaderCfg .load₁ none falseInput trueOutput [] [] [] [] [])
  let falseLoaderReady := liftLoaderCfg .falseArm
    (unaryTripleLoaderReadyCfg frame.whenFalse 0 frame.selectorNot
      (.frameEnd :: orInput) trueOutput [] [])
  let falseStart := liftCoreCfg .falseArm
    (affineExactlyOneFamilyAndReadyCfg
      frame.whenFalse frame.selectorNot orInput trueOutput)
  let falseDone := liftCoreCfg .falseArm
    (affineExactlyOneFamilyFinishCfg orInput falseOutput)
  let orLoaderStart := liftLoaderCfg .combine
    (unaryTripleLoaderCfg .load₁ none orInput falseOutput [] [] [] [] [])
  let orLoaderReady := liftLoaderCfg .combine
    (unaryTripleLoaderReadyCfg frame.trueArm 0 (frame.falseArm + 1)
      (.frameEnd :: tail) falseOutput [] [])
  let orStart := liftCoreCfg .combine
    (affineExactlyOneFamilyOrReadyCfg
      frame.trueArm frame.falseArm tail falseOutput)
  let orDone := liftCoreCfg .combine
    (affineExactlyOneFamilyFinishCfg tail finalOutput)
  have hmarker : EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinCheckCfg (.frameEnd :: trueInput) output)
      (some trueLoaderStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have htrueLoader : EvalsToInTime (step affineMuxFinRevProgram)
      trueLoaderStart (some trueLoaderReady)
      (unaryTripleLoaderSteps frame.whenTrue 0 frame.selector) := by
    simpa [trueLoaderStart, trueLoaderReady, trueInput] using
      affineMuxFin_loader_run .trueArm frame.whenTrue 0 frame.selector
        (.frameEnd :: falseInput) output
  have htrueBridge : EvalsToInTime (step affineMuxFinRevProgram)
      trueLoaderReady (some trueStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have htrue : EvalsToInTime (step affineMuxFinRevProgram)
      trueStart (some trueDone)
      (affineExactlyOneFamilyAndUntilFinishSteps
        frame.whenTrue frame.selector) := by
    simpa [trueStart, trueDone, trueOutput] using
      affineMuxFin_and_run .trueArm frame.whenTrue frame.selector
        falseInput output
  have htoFalse : EvalsToInTime (step affineMuxFinRevProgram)
      trueDone (some falseLoaderStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hfalseLoader : EvalsToInTime (step affineMuxFinRevProgram)
      falseLoaderStart (some falseLoaderReady)
      (unaryTripleLoaderSteps frame.whenFalse 0 frame.selectorNot) := by
    simpa [falseLoaderStart, falseLoaderReady, falseInput] using
      affineMuxFin_loader_run .falseArm frame.whenFalse 0
        frame.selectorNot (.frameEnd :: orInput) trueOutput
  have hfalseBridge : EvalsToInTime (step affineMuxFinRevProgram)
      falseLoaderReady (some falseStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hfalse : EvalsToInTime (step affineMuxFinRevProgram)
      falseStart (some falseDone)
      (affineExactlyOneFamilyAndUntilFinishSteps
        frame.whenFalse frame.selectorNot) := by
    simpa [falseStart, falseDone, falseOutput] using
      affineMuxFin_and_run .falseArm frame.whenFalse frame.selectorNot
        orInput trueOutput
  have htoOr : EvalsToInTime (step affineMuxFinRevProgram)
      falseDone (some orLoaderStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have horLoader : EvalsToInTime (step affineMuxFinRevProgram)
      orLoaderStart (some orLoaderReady)
      (unaryTripleLoaderSteps frame.trueArm 0 (frame.falseArm + 1)) := by
    simpa [orLoaderStart, orLoaderReady, orInput] using
      affineMuxFin_loader_run .combine frame.trueArm 0
        (frame.falseArm + 1) (.frameEnd :: tail) falseOutput
  have horBridge : EvalsToInTime (step affineMuxFinRevProgram)
      orLoaderReady (some orStart) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hor : EvalsToInTime (step affineMuxFinRevProgram)
      orStart (some orDone)
      (affineExactlyOneFamilyOrUntilFinishSteps
        frame.trueArm frame.falseArm) := by
    simpa [orStart, orDone, finalOutput] using
      affineMuxFin_or_run frame.trueArm frame.falseArm tail falseOutput
  have hloop : EvalsToInTime (step affineMuxFinRevProgram)
      orDone (some (affineMuxFinCheckCfg tail finalOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineMuxFinRevProgram) 2 _ _
    trueLoaderStart _ hmarker htrueLoader
  let t₂ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ 1 _
    trueLoaderReady _ t₁ htrueBridge
  let t₃ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ _ _
    trueStart _ t₂ htrue
  let t₄ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ 1 _
    trueDone _ t₃ htoFalse
  let t₅ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ _ _
    falseLoaderStart _ t₄ hfalseLoader
  let t₆ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ 1 _
    falseLoaderReady _ t₅ hfalseBridge
  let t₇ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ _ _
    falseStart _ t₆ hfalse
  let t₈ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ 1 _
    falseDone _ t₇ htoOr
  let t₉ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ _ _
    orLoaderStart _ t₈ horLoader
  let t₁₀ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ 2 _
    orLoaderReady _ t₉ horBridge
  let t₁₁ := EvalsToInTime.trans (step affineMuxFinRevProgram) _ _ _
    orStart _ t₁₀ hor
  let full := EvalsToInTime.trans (step affineMuxFinRevProgram) _ 1 _
    orDone _ t₁₁ hloop
  convert full using 1
  · simp [encodeAffineMuxFinPairFrame, trueInput, falseInput, orInput,
      List.append_assoc]
  · simp [finalOutput, falseOutput, trueOutput, List.reverse_append,
      List.append_assoc]
  · unfold affineMuxFinPairSteps
    omega

/-- Exact recursive runtime after the shared selector negation. -/
def affineMuxFinFoldSteps : List AffineMuxFinPairFrame → Nat
  | [] => 1
  | frame :: rest =>
      affineMuxFinPairSteps frame + affineMuxFinFoldSteps rest

/-- Exact coordinate-family cost when execution stops before consuming the
following input symbol. -/
def affineMuxFinBodySteps : List AffineMuxFinPairFrame → Nat
  | [] => 0
  | frame :: rest =>
      affineMuxFinPairSteps frame + affineMuxFinBodySteps rest

theorem affineMuxFinFoldSteps_eq_body_add_one
    (frames : List AffineMuxFinPairFrame) :
    affineMuxFinFoldSteps frames = affineMuxFinBodySteps frames + 1 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [affineMuxFinFoldSteps, affineMuxFinBodySteps, ih]
      omega

/-- Execute mux coordinate frames while preserving an arbitrary unary suffix
and stop at the outer coordinate check. -/
def affineMuxFinFrames_runToCheck (frames : List AffineMuxFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinCheckCfg
        (frames.flatMap encodeAffineMuxFinPairFrame ++ tail) output)
      (some (affineMuxFinCheckCfg tail
        (((frames.flatMap fun frame =>
          affineAndGateStream frame.whenTrue frame.selector ++
            affineAndGateStream frame.whenFalse frame.selectorNot ++
            affineOrGateStream frame.trueArm frame.falseArm)).reverse ++
          output)))
      (affineMuxFinBodySteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        ((affineAndGateStream frame.whenTrue frame.selector ++
          affineAndGateStream frame.whenFalse frame.selectorNot ++
          affineOrGateStream frame.trueArm frame.falseArm)).reverse ++ output
      have hframe := affineMuxFinPair_run frame
        (rest.flatMap encodeAffineMuxFinPairFrame ++ tail) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineMuxFinRevProgram)
        (affineMuxFinPairSteps frame) (affineMuxFinBodySteps rest) _
        (affineMuxFinCheckCfg
          (rest.flatMap encodeAffineMuxFinPairFrame ++ tail) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [List.append_assoc]
      · simp [frameOutput, List.reverse_append, List.append_assoc]
      · simp [affineMuxFinBodySteps]
        omega

private def affineMuxFinFrames_run (frames : List AffineMuxFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinCheckCfg
        (frames.flatMap encodeAffineMuxFinPairFrame) output)
      (some (affineMuxFinFinishCfg
        (((frames.flatMap fun frame =>
          affineAndGateStream frame.whenTrue frame.selector ++
            affineAndGateStream frame.whenFalse frame.selectorNot ++
            affineOrGateStream frame.trueArm frame.falseArm)).reverse ++
          output)))
      (affineMuxFinFoldSteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let frameOutput :=
        ((affineAndGateStream frame.whenTrue frame.selector ++
          affineAndGateStream frame.whenFalse frame.selectorNot ++
          affineOrGateStream frame.trueArm frame.falseArm)).reverse ++ output
      have hframe := affineMuxFinPair_run frame
        (rest.flatMap encodeAffineMuxFinPairFrame) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans (step affineMuxFinRevProgram)
        (affineMuxFinPairSteps frame) (affineMuxFinFoldSteps rest) _
        (affineMuxFinCheckCfg
          (rest.flatMap encodeAffineMuxFinPairFrame) frameOutput) _
        hframe hrest
      convert full using 1
      · simp [List.append_assoc]
      · simp [frameOutput, List.reverse_append, List.append_assoc]
      · simp [affineMuxFinFoldSteps]
        omega

/-- Exact contextual runtime through the public finish label. -/
def affineMuxFinUntilFinishSteps (selector : Nat)
    (frames : List AffineMuxFinPairFrame) : Nat :=
  affineMuxFinHeaderSteps selector + affineMuxFinFoldSteps frames

/-- Execute an arbitrary explicit multiplexer family with one fixed program. -/
def affineMuxFin_runToFinish (selector : Nat)
    (frames : List AffineMuxFinPairFrame) (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinLoopCfg (encodeAffineMuxFinFrames selector frames) output)
      (some (affineMuxFinFinishCfg
        ((affineMuxFinGateStream selector frames).reverse ++ output)))
      (affineMuxFinUntilFinishSteps selector frames) := by
  let bodyInput := frames.flatMap encodeAffineMuxFinPairFrame
  let notOutput := (affineNotGateStream selector).reverse ++ output
  have hheader := affineMuxFinHeader_run selector bodyInput output
  have hframes := affineMuxFinFrames_run frames notOutput
  let full := EvalsToInTime.trans (step affineMuxFinRevProgram)
    (affineMuxFinHeaderSteps selector) (affineMuxFinFoldSteps frames) _
    (affineMuxFinCheckCfg bodyInput notOutput) _ hheader hframes
  convert full using 1
  · simp [encodeAffineMuxFinFrames, bodyInput]
  · simp [affineMuxFinGateStream, notOutput, List.reverse_append,
      List.append_assoc]
  · simp [affineMuxFinUntilFinishSteps, Nat.add_comm]

/-- Execute a complete mux phase while preserving an arbitrary unary suffix
and stop before the outer coordinate check inspects it. -/
def affineMuxFin_runToCheck (selector : Nat)
    (frames : List AffineMuxFinPairFrame) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinLoopCfg
        (encodeAffineMuxFinFrames selector frames ++ tail) output)
      (some (affineMuxFinCheckCfg tail
        ((affineMuxFinGateStream selector frames).reverse ++ output)))
      (affineMuxFinHeaderSteps selector + affineMuxFinBodySteps frames) := by
  let bodyInput := frames.flatMap encodeAffineMuxFinPairFrame ++ tail
  let notOutput := (affineNotGateStream selector).reverse ++ output
  have hheader := affineMuxFinHeader_run selector bodyInput output
  have hframes := affineMuxFinFrames_runToCheck frames tail notOutput
  let full := EvalsToInTime.trans (step affineMuxFinRevProgram)
    (affineMuxFinHeaderSteps selector) (affineMuxFinBodySteps frames) _
    (affineMuxFinCheckCfg bodyInput notOutput) _ hheader
    (by simpa [bodyInput] using hframes)
  convert full using 1
  · simp [encodeAffineMuxFinFrames, bodyInput, List.append_assoc]
  · simp [affineMuxFinGateStream, notOutput, List.reverse_append,
      List.append_assoc]
  · omega

/-! ## Canonical frames and semantic trace agreement -/

/-- Canonical runtime frames for the semantic finite-family multiplexer. -/
def affineMuxFinCanonicalFrames (start selector : Nat) :
    (n : Nat) →
      (whenTrue whenFalse : Fin n → CookLevin.CircuitBuilder.Wire) →
        List AffineMuxFinPairFrame
  | 0, _, _ => []
  | n + 1, whenTrue, whenFalse =>
      affineMuxFinCanonicalFrames start selector n
          (fun i => whenTrue i.castSucc) (fun i => whenFalse i.castSucc) ++
        [{ whenTrue := whenTrue (Fin.last n)
           whenFalse := whenFalse (Fin.last n)
           selector := selector
           selectorNot := start
           trueArm := start + 1 + 3 * n
           falseArm := start + 2 + 3 * n }]

private theorem affineMuxFinCanonicalBodyStream_eq_trace
    (start selector : Nat) :
    (n : Nat) →
      (whenTrue whenFalse : Fin n → CookLevin.CircuitBuilder.Wire) →
      (affineMuxFinCanonicalFrames start selector n whenTrue whenFalse).flatMap
        (fun frame =>
          affineAndGateStream frame.whenTrue frame.selector ++
            affineAndGateStream frame.whenFalse frame.selectorNot ++
            affineOrGateStream frame.trueArm frame.falseArm) =
      (CircuitBuilder.muxFinBodyGateTrace
        (start + 1) selector start n whenTrue whenFalse).flatMap
          encodeCircuitGate := by
  intro n
  induction n with
  | zero =>
      intro whenTrue whenFalse
      rfl
  | succ n ih =>
      intro whenTrue whenFalse
      rw [show affineMuxFinCanonicalFrames start selector (n + 1)
          whenTrue whenFalse =
        affineMuxFinCanonicalFrames start selector n
            (fun i => whenTrue i.castSucc)
            (fun i => whenFalse i.castSucc) ++
          [{ whenTrue := whenTrue (Fin.last n)
             whenFalse := whenFalse (Fin.last n)
             selector := selector
             selectorNot := start
             trueArm := start + 1 + 3 * n
             falseArm := start + 2 + 3 * n }] by rfl]
      rw [List.flatMap_append, ih]
      simp only [CircuitBuilder.muxFinBodyGateTrace,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.flatMap_append]
      simp [CircuitBuilder.muxFinBodyGateTrace_length,
        affineAndGateStream, affineOrGateStream, List.append_assoc]
      congr 2 <;> omega

/-- The canonical runtime stream is byte-for-byte the exact ordered semantic
multiplexer trace. -/
theorem affineMuxFinCanonicalGateStream_eq_trace (start selector : Nat)
    {n : Nat}
    (whenTrue whenFalse : Fin n → CookLevin.CircuitBuilder.Wire) :
    affineMuxFinGateStream selector
        (affineMuxFinCanonicalFrames start selector n whenTrue whenFalse) =
      (CircuitBuilder.muxFinGateTrace start selector
        whenTrue whenFalse).flatMap encodeCircuitGate := by
  unfold affineMuxFinGateStream CircuitBuilder.muxFinGateTrace
  rw [affineMuxFinCanonicalBodyStream_eq_trace]
  simp [affineNotGateStream]

/-- Standalone exact execution, including the final halt instruction. -/
def affineMuxFinRevSteps (selector : Nat)
    (frames : List AffineMuxFinPairFrame) : Nat :=
  affineMuxFinUntilFinishSteps selector frames + 1

def affineMuxFin_run (selector : Nat) (frames : List AffineMuxFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinLoopCfg
        (encodeAffineMuxFinFrames selector frames) output)
      (some (haltCfg affineMuxFinRevProgram
        ((affineMuxFinGateStream selector frames).reverse ++ output)))
      (affineMuxFinRevSteps selector frames) := by
  let gateOutput := (affineMuxFinGateStream selector frames).reverse ++ output
  have hfinish := affineMuxFin_runToFinish selector frames output
  have hhalt : EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinFinishCfg gateOutput)
      (some (haltCfg affineMuxFinRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineMuxFinRevProgram)
    (affineMuxFinUntilFinishSteps selector frames) 1 _
    (affineMuxFinFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  convert full using 1 <;>
    simp [affineMuxFinRevSteps, gateOutput, Nat.add_comm] <;> omega

/-- Canonical fixed-controller execution specialized to the semantic
finite-family multiplexer trace. -/
def affineMuxFinCanonical_run (start selector : Nat) {n : Nat}
    (whenTrue whenFalse : Fin n → CookLevin.CircuitBuilder.Wire)
    (output : List CircuitSym) :
    EvalsToInTime (step affineMuxFinRevProgram)
      (affineMuxFinLoopCfg
        (encodeAffineMuxFinFrames selector
          (affineMuxFinCanonicalFrames start selector n
            whenTrue whenFalse)) output)
      (some (haltCfg affineMuxFinRevProgram
        (((CircuitBuilder.muxFinGateTrace start selector
          whenTrue whenFalse).flatMap encodeCircuitGate).reverse ++ output)))
      (affineMuxFinRevSteps selector
        (affineMuxFinCanonicalFrames start selector n
          whenTrue whenFalse)) := by
  simpa [affineMuxFinCanonicalGateStream_eq_trace] using
    affineMuxFin_run selector
      (affineMuxFinCanonicalFrames start selector n whenTrue whenFalse) output

@[simp] theorem encodeAffineMuxFinHeader_length (selector : Nat) :
    (encodeAffineMuxFinHeader selector).length = selector + 4 := by
  simp [encodeAffineMuxFinHeader, encodeUnaryFrame_length]
  omega

@[simp] theorem encodeAffineMuxFinPairFrame_length
    (frame : AffineMuxFinPairFrame) :
    (encodeAffineMuxFinPairFrame frame).length =
      frame.whenTrue + frame.whenFalse + frame.selector +
        frame.selectorNot + frame.trueArm + frame.falseArm + 14 := by
  simp [encodeAffineMuxFinPairFrame, encodeUnaryFrame_length]
  omega

theorem affineMuxFinHeader_steps_le (selector : Nat) :
    affineMuxFinHeaderSteps selector ≤
      200 * (encodeAffineMuxFinHeader selector).length := by
  simp [affineMuxFinHeaderSteps, unaryTripleLoaderSteps,
    affineExactlyOneFamilyNotUntilFinishSteps,
    affineNotRevCoreSteps, encodeAffineMuxFinHeader_length]
  omega

theorem affineMuxFinPair_steps_le (frame : AffineMuxFinPairFrame) :
    affineMuxFinPairSteps frame ≤
      200 * (encodeAffineMuxFinPairFrame frame).length := by
  simp [affineMuxFinPairSteps, unaryTripleLoaderSteps,
    affineExactlyOneFamilyAndUntilFinishSteps, affineAndRevCoreSteps,
    affineExactlyOneFamilyOrUntilFinishSteps, affineOrRevCoreSteps,
    encodeAffineMuxFinPairFrame_length]
  omega

theorem affineMuxFinFold_steps_le (frames : List AffineMuxFinPairFrame) :
    affineMuxFinFoldSteps frames ≤
      200 * (frames.flatMap encodeAffineMuxFinPairFrame).length + 1 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have hframe := affineMuxFinPair_steps_le frame
      simp only [affineMuxFinFoldSteps, List.flatMap_cons,
        List.length_append]
      omega

/-- The complete run is linear—and hence polynomial—in its delimiter-bearing
unary runtime input. -/
theorem affineMuxFinRev_steps_le (selector : Nat)
    (frames : List AffineMuxFinPairFrame) :
    affineMuxFinRevSteps selector frames ≤
      200 * (encodeAffineMuxFinFrames selector frames).length + 2 := by
  have hheader := affineMuxFinHeader_steps_le selector
  have hframes := affineMuxFinFold_steps_le frames
  simp [affineMuxFinRevSteps, affineMuxFinUntilFinishSteps,
    encodeAffineMuxFinFrames, List.length_append] at *
  omega

end CLRS.Chapter34.Turing.PolyBuilder
