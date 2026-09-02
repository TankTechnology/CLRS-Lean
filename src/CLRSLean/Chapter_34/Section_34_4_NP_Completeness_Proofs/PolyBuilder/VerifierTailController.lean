import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.EqFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputShapeController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction

/-!
# Continuous post-transition verifier-tail controller

One fixed program executes the symbolic initial boundary, verifier-input
boundary, total accepting boundary, final conjunction, and encoded output wire.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

structure AffineVerifierTailScript where
  initialFrames : List AffineEqFinPairFrame
  inputShape : AffineInputShapeScript
  acceptingFrames : Option (List AffineEqFinPairFrame)
  conjunctionFrame : AffineConjunctionFrame
  outputWire : Nat

def encodeAffineVerifierTailAccepting :
    Option (List AffineEqFinPairFrame) → List UnaryFrameSym
  | none => [.separator]
  | some frames =>
      .frameEnd :: encodeAffineEqFinFrames frames ++ [.separator]

def affineVerifierTailAcceptingGateStream :
    Option (List AffineEqFinPairFrame) → List CircuitSym
  | none => []
  | some frames => affineEqFinGateStream frames

def encodeAffineVerifierTailScript (script : AffineVerifierTailScript) :
    List UnaryFrameSym :=
  encodeAffineEqFinFrames script.initialFrames ++ [.separator] ++
    encodeAffineInputShapeScript script.inputShape ++ [.tick] ++
    encodeAffineVerifierTailAccepting script.acceptingFrames ++
    encodeAffineConjunctionFrame script.conjunctionFrame ++
    encodeUnaryFrameBlock script.outputWire

def affineVerifierTailGateStream (script : AffineVerifierTailScript) :
    List CircuitSym :=
  affineEqFinGateStream script.initialFrames ++
    affineInputShapeGateStream script.inputShape ++
    affineVerifierTailAcceptingGateStream script.acceptingFrames ++
    affineConjunctionGateStream script.conjunctionFrame ++
    .outputMark :: encNat script.outputWire

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

inductive AffineVerifierTailLabel
  | initial (label : AffineEqFinLabel)
  | inputShape (label : AffineInputShapeLabel)
  | acceptingCheck | acceptingClear | acceptingNoneClear
  | acceptingEq (label : AffineEqFinLabel)
  | conjunction (label : AffineConjunctionLabel)
  | outputMark | outputScan | outputPushArg | outputPushEnd
  | finish | invalid
deriving DecidableEq, Fintype

def affineVerifierTailRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineVerifierTailLabel
  main := .initial .seed
  op
    | .initial .finish =>
        .popWork₁ (.inputShape affineInputShapeRevProgram.main)
          (fun _ => .invalid)
    | .initial .check => .popInput (.initial .finish) fun
        | .frameEnd => .initial .clearMarker
        | .separator => .initial .finish
        | .tick => .initial .invalid
    | .initial label => relabelOp .initial (affineEqFinRevProgram.op label)
    | .inputShape .finish => .popWork₁ .acceptingCheck (fun _ => .invalid)
    | .inputShape label =>
        relabelOp .inputShape (affineInputShapeRevProgram.op label)
    | .acceptingCheck => .popInput .invalid fun
        | .frameEnd => .acceptingClear
        | .separator => .acceptingNoneClear
        | .tick => .invalid
    | .acceptingClear =>
        .popWork₁ (.acceptingEq affineEqFinRevProgram.main)
          (fun _ => .invalid)
    | .acceptingNoneClear =>
        .popWork₁ (.conjunction affineConjunctionRevProgram.main)
          (fun _ => .invalid)
    | .acceptingEq .finish =>
        .popWork₁ (.conjunction affineConjunctionRevProgram.main)
          (fun _ => .invalid)
    | .acceptingEq .check => .popInput (.acceptingEq .finish) fun
        | .frameEnd => .acceptingEq .clearMarker
        | .separator => .acceptingEq .finish
        | .tick => .acceptingEq .invalid
    | .acceptingEq label =>
        relabelOp .acceptingEq (affineEqFinRevProgram.op label)
    | .conjunction .finish => .popWork₁ .outputMark (fun _ => .invalid)
    | .conjunction label =>
        relabelOp .conjunction (affineConjunctionRevProgram.op label)
    | .outputMark => .pushOutput .outputMark .outputScan
    | .outputScan => .popInput .invalid fun
        | .tick => .outputPushArg
        | .separator => .outputPushEnd
        | .frameEnd => .invalid
    | .outputPushArg => .pushOutput .argMark .outputScan
    | .outputPushEnd => .pushOutput .endMark .finish
    | .finish => .halt
    | .invalid => .halt

def affineVerifierTailCfg (label : AffineVerifierTailLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineVerifierTailRevProgram where
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

def affineVerifierTailLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineVerifierTailRevProgram :=
  affineVerifierTailCfg (.initial .seed)
    none none false input output [] [] [] [] []

private def relabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineVerifierTailLabel) (c : BuilderCfg P) :
    BuilderCfg affineVerifierTailRevProgram where
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

private def liftInitialCfg (c : BuilderCfg affineEqFinRevProgram) :
    BuilderCfg affineVerifierTailRevProgram := relabelCfg .initial c

private def liftInputCfg (c : BuilderCfg affineInputShapeRevProgram) :
    BuilderCfg affineVerifierTailRevProgram := relabelCfg .inputShape c

private def liftAcceptingCfg (c : BuilderCfg affineEqFinRevProgram) :
    BuilderCfg affineVerifierTailRevProgram := relabelCfg .acceptingEq c

private def liftConjunctionCfg (c : BuilderCfg affineConjunctionRevProgram) :
    BuilderCfg affineVerifierTailRevProgram := relabelCfg .conjunction c

/-- A shape used only by the outer controller after it consumes the explicit
equality-family separator.  The reusable equality primitive remains unchanged. -/
private def eqBoundaryFinishCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineEqFinRevProgram :=
  affineEqFinCfg .finish (some .separator) none false tail output
    [] [] [] [] []

private def eqBoundaryBad (c : BuilderCfg affineEqFinRevProgram) : Prop :=
  c.label = some .check ∧ ∃ tail, c.input = .separator :: tail

private theorem relabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineVerifierTailLabel)
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

private theorem outer_op_initial (label : AffineEqFinLabel)
    (hcheck : label ≠ .check) (hexit : label ≠ .finish) :
    affineVerifierTailRevProgram.op (.initial label) =
      relabelOp .initial (affineEqFinRevProgram.op label) := by
  cases label <;> simp_all [affineVerifierTailRevProgram] <;> rfl

private theorem outer_op_input (label : AffineInputShapeLabel)
    (hexit : label ≠ .finish) :
    affineVerifierTailRevProgram.op (.inputShape label) =
      relabelOp .inputShape (affineInputShapeRevProgram.op label) := by
  cases label <;> simp_all [affineVerifierTailRevProgram] <;> rfl

private theorem outer_op_accepting (label : AffineEqFinLabel)
    (hcheck : label ≠ .check) (hexit : label ≠ .finish) :
    affineVerifierTailRevProgram.op (.acceptingEq label) =
      relabelOp .acceptingEq (affineEqFinRevProgram.op label) := by
  cases label <;> simp_all [affineVerifierTailRevProgram] <;> rfl

private theorem outer_op_conjunction (label : AffineConjunctionLabel)
    (hexit : label ≠ .finish) :
    affineVerifierTailRevProgram.op (.conjunction label) =
      relabelOp .conjunction (affineConjunctionRevProgram.op label) := by
  cases label <;> simp_all [affineVerifierTailRevProgram] <;> rfl

private theorem lift_step {P : Program UnaryFrameSym CircuitSym}
    (exit : P.Label) (tag : P.Label → AffineVerifierTailLabel)
    (hop : ∀ label, label ≠ exit →
      affineVerifierTailRevProgram.op (tag label) =
        relabelOp tag (P.op label))
    (c : BuilderCfg P) (hexit : c.label ≠ some exit) :
    step affineVerifierTailRevProgram (relabelCfg tag c) =
      Option.map (relabelCfg tag) (step P c) := by
  unfold step
  rw [show (relabelCfg tag c).label = c.label.map tag by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ exit := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [hop label hlabelExit]
      exact congrArg some (relabel_stepOp tag (P.op label) c)

private theorem liftInitial_step (c : BuilderCfg affineEqFinRevProgram)
    (hexit : c.label ≠ some .finish) (hsafe : ¬ eqBoundaryBad c) :
    step affineVerifierTailRevProgram (liftInitialCfg c) =
      Option.map liftInitialCfg (step affineEqFinRevProgram c) := by
  unfold step
  rw [show (liftInitialCfg c).label = c.label.map .initial by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hfinish : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      by_cases hcheck : label = .check
      · subst label
        rcases c with
          ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
            counter₁, counter₂, counter₃⟩
        simp only at hlabel
        subst label
        cases input with
        | nil => rfl
        | cons head tail =>
            cases head with
            | separator =>
                exfalso
                apply hsafe
                exact ⟨rfl, ⟨tail, rfl⟩⟩
            | frameEnd => rfl
            | tick => rfl
      rw [outer_op_initial label hcheck hfinish]
      exact congrArg some
        (relabel_stepOp .initial (affineEqFinRevProgram.op label) c)

private theorem liftAccepting_step (c : BuilderCfg affineEqFinRevProgram)
    (hexit : c.label ≠ some .finish) (hsafe : ¬ eqBoundaryBad c) :
    step affineVerifierTailRevProgram (liftAcceptingCfg c) =
      Option.map liftAcceptingCfg (step affineEqFinRevProgram c) := by
  unfold step
  rw [show (liftAcceptingCfg c).label = c.label.map .acceptingEq by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hfinish : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      by_cases hcheck : label = .check
      · subst label
        rcases c with
          ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
            counter₁, counter₂, counter₃⟩
        simp only at hlabel
        subst label
        cases input with
        | nil => rfl
        | cons head tail =>
            cases head with
            | separator =>
                exfalso
                apply hsafe
                exact ⟨rfl, ⟨tail, rfl⟩⟩
            | frameEnd => rfl
            | tick => rfl
      rw [outer_op_accepting label hcheck hfinish]
      exact congrArg some
        (relabel_stepOp .acceptingEq (affineEqFinRevProgram.op label) c)

private theorem iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem haltExit_no_return {P : Program UnaryFrameSym CircuitSym}
    (exit target : P.Label) (hop : P.op exit = .halt)
    (a b : BuilderCfg P) (ha : a.label = some exit)
    (hb : b.label = some target) : ∀ n : Nat,
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

private theorem eqBoundaryBad_step (c : BuilderCfg affineEqFinRevProgram)
    (hbad : eqBoundaryBad c) :
    ∃ d : BuilderCfg affineEqFinRevProgram,
      step affineEqFinRevProgram c = some d ∧ d.label = some .invalid := by
  rcases hbad with ⟨hlabel, ⟨tail, hinput⟩⟩
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at hlabel hinput
  subst label
  subst input
  refine ⟨_, rfl, rfl⟩

private theorem liftEq_iterations_avoiding
    (tag : AffineEqFinLabel → AffineVerifierTailLabel)
    (hstep : ∀ c : BuilderCfg affineEqFinRevProgram,
      c.label ≠ some .finish → ¬ eqBoundaryBad c →
      step affineVerifierTailRevProgram (relabelCfg tag c) =
        Option.map (relabelCfg tag) (step affineEqFinRevProgram c))
    (target : AffineEqFinLabel) (htarget : target ≠ .invalid)
    {a b : BuilderCfg affineEqFinRevProgram}
    (hb : b.label = some target) : ∀ n : Nat,
    (flip Option.bind (step affineEqFinRevProgram))^[n] (some a) = some b →
      (flip Option.bind (step affineVerifierTailRevProgram))^[n]
        (some (relabelCfg tag a)) = some (relabelCfg tag b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineEqFinRevProgram))^[n]
        (step affineEqFinRevProgram a) = some b at h
      change (flip Option.bind (step affineVerifierTailRevProgram))^[n]
        (step affineVerifierTailRevProgram (relabelCfg tag a)) =
          some (relabelCfg tag b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact haltExit_no_return AffineEqFinLabel.finish target rfl
          a b ha hb n h
      have hasafe : ¬ eqBoundaryBad a := by
        intro hbad
        obtain ⟨d, hbadStep, hdlabel⟩ := eqBoundaryBad_step a hbad
        cases n with
        | zero =>
            rw [hbadStep] at h
            injection h with hdb
            have hlabels := congrArg (fun cfg => cfg.label) hdb
            simp [hdlabel, hb] at hlabels
            exact htarget (Option.some.inj hlabels.symm)
        | succ n =>
            rw [Function.iterate_succ_apply, hbadStep] at h
            change (flip Option.bind (step affineEqFinRevProgram))^[n]
              (step affineEqFinRevProgram d) = some b at h
            exact haltExit_no_return AffineEqFinLabel.invalid target rfl
              d b hdlabel hb n h
      cases hsource : step affineEqFinRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit hasafe
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem lift_iterations_to_haltExit
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tag : P.Label → AffineVerifierTailLabel)
    (hopOuter : ∀ label, label ≠ exit →
      affineVerifierTailRevProgram.op (tag label) =
        relabelOp tag (P.op label))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineVerifierTailRevProgram))^[n]
        (some (relabelCfg tag a)) = some (relabelCfg tag b) := by
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
      change (flip Option.bind (step affineVerifierTailRevProgram))^[n]
        (step affineVerifierTailRevProgram (relabelCfg tag a)) =
          some (relabelCfg tag b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact haltExit_no_return exit exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := lift_step exit tag hopOuter a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem eqFoldSteps_eq_body_add_one
    (frames : List AffineEqFinPairFrame) :
    affineEqFinFoldSteps frames = affineEqFinBodySteps frames + 1 := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [affineEqFinFoldSteps, affineEqFinBodySteps, ih]
      omega

private def liftInitial_run (frames : List AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (liftInitialCfg (affineEqFinLoopCfg
        (encodeAffineEqFinFrames frames ++ .separator :: tail) output))
      (some (liftInitialCfg (eqBoundaryFinishCfg tail
        ((affineEqFinGateStream frames).reverse ++ output))))
      (affineEqFinUntilFinishSteps frames) := by
  let gateOutput := (affineEqFinGateStream frames).reverse ++ output
  let checked := affineEqFinCheckCfg (.separator :: tail) gateOutput
  have sourceRun := affineEqFin_runToCheck frames (.separator :: tail) output
  have hbody : EvalsToInTime (step affineVerifierTailRevProgram)
      (liftInitialCfg (affineEqFinLoopCfg
        (encodeAffineEqFinFrames frames ++ .separator :: tail) output))
      (some (liftInitialCfg checked)) (1 + affineEqFinBodySteps frames) := by
    refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
    exact liftEq_iterations_avoiding .initial liftInitial_step .check
      (by decide) rfl sourceRun.steps
      (by simpa [checked, gateOutput] using sourceRun.evals_in_steps)
  have hfinish : EvalsToInTime (step affineVerifierTailRevProgram)
      (liftInitialCfg checked)
      (some (liftInitialCfg (eqBoundaryFinishCfg tail gateOutput))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineVerifierTailRevProgram)
    (1 + affineEqFinBodySteps frames) 1 _ (liftInitialCfg checked) _
    hbody hfinish
  have hsteps : 1 + (1 + affineEqFinBodySteps frames) =
      affineEqFinUntilFinishSteps frames := by
    rw [affineEqFinUntilFinishSteps, eqFoldSteps_eq_body_add_one]
    omega
  rw [← hsteps]
  simpa [gateOutput, Nat.add_comm] using full

private def liftInput_run (script : AffineInputShapeScript)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (liftInputCfg (affineInputShapeLoopCfg
        (encodeAffineInputShapeScript script ++ .tick :: tail) output))
      (some (liftInputCfg (affineInputShapeFinishInputCfg tail
        ((affineInputShapeGateStream script).reverse ++ output))))
      (affineInputShapeUntilFinishSteps script) := by
  have sourceRun := affineInputShape_runToFinishWithTail script tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineInputShapeLabel.finish rfl
    .inputShape outer_op_input rfl sourceRun.steps sourceRun.evals_in_steps

private def liftAccepting_run (frames : List AffineEqFinPairFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (liftAcceptingCfg (affineEqFinLoopCfg
        (encodeAffineEqFinFrames frames ++ .separator :: tail) output))
      (some (liftAcceptingCfg (eqBoundaryFinishCfg tail
        ((affineEqFinGateStream frames).reverse ++ output))))
      (affineEqFinUntilFinishSteps frames) := by
  let gateOutput := (affineEqFinGateStream frames).reverse ++ output
  let checked := affineEqFinCheckCfg (.separator :: tail) gateOutput
  have sourceRun := affineEqFin_runToCheck frames (.separator :: tail) output
  have hbody : EvalsToInTime (step affineVerifierTailRevProgram)
      (liftAcceptingCfg (affineEqFinLoopCfg
        (encodeAffineEqFinFrames frames ++ .separator :: tail) output))
      (some (liftAcceptingCfg checked)) (1 + affineEqFinBodySteps frames) := by
    refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
    exact liftEq_iterations_avoiding .acceptingEq liftAccepting_step .check
      (by decide) rfl sourceRun.steps
      (by simpa [checked, gateOutput] using sourceRun.evals_in_steps)
  have hfinish : EvalsToInTime (step affineVerifierTailRevProgram)
      (liftAcceptingCfg checked)
      (some (liftAcceptingCfg (eqBoundaryFinishCfg tail gateOutput))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineVerifierTailRevProgram)
    (1 + affineEqFinBodySteps frames) 1 _ (liftAcceptingCfg checked) _
    hbody hfinish
  have hsteps : 1 + (1 + affineEqFinBodySteps frames) =
      affineEqFinUntilFinishSteps frames := by
    rw [affineEqFinUntilFinishSteps, eqFoldSteps_eq_body_add_one]
    omega
  rw [← hsteps]
  simpa [gateOutput, Nat.add_comm] using full

private def liftConjunction_run (frame : AffineConjunctionFrame)
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (liftConjunctionCfg (affineConjunctionLoopCfg
        (encodeAffineConjunctionFrame frame ++ tail) output))
      (some (liftConjunctionCfg (affineConjunctionFinishCfg tail
        ((affineConjunctionGateStream frame).reverse ++ output))))
      (affineConjunctionUntilFinishSteps frame) := by
  have sourceRun := affineConjunction_runToFinish frame tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineConjunctionLabel.finish rfl
    .conjunction outer_op_conjunction rfl sourceRun.steps
      sourceRun.evals_in_steps

def affineVerifierTailOutputCfg (label : AffineVerifierTailLabel)
    (buffer : Option UnaryFrameSym) (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineVerifierTailRevProgram :=
  affineVerifierTailCfg label buffer none false input output [] [] [] [] []

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem outputScan_eval (buffer : Option UnaryFrameSym) (value : Nat)
    (output : List CircuitSym) :
    (flip Option.bind (step affineVerifierTailRevProgram))^[2 * value + 3]
      (some (affineVerifierTailOutputCfg .outputScan buffer
        (encodeUnaryFrameBlock value) output)) =
      some (haltCfg affineVerifierTailRevProgram
        (.endMark :: List.replicate value .argMark ++ output)) := by
  induction value generalizing buffer output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 3 = (2 * value + 3) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step affineVerifierTailRevProgram))^[
          2 * value + 3]
        (some (affineVerifierTailOutputCfg .outputScan (some .tick)
          (encodeUnaryFrameBlock value) (.argMark :: output))) = _
      simpa [encodeUnaryFrameBlock, affineVerifierTailOutputCfg,
        List.replicate_succ, replicate_append_cons,
        List.append_assoc] using ih (some .tick) (.argMark :: output)

private def affineVerifierTail_output_run (value : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (affineVerifierTailOutputCfg .outputMark none
        (encodeUnaryFrameBlock value) output)
      (some (haltCfg affineVerifierTailRevProgram
        ((.outputMark :: encNat value).reverse ++ output)))
      (2 * value + 4) := by
  have hmark : EvalsToInTime (step affineVerifierTailRevProgram)
      (affineVerifierTailOutputCfg .outputMark none
        (encodeUnaryFrameBlock value) output)
      (some (affineVerifierTailOutputCfg .outputScan none
        (encodeUnaryFrameBlock value) (.outputMark :: output))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hscan : EvalsToInTime (step affineVerifierTailRevProgram)
      (affineVerifierTailOutputCfg .outputScan none
        (encodeUnaryFrameBlock value) (.outputMark :: output))
      (some (haltCfg affineVerifierTailRevProgram
        (.endMark :: List.replicate value .argMark ++ .outputMark :: output)))
      (2 * value + 3) :=
    ⟨⟨2 * value + 3, outputScan_eval none value (.outputMark :: output)⟩,
      le_rfl⟩
  let full := EvalsToInTime.trans (step affineVerifierTailRevProgram)
    1 (2 * value + 3) _
    (affineVerifierTailOutputCfg .outputScan none
      (encodeUnaryFrameBlock value) (.outputMark :: output)) _ hmark hscan
  convert full using 1
  · simp [encNat, List.reverse_append, List.append_assoc]

def affineVerifierTailAcceptingSteps :
    Option (List AffineEqFinPairFrame) → Nat
  | none => 2
  | some frames => affineEqFinUntilFinishSteps frames + 3

def affineVerifierTailRevSteps (script : AffineVerifierTailScript) : Nat :=
  affineEqFinUntilFinishSteps script.initialFrames + 1 +
    affineInputShapeUntilFinishSteps script.inputShape + 1 +
    affineVerifierTailAcceptingSteps script.acceptingFrames +
    affineConjunctionUntilFinishSteps script.conjunctionFrame + 1 +
    (2 * script.outputWire + 4)

/-- Exact continuous execution of the complete post-transition circuit tail. -/
def affineVerifierTail_run (script : AffineVerifierTailScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierTailRevProgram)
      (affineVerifierTailLoopCfg
        (encodeAffineVerifierTailScript script) output)
      (some (haltCfg affineVerifierTailRevProgram
        ((affineVerifierTailGateStream script).reverse ++ output)))
      (affineVerifierTailRevSteps script) := by
  let outputInput := encodeUnaryFrameBlock script.outputWire
  let conjunctionInput :=
    encodeAffineConjunctionFrame script.conjunctionFrame ++ outputInput
  let acceptingInput :=
    encodeAffineVerifierTailAccepting script.acceptingFrames ++
      conjunctionInput
  let inputTail := acceptingInput
  let initialTail :=
    encodeAffineInputShapeScript script.inputShape ++ .tick :: inputTail
  let afterInitial := (affineEqFinGateStream script.initialFrames).reverse ++
    output
  let afterInput := (affineInputShapeGateStream script.inputShape).reverse ++
    afterInitial
  let afterAccepting :=
    (affineVerifierTailAcceptingGateStream script.acceptingFrames).reverse ++
      afterInput
  let afterConjunction :=
    (affineConjunctionGateStream script.conjunctionFrame).reverse ++
      afterAccepting
  let initialDone := liftInitialCfg
    (eqBoundaryFinishCfg initialTail afterInitial)
  let inputStart := liftInputCfg
    (affineInputShapeLoopCfg initialTail afterInitial)
  let inputDone := liftInputCfg
    (affineInputShapeFinishInputCfg inputTail afterInput)
  let acceptingStart := affineVerifierTailOutputCfg .acceptingCheck none
    acceptingInput afterInput
  let conjunctionStart := liftConjunctionCfg
    (affineConjunctionLoopCfg conjunctionInput afterAccepting)
  let conjunctionDone := liftConjunctionCfg
    (affineConjunctionFinishCfg outputInput afterConjunction)
  let outputStart := affineVerifierTailOutputCfg .outputMark none
    outputInput afterConjunction
  have hinitial : EvalsToInTime (step affineVerifierTailRevProgram)
      (affineVerifierTailLoopCfg
        (encodeAffineVerifierTailScript script) output)
      (some initialDone)
      (affineEqFinUntilFinishSteps script.initialFrames) := by
    simpa [affineVerifierTailLoopCfg, encodeAffineVerifierTailScript,
      initialDone, initialTail, inputTail, acceptingInput, conjunctionInput,
      outputInput, afterInitial, liftInitialCfg, relabelCfg,
      affineEqFinLoopCfg, affineEqFinCfg, affineVerifierTailCfg,
      List.append_assoc] using
      liftInitial_run script.initialFrames initialTail output
  have htoInput : EvalsToInTime (step affineVerifierTailRevProgram)
      initialDone (some inputStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hinput : EvalsToInTime (step affineVerifierTailRevProgram)
      inputStart (some inputDone)
      (affineInputShapeUntilFinishSteps script.inputShape) := by
    simpa [inputStart, inputDone, initialTail, inputTail,
      afterInitial, afterInput] using
      liftInput_run script.inputShape inputTail afterInitial
  have htoAccepting : EvalsToInTime (step affineVerifierTailRevProgram)
      inputDone (some acceptingStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have haccepting : EvalsToInTime (step affineVerifierTailRevProgram)
      acceptingStart (some conjunctionStart)
      (affineVerifierTailAcceptingSteps script.acceptingFrames) := by
    cases hframes : script.acceptingFrames with
    | none =>
        simpa [acceptingStart, conjunctionStart, acceptingInput,
          conjunctionInput, afterAccepting,
          affineVerifierTailAcceptingSteps,
          encodeAffineVerifierTailAccepting,
          affineVerifierTailAcceptingGateStream, hframes,
          affineVerifierTailOutputCfg, liftConjunctionCfg, relabelCfg,
          affineConjunctionLoopCfg, affineConjunctionCfg,
          affineVerifierTailCfg] using
          (show EvalsToInTime (step affineVerifierTailRevProgram)
            acceptingStart (some conjunctionStart) 2 from
              ⟨⟨2, by
                simp only [acceptingStart, conjunctionStart, acceptingInput,
                  conjunctionInput, afterAccepting,
                  encodeAffineVerifierTailAccepting,
                  affineVerifierTailAcceptingGateStream, hframes]
                rfl⟩, le_rfl⟩)
    | some frames =>
        let eqStart := liftAcceptingCfg (affineEqFinLoopCfg
          (encodeAffineEqFinFrames frames ++ .separator :: conjunctionInput)
          afterInput)
        let eqDone := liftAcceptingCfg (eqBoundaryFinishCfg
          conjunctionInput
          ((affineEqFinGateStream frames).reverse ++ afterInput))
        have henter : EvalsToInTime (step affineVerifierTailRevProgram)
            acceptingStart (some eqStart) 2 := ⟨⟨2, by
              simp only [acceptingStart, eqStart, acceptingInput,
                conjunctionInput, encodeAffineVerifierTailAccepting, hframes]
              simp only [List.append_assoc, List.singleton_append]
              rfl⟩, le_rfl⟩
        have heq : EvalsToInTime (step affineVerifierTailRevProgram)
            eqStart (some eqDone) (affineEqFinUntilFinishSteps frames) := by
          simpa [eqStart, eqDone] using
            liftAccepting_run frames conjunctionInput afterInput
        have hexit : EvalsToInTime (step affineVerifierTailRevProgram)
            eqDone (some conjunctionStart) 1 := ⟨⟨1, by
              simp only [eqDone, conjunctionStart, conjunctionInput,
                afterAccepting, affineVerifierTailAcceptingGateStream,
                hframes]
              rfl⟩, le_rfl⟩
        let throughEq := EvalsToInTime.trans
          (step affineVerifierTailRevProgram) 2 _ _ eqStart _ henter heq
        let full := EvalsToInTime.trans
          (step affineVerifierTailRevProgram) _ 1 _ eqDone _ throughEq hexit
        change EvalsToInTime (step affineVerifierTailRevProgram)
          acceptingStart (some conjunctionStart)
            (affineEqFinUntilFinishSteps frames + 3)
        rw [show affineEqFinUntilFinishSteps frames + 3 =
            1 + (affineEqFinUntilFinishSteps frames + 2) by omega]
        exact full
  have hconjunction : EvalsToInTime (step affineVerifierTailRevProgram)
      conjunctionStart (some conjunctionDone)
      (affineConjunctionUntilFinishSteps script.conjunctionFrame) := by
    simpa [conjunctionStart, conjunctionDone, conjunctionInput,
      outputInput, afterAccepting, afterConjunction] using
      liftConjunction_run script.conjunctionFrame outputInput afterAccepting
  have htoOutput : EvalsToInTime (step affineVerifierTailRevProgram)
      conjunctionDone (some outputStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have houtput : EvalsToInTime (step affineVerifierTailRevProgram)
      outputStart
      (some (haltCfg affineVerifierTailRevProgram
        ((.outputMark :: encNat script.outputWire).reverse ++
          afterConjunction)))
      (2 * script.outputWire + 4) := by
    simpa [outputStart, outputInput] using
      affineVerifierTail_output_run script.outputWire afterConjunction
  let t₁ := EvalsToInTime.trans (step affineVerifierTailRevProgram) _ 1 _
    initialDone _ hinitial htoInput
  let t₂ := EvalsToInTime.trans (step affineVerifierTailRevProgram) _ _ _
    inputStart _ t₁ hinput
  let t₃ := EvalsToInTime.trans (step affineVerifierTailRevProgram) _ 1 _
    inputDone _ t₂ htoAccepting
  let t₄ := EvalsToInTime.trans (step affineVerifierTailRevProgram) _ _ _
    acceptingStart _ t₃ haccepting
  let t₅ := EvalsToInTime.trans (step affineVerifierTailRevProgram) _ _ _
    conjunctionStart _ t₄ hconjunction
  let t₆ := EvalsToInTime.trans (step affineVerifierTailRevProgram) _ 1 _
    conjunctionDone _ t₅ htoOutput
  let full := EvalsToInTime.trans (step affineVerifierTailRevProgram) _ _ _
    outputStart _ t₆ houtput
  convert full using 1
  · simp [affineVerifierTailGateStream, afterInitial, afterInput,
      afterAccepting, afterConjunction, List.reverse_append,
      List.append_assoc]
  · simp [affineVerifierTailRevSteps]
    omega

/-- Coarse polynomial envelope in the exact combined runtime encoding. -/
theorem affineVerifierTailRev_steps_le (script : AffineVerifierTailScript) :
    affineVerifierTailRevSteps script ≤
      5000 * (encodeAffineVerifierTailScript script).length ^ 2 + 100 := by
  let a := (encodeAffineEqFinFrames script.initialFrames).length
  let b := (encodeAffineInputShapeScript script.inputShape).length
  let c := (encodeAffineVerifierTailAccepting script.acceptingFrames).length
  let d := (encodeAffineConjunctionFrame script.conjunctionFrame).length
  let e := (encodeUnaryFrameBlock script.outputWire).length
  let n := (encodeAffineVerifierTailScript script).length
  have hn : n = a + 1 + b + 1 + c + d + e := by
    simp [n, a, b, c, d, e, encodeAffineVerifierTailScript]
    omega
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  have hc : c ≤ n := by omega
  have hd : d ≤ n := by omega
  have he : e ≤ n := by omega
  have hnpos : 1 ≤ n := by omega
  have hiBase := affineEqFinRev_steps_le script.initialFrames
  have hi : affineEqFinUntilFinishSteps script.initialFrames ≤
      113 * a + 3 := by
    calc
      affineEqFinUntilFinishSteps script.initialFrames ≤
          affineEqFinRevSteps script.initialFrames := by
            simp [affineEqFinRevSteps]
      _ ≤ 113 * a + 3 := by simpa [a] using hiBase
  have hbBase := affineInputShapeRev_steps_le script.inputShape
  have hinput : affineInputShapeUntilFinishSteps script.inputShape ≤
      1200 * b ^ 2 + 20 := by
    calc
      affineInputShapeUntilFinishSteps script.inputShape ≤
          affineInputShapeRevSteps script.inputShape := by
            simp [affineInputShapeRevSteps]
      _ ≤ 1200 * b ^ 2 + 20 := by simpa [b] using hbBase
  have haAccept : affineVerifierTailAcceptingSteps script.acceptingFrames ≤
      113 * c + 6 := by
    cases hframes : script.acceptingFrames with
    | none =>
        simp [affineVerifierTailAcceptingSteps,
          encodeAffineVerifierTailAccepting, c, hframes]
    | some frames =>
        have h := affineEqFinRev_steps_le frames
        have hu : affineEqFinUntilFinishSteps frames ≤
            113 * (encodeAffineEqFinFrames frames).length + 3 := by
          calc
            affineEqFinUntilFinishSteps frames ≤
                affineEqFinRevSteps frames := by
                  simp [affineEqFinRevSteps]
            _ ≤ 113 * (encodeAffineEqFinFrames frames).length + 3 := h
        have hcLen : c = (encodeAffineEqFinFrames frames).length + 2 := by
          simp [c, encodeAffineVerifierTailAccepting, hframes]
        simp [affineVerifierTailAcceptingSteps, hframes]
        omega
  have hcBase := affineConjunctionRev_steps_le script.conjunctionFrame
  have hconjunction :
      affineConjunctionUntilFinishSteps script.conjunctionFrame ≤
        1000 * d ^ 2 + 2 := by
    calc
      affineConjunctionUntilFinishSteps script.conjunctionFrame ≤
          affineConjunctionRevSteps script.conjunctionFrame := by
            simp [affineConjunctionRevSteps]
      _ ≤ 1000 * d ^ 2 + 2 := by simpa [d] using hcBase
  have heq : e = script.outputWire + 1 := by
    simp [e, encodeUnaryFrameBlock]
  have hasquare : a ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left ha 2
  have hbsquare : b ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hb 2
  have hcsquare : c ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hc 2
  have hdsquare : d ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hd 2
  have hlinear : 400 * n ≤ 400 * n ^ 2 := by nlinarith
  simp only [affineVerifierTailRevSteps]
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
