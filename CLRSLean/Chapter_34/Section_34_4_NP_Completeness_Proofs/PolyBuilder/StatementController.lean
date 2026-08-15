import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Statement

/-!
# Fixed controller skeleton for tagged statement scripts

This controller embeds the existing arbitrary-OR and finite-mux programs under
one finite label type.  At their clean outer-loop boundaries it recognizes the
next statement phase tag, clears the consumed tag, and enters the next
component without halting.  Contextual component-run theorems are proved in a
later layer; this file fixes and tests the actual transition protocol.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Embed a unary component callback into the tagged statement alphabet. -/
def affineStmtDataNext {Λ Μ : Type} (tag : Λ → Μ) (invalid : Μ)
    (next : UnaryFrameSym → Λ) : AffineStmtScriptSym → Μ
  | .data symbol => tag (next symbol)
  | _ => invalid

/-- Structural embedding of a unary component instruction. -/
def affineStmtRelabelOp {Λ Μ : Type} (tag : Λ → Μ) (invalid : Μ) :
    Op UnaryFrameSym CircuitSym Λ → Op AffineStmtScriptSym CircuitSym Μ
  | .pushOutput symbol next => .pushOutput symbol (tag next)
  | .pushWork₁ symbol next => .pushWork₁ (.data symbol) (tag next)
  | .pushWork₂ symbol next => .pushWork₂ (.data symbol) (tag next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .popInput nextEmpty nextMoved =>
      .popInput (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (tag nextEmpty) (affineStmtDataNext tag invalid nextMoved)
  | .inc₁ next => .inc₁ (tag next)
  | .inc₂ next => .inc₂ (tag next)
  | .inc₃ next => .inc₃ (tag next)
  | .dec₁ nextZero nextSucc => .dec₁ (tag nextZero) (tag nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (tag nextZero) (tag nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (tag nextZero) (tag nextSucc)
  | .jump next => .jump (tag next)
  | .halt => .halt

inductive AffineStmtControllerLabel
  | dispatch
  | clearOneHotMap
  | clearOneHotPredicate
  | clearOneHotPairMap
  | clearPop
  | clearMux
  | orFin (label : AffineOrFinLabel)
  | muxFin (label : AffineMuxFinLabel)
  | finish
  | invalid
deriving DecidableEq, Fintype

/-- Continuation selected after consuming one phase tag. -/
def affineStmtTagTarget : AffineStmtScriptSym → AffineStmtControllerLabel
  | .oneHotMap => .clearOneHotMap
  | .oneHotPredicate => .clearOneHotPredicate
  | .oneHotPairMap => .clearOneHotPairMap
  | .pop => .clearPop
  | .mux => .clearMux
  | .data _ => .invalid

/-- Boundary callback for the arbitrary-OR check loop. -/
def affineStmtOrCheckTarget : AffineStmtScriptSym → AffineStmtControllerLabel
  | .data .frameEnd => .orFin .clearMarker
  | .data .separator => .orFin .familyCloseClear
  | .data .tick => .orFin .invalid
  | tag => affineStmtTagTarget tag

/-- Boundary callback for the arbitrary-OR family loop. -/
def affineStmtOrFamilyTarget : AffineStmtScriptSym → AffineStmtControllerLabel
  | .data .separator => .orFin .familyOpenClear
  | .data _ => .orFin .invalid
  | tag => affineStmtTagTarget tag

/-- Boundary callback for the finite-mux coordinate loop. -/
def affineStmtMuxCheckTarget : AffineStmtScriptSym → AffineStmtControllerLabel
  | .data .frameEnd => .muxFin .clearMarker
  | .data _ => .muxFin .invalid
  | tag => affineStmtTagTarget tag

/-- One fixed program executes every tagged statement phase kind.  Runtime
dimensions and wire operands occur only in the input symbols. -/
def affineStmtRevProgram : Program AffineStmtScriptSym CircuitSym where
  Label := AffineStmtControllerLabel
  main := .dispatch
  op
    | .dispatch => .popInput .finish affineStmtTagTarget
    | .clearOneHotMap =>
        .popWork₁ (.orFin .familyCheck) (fun _ => .invalid)
    | .clearOneHotPredicate =>
        .popWork₁ (.orFin .seed) (fun _ => .invalid)
    | .clearOneHotPairMap =>
        .popWork₁ (.orFin .andCheck) (fun _ => .invalid)
    | .clearPop =>
        .popWork₁ (.orFin .check) (fun _ => .invalid)
    | .clearMux =>
        .popWork₁ (.muxFin (.loader .selectorNot unaryTripleLoaderProgram.main))
          (fun _ => .invalid)
    | .orFin .check => .popInput (.orFin .finish) affineStmtOrCheckTarget
    | .orFin .familyCheck =>
        .popInput (.orFin .finish) affineStmtOrFamilyTarget
    | .orFin .finish => .jump .finish
    | .orFin .invalid => .halt
    | .orFin label => affineStmtRelabelOp .orFin .invalid
        (affineOrFinRevProgram.op label)
    | .muxFin .check =>
        .popInput (.muxFin .finish) affineStmtMuxCheckTarget
    | .muxFin .finish => .jump .finish
    | .muxFin .invalid => .halt
    | .muxFin label => affineStmtRelabelOp .muxFin .invalid
        (affineMuxFinRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

/-- Embed a pure unary component configuration into the tagged controller. -/
def affineStmtRelabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineStmtControllerLabel) (c : BuilderCfg P) :
    BuilderCfg affineStmtRevProgram where
  label := c.label.map tag
  buffer₁ := c.buffer₁.map .data
  buffer₂ := c.buffer₂.map .data
  test := c.test
  input := c.input.map .data
  output := c.output
  work₁ := c.work₁.map .data
  work₂ := c.work₂.map .data
  counter₁ := c.counter₁
  counter₂ := c.counter₂
  counter₃ := c.counter₃

def affineStmtLiftOrCfg (c : BuilderCfg affineOrFinRevProgram) :
    BuilderCfg affineStmtRevProgram :=
  affineStmtRelabelCfg .orFin c

def affineStmtLiftMuxCfg (c : BuilderCfg affineMuxFinRevProgram) :
    BuilderCfg affineStmtRevProgram :=
  affineStmtRelabelCfg .muxFin c

theorem affineStmtRelabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineStmtControllerLabel)
    (op : Op UnaryFrameSym CircuitSym P.Label) (c : BuilderCfg P) :
    stepOp (affineStmtRelabelOp tag AffineStmtControllerLabel.invalid op)
        (affineStmtRelabelCfg tag c) =
      affineStmtRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases input <;> cases work₁ <;> cases work₂ <;>
    cases counter₁ <;> cases counter₂ <;> cases counter₃ <;>
    cases op <;> rfl

private theorem affineStmt_op_orFin (label : AffineOrFinLabel)
    (hcheck : label ≠ .check) (hfamily : label ≠ .familyCheck)
    (hfinish : label ≠ .finish) :
    affineStmtRevProgram.op (.orFin label) =
      affineStmtRelabelOp .orFin .invalid
        (affineOrFinRevProgram.op label) := by
  cases label <;> simp_all [affineStmtRevProgram, affineOrFinRevProgram,
    affineStmtRelabelOp]

private theorem affineStmt_op_muxFin (label : AffineMuxFinLabel)
    (hcheck : label ≠ .check) (hfinish : label ≠ .finish) :
    affineStmtRevProgram.op (.muxFin label) =
      affineStmtRelabelOp .muxFin .invalid
        (affineMuxFinRevProgram.op label) := by
  cases label <;> simp_all [affineStmtRevProgram, affineMuxFinRevProgram,
    affineStmtRelabelOp]

/-- Pure unary OR-controller steps are simulated exactly until its clean
finish label; statement tags only extend the behavior at outer boundaries. -/
theorem affineStmtLiftOr_step (c : BuilderCfg affineOrFinRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineStmtRevProgram (affineStmtLiftOrCfg c) =
      Option.map affineStmtLiftOrCfg (step affineOrFinRevProgram c) := by
  unfold step
  rw [show (affineStmtLiftOrCfg c).label =
    c.label.map .orFin by rfl]
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
        | cons head tail => cases head <;> rfl
      by_cases hfamily : label = .familyCheck
      · subst label
        rcases c with
          ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
            counter₁, counter₂, counter₃⟩
        simp only at hlabel
        subst label
        cases input with
        | nil => rfl
        | cons head tail => cases head <;> rfl
      rw [affineStmt_op_orFin label hcheck hfamily hfinish]
      change some (stepOp
          (affineStmtRelabelOp AffineStmtControllerLabel.orFin
            AffineStmtControllerLabel.invalid
            (affineOrFinRevProgram.op label))
          (affineStmtLiftOrCfg c)) =
        some (affineStmtLiftOrCfg
          (stepOp (affineOrFinRevProgram.op label) c))
      exact congrArg some
        (affineStmtRelabel_stepOp AffineStmtControllerLabel.orFin
          (affineOrFinRevProgram.op label) c)

/-- Pure unary mux-controller steps are simulated exactly until finish. -/
theorem affineStmtLiftMux_step (c : BuilderCfg affineMuxFinRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineStmtRevProgram (affineStmtLiftMuxCfg c) =
      Option.map affineStmtLiftMuxCfg (step affineMuxFinRevProgram c) := by
  unfold step
  rw [show (affineStmtLiftMuxCfg c).label =
    c.label.map .muxFin by rfl]
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
        | cons head tail => cases head <;> rfl
      rw [affineStmt_op_muxFin label hcheck hfinish]
      change some (stepOp
          (affineStmtRelabelOp AffineStmtControllerLabel.muxFin
            AffineStmtControllerLabel.invalid
            (affineMuxFinRevProgram.op label))
          (affineStmtLiftMuxCfg c)) =
        some (affineStmtLiftMuxCfg
          (stepOp (affineMuxFinRevProgram.op label) c))
      exact congrArg some
        (affineStmtRelabel_stepOp AffineStmtControllerLabel.muxFin
          (affineMuxFinRevProgram.op label) c)

private theorem affineStmt_iterate_bind_none {σ : Type}
    (f : σ → Option σ) (n : Nat) :
    (flip Option.bind f)^[n] (none : Option σ) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem affineStmt_haltExit_no_return
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt) (a b : BuilderCfg P)
    (ha : a.label = some exit) (hb : b.label = some exit) (n : Nat) :
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
      rw [hnone, affineStmt_iterate_bind_none]
      simp

private theorem affineStmt_lift_iterations_to_finish
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg affineStmtRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineStmtRevProgram (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineStmtRevProgram))^[n]
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
      change (flip Option.bind (step affineStmtRevProgram))^[n]
        (step affineStmtRevProgram (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact affineStmt_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, affineStmt_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

def affineStmtLiftOr_runToFinish {a b : BuilderCfg affineOrFinRevProgram}
    (hb : b.label = some .finish) (m : Nat)
    (sourceRun : EvalsToInTime (step affineOrFinRevProgram)
      a (some b) m) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtLiftOrCfg a) (some (affineStmtLiftOrCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineStmt_lift_iterations_to_finish AffineOrFinLabel.finish rfl
    affineStmtLiftOrCfg affineStmtLiftOr_step hb sourceRun.steps
      sourceRun.evals_in_steps

def affineStmtLiftMux_runToFinish {a b : BuilderCfg affineMuxFinRevProgram}
    (hb : b.label = some .finish) (m : Nat)
    (sourceRun : EvalsToInTime (step affineMuxFinRevProgram)
      a (some b) m) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtLiftMuxCfg a) (some (affineStmtLiftMuxCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineStmt_lift_iterations_to_finish AffineMuxFinLabel.finish rfl
    affineStmtLiftMuxCfg affineStmtLiftMux_step hb sourceRun.steps
      sourceRun.evals_in_steps

/-- Fieldwise configuration surface for the statement controller. -/
def affineStmtCfg (label : AffineStmtControllerLabel)
    (buffer₁ buffer₂ : Option AffineStmtScriptSym) (test : Bool)
    (input : List AffineStmtScriptSym) (output : List CircuitSym)
    (work₁ work₂ : List AffineStmtScriptSym)
    (first second third : List Unit) : BuilderCfg affineStmtRevProgram where
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

/-- Clean public entry for a complete tagged statement script. -/
def affineStmtLoopCfg (input : List AffineStmtScriptSym)
    (output : List CircuitSym) : BuilderCfg affineStmtRevProgram :=
  affineStmtCfg .dispatch none none false input output [] [] [] [] []

/-- Clean component entry after the phase tag has been consumed and cleared. -/
def affineStmtPhaseEntryCfg (phase : AffineStmtPhase)
    (tail : List AffineStmtScriptSym) (output : List CircuitSym) :
    BuilderCfg affineStmtRevProgram :=
  let dataTail := match phase with
    | .oneHotMap groups => (encodeAffineOrFinGroups groups).map .data ++ tail
    | .oneHotPredicate frames =>
        (encodeAffineOrFinFrames frames).map .data ++ tail
    | .oneHotPairMap andFrames orGroups =>
        (encodeAffineAndThenOrInput andFrames orGroups).map .data ++ tail
    | .pop frames => (encodeAffineOrFinFrames frames).map .data ++ tail
    | .mux selector frames =>
        (encodeAffineMuxFinFrames selector frames).map .data ++ tail
  let label := match phase with
    | .oneHotMap _ => .orFin .familyCheck
    | .oneHotPredicate _ => .orFin .seed
    | .oneHotPairMap _ _ => .orFin .andCheck
    | .pop _ => .orFin .check
    | .mux _ _ => .muxFin (.loader .selectorNot unaryTripleLoaderProgram.main)
  affineStmtCfg label none none false dataTail output [] [] [] [] []

/-- Dispatching a well-formed phase tag takes exactly two steps and leaves a
clean component entry with the remainder of the tagged script untouched. -/
def affineStmt_dispatch_phase (phase : AffineStmtPhase)
    (tail : List AffineStmtScriptSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtLoopCfg (encodeAffineStmtPhase phase ++ tail) output)
      (some (affineStmtPhaseEntryCfg phase tail output)) 2 := by
  cases phase <;> exact ⟨⟨2, rfl⟩, le_rfl⟩

/-- The empty script reaches the public halted configuration in two steps. -/
def affineStmt_empty_run (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtLoopCfg [] output)
      (some (haltCfg affineStmtRevProgram output)) 2 :=
  ⟨⟨2, rfl⟩, le_rfl⟩

/-- Exact controller cost of one final phase, including the public finish
bridge and halt. -/
def affineStmtPhaseLastSteps (phase : AffineStmtPhase) : Nat :=
  affineStmtPhaseStandaloneSteps phase + 1

/-- Every phase kind executes exactly when it is the final script phase.  This
is the no-suffix base case for contextual phase composition. -/
def affineStmt_phase_last_run (phase : AffineStmtPhase)
    (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtPhaseEntryCfg phase [] output)
      (some (haltCfg affineStmtRevProgram
        ((affineStmtPhaseGateStream phase).reverse ++ output)))
      (affineStmtPhaseLastSteps phase) := by
  cases phase with
  | oneHotMap groups =>
      let gateOutput := (affineOrFinFamilyGateStream groups).reverse ++ output
      have sourceRun := affineOrFinFamily_runToFinish groups output
      have hlift := affineStmtLiftOr_runToFinish rfl _ sourceRun
      have hhalt : EvalsToInTime (step affineStmtRevProgram)
          (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput))
          (some (haltCfg affineStmtRevProgram gateOutput)) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step affineStmtRevProgram)
        (affineOrFinFamilyUntilFinishSteps groups) 2 _
        (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput)) _
        (by simpa [gateOutput] using hlift) hhalt
      convert full using 1
      · simp [affineStmtPhaseEntryCfg, affineStmtLiftOrCfg,
          affineStmtRelabelCfg, affineOrFinFamilyLoopCfg, affineOrFinCfg,
          affineStmtCfg]
      · simp [affineStmtPhaseGateStream, gateOutput]
      · simp [affineStmtPhaseLastSteps, affineStmtPhaseStandaloneSteps,
          affineOrFinFamilyRevSteps]
        omega
  | oneHotPredicate frames =>
      let gateOutput := (affineOrFinGateStream frames).reverse ++ output
      have sourceRun := affineOrFin_runToFinish frames output
      have hlift := affineStmtLiftOr_runToFinish rfl _ sourceRun
      have hhalt : EvalsToInTime (step affineStmtRevProgram)
          (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput))
          (some (haltCfg affineStmtRevProgram gateOutput)) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step affineStmtRevProgram)
        (affineOrFinUntilFinishSteps frames) 2 _
        (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput)) _
        (by simpa [gateOutput] using hlift) hhalt
      convert full using 1
      · simp [affineStmtPhaseEntryCfg, affineStmtLiftOrCfg,
          affineStmtRelabelCfg, affineOrFinLoopCfg, affineOrFinCfg,
          affineStmtCfg]
      · simp [affineStmtPhaseGateStream, gateOutput]
      · simp [affineStmtPhaseLastSteps, affineStmtPhaseStandaloneSteps,
          affineOrFinRevSteps]
        omega
  | oneHotPairMap andFrames orGroups =>
      let gateOutput :=
        (affineAndThenOrGateStream andFrames orGroups).reverse ++ output
      have sourceRun := affineAndThenOr_runToFinish andFrames orGroups output
      have hlift := affineStmtLiftOr_runToFinish rfl _ sourceRun
      have hhalt : EvalsToInTime (step affineStmtRevProgram)
          (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput))
          (some (haltCfg affineStmtRevProgram gateOutput)) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step affineStmtRevProgram)
        (affineAndThenOrUntilFinishSteps andFrames orGroups) 2 _
        (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput)) _
        (by simpa [gateOutput] using hlift) hhalt
      convert full using 1
      · simp [affineStmtPhaseEntryCfg, affineStmtLiftOrCfg,
          affineStmtRelabelCfg, affineAndFinLoopCfg, affineOrFinCfg,
          affineStmtCfg]
      · simp [affineStmtPhaseGateStream, gateOutput]
      · simp [affineStmtPhaseLastSteps, affineStmtPhaseStandaloneSteps,
          affineAndThenOrRevSteps]
        omega
  | pop frames =>
      let gateOutput := (affineOrFinNoSeedGateStream frames).reverse ++ output
      have sourceRun := affineOrFinNoSeed_runToFinish frames output
      have hlift := affineStmtLiftOr_runToFinish rfl _ sourceRun
      have hhalt : EvalsToInTime (step affineStmtRevProgram)
          (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput))
          (some (haltCfg affineStmtRevProgram gateOutput)) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step affineStmtRevProgram)
        (affineOrFinFoldSteps frames) 2 _
        (affineStmtLiftOrCfg (affineOrFinFinishCfg gateOutput)) _
        (by simpa [gateOutput] using hlift) hhalt
      convert full using 1
      · simp [affineStmtPhaseEntryCfg, affineStmtLiftOrCfg,
          affineStmtRelabelCfg, affineOrFinCheckCfg, affineOrFinCfg,
          affineStmtCfg]
      · simp [affineStmtPhaseGateStream, gateOutput]
      · simp [affineStmtPhaseLastSteps, affineStmtPhaseStandaloneSteps,
          affineOrFinNoSeedRevSteps]
        omega
  | mux selector frames =>
      let gateOutput := (affineMuxFinGateStream selector frames).reverse ++ output
      have sourceRun := affineMuxFin_runToFinish selector frames output
      have hlift := affineStmtLiftMux_runToFinish rfl _ sourceRun
      have hhalt : EvalsToInTime (step affineStmtRevProgram)
          (affineStmtLiftMuxCfg (affineMuxFinFinishCfg gateOutput))
          (some (haltCfg affineStmtRevProgram gateOutput)) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step affineStmtRevProgram)
        (affineMuxFinUntilFinishSteps selector frames) 2 _
        (affineStmtLiftMuxCfg (affineMuxFinFinishCfg gateOutput)) _
        (by simpa [gateOutput] using hlift) hhalt
      convert full using 1
      · simp [affineStmtPhaseEntryCfg, affineStmtLiftMuxCfg,
          affineStmtRelabelCfg, affineMuxFinLoopCfg, affineMuxFinCfg,
          affineStmtCfg]
      · simp [affineStmtPhaseGateStream, gateOutput]
      · simp [affineStmtPhaseLastSteps, affineStmtPhaseStandaloneSteps,
          affineMuxFinRevSteps]
        omega

/-! ## Executable phase-boundary checks -/

/-- An empty pop phase redirects directly into the next tagged phase. -/
def affineStmt_emptyPop_redirect (next : AffineStmtPhase)
    (tail : List AffineStmtScriptSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtPhaseEntryCfg (.pop [])
        (encodeAffineStmtPhase next ++ tail) output)
      (some (affineStmtPhaseEntryCfg next tail output)) 2 := by
  cases next <;> exact ⟨⟨2, rfl⟩, le_rfl⟩

/-- An empty one-hot-map family redirects directly into the next tag. -/
def affineStmt_emptyOneHotMap_redirect (next : AffineStmtPhase)
    (tail : List AffineStmtScriptSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtPhaseEntryCfg (.oneHotMap [])
        (encodeAffineStmtPhase next ++ tail) output)
      (some (affineStmtPhaseEntryCfg next tail output)) 2 := by
  cases next <;> exact ⟨⟨2, rfl⟩, le_rfl⟩

/-- An empty predicate still emits its required false seed, then redirects. -/
def affineStmt_emptyPredicate_redirect (next : AffineStmtPhase)
    (tail : List AffineStmtScriptSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtPhaseEntryCfg (.oneHotPredicate [])
        (encodeAffineStmtPhase next ++ tail) output)
      (some (affineStmtPhaseEntryCfg next tail
        (.constFalseMark :: output))) 3 := by
  cases next <;> exact ⟨⟨3, rfl⟩, le_rfl⟩

/-- The empty pair-map consumes its AND-to-family delimiter and redirects. -/
def affineStmt_emptyPairMap_redirect (next : AffineStmtPhase)
    (tail : List AffineStmtScriptSym) (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtPhaseEntryCfg (.oneHotPairMap [] [])
        (encodeAffineStmtPhase next ++ tail) output)
      (some (affineStmtPhaseEntryCfg next tail output)) 4 := by
  cases next <;> exact ⟨⟨4, rfl⟩, le_rfl⟩

end CLRS.Chapter34.Turing.PolyBuilder
