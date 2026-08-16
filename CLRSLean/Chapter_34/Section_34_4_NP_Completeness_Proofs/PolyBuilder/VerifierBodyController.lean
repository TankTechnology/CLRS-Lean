import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityRowFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.VerifierTailController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-!
# Continuous Cook--Levin verifier-body controller

One fixed program executes every validity row, every local transition, and
the complete post-transition verifier tail.  The whole runtime script remains
pure unary data inside `AffineStmtScriptSym`; only the finite control records
which reusable component is active.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Runtime operands for the complete verifier body after the shared Boolean
pool. -/
structure AffineVerifierBodyScript where
  validityFrames : List AffineValidityRowFrame
  transitionScripts : List AffineTransitionScript
  tailScript : AffineVerifierTailScript

/-- Pure-unary verifier-body protocol.  The validity-family `frameEnd` is its
redirectable terminator; the following `separator` is reserved for the
transition-to-tail handoff. -/
def encodeAffineVerifierBodyUnary (script : AffineVerifierBodyScript) :
    List UnaryFrameSym :=
  encodeAffineValidityRowFamilyInput script.validityFrames ++
    encodeAffineTransitionFamilyUnary script.transitionScripts ++
    .separator :: encodeAffineVerifierTailScript script.tailScript

/-- Common-alphabet runtime encoding consumed by the fixed body controller. -/
def encodeAffineVerifierBodyScript (script : AffineVerifierBodyScript) :
    List AffineStmtScriptSym :=
  (encodeAffineVerifierBodyUnary script).map .data

/-- Exact forward circuit-byte stream emitted by the verifier body. -/
def affineVerifierBodyGateStream (script : AffineVerifierBodyScript) :
    List CircuitSym :=
  affineValidityRowFamilyGateStream script.validityFrames ++
    affineTransitionFamilyGateStream script.transitionScripts ++
    affineVerifierTailGateStream script.tailScript

inductive AffineVerifierBodyLabel
  | validity (label : AffineValidityRowFamilyLabel)
  | transition (label : AffineTransitionFamilyLabel)
  | transitionClear
  | tail (label : AffineVerifierTailLabel)
  | invalid
deriving DecidableEq, Fintype

/-- The ordinary transition-family marker keeps the reusable family loop
running; the reserved separator enters the verifier tail. -/
def affineVerifierBodyTransitionTarget :
    AffineStmtScriptSym → AffineVerifierBodyLabel
  | .data .frameEnd => .transition .clearStart
  | .data .separator => .transitionClear
  | _ => .transition .invalid

/-- One finite controller for the complete runtime-sized verifier body. -/
def affineVerifierBodyRevProgram : Program AffineStmtScriptSym CircuitSym where
  Label := AffineVerifierBodyLabel
  main := .validity affineValidityRowFamilyRevProgram.main
  op
    | .validity .finish =>
        .popWork₁ (.transition affineTransitionFamilyRevProgram.main)
          (fun _ => .invalid)
    | .validity label =>
        affineStmtRelabelOp .validity .invalid
          (affineValidityRowFamilyRevProgram.op label)
    | .transition .check =>
        .popInput (.transition .finish) affineVerifierBodyTransitionTarget
    | .transition label =>
        affineTransitionRelabelSameOp .transition
          (affineTransitionFamilyRevProgram.op label)
    | .transitionClear =>
        .popWork₁ (.tail affineVerifierTailRevProgram.main)
          (fun _ => .invalid)
    | .tail label =>
        affineStmtRelabelOp .tail .invalid
          (affineVerifierTailRevProgram.op label)
    | .invalid => .halt

def affineVerifierBodyCfg (label : AffineVerifierBodyLabel)
    (buffer₁ buffer₂ : Option AffineStmtScriptSym) (test : Bool)
    (input : List AffineStmtScriptSym) (output : List CircuitSym)
    (work₁ work₂ : List AffineStmtScriptSym)
    (first second third : List Unit) :
    BuilderCfg affineVerifierBodyRevProgram where
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

def affineVerifierBodyLoopCfg (input : List AffineStmtScriptSym)
    (output : List CircuitSym) : BuilderCfg affineVerifierBodyRevProgram :=
  affineVerifierBodyCfg
    (.validity affineValidityRowFamilyRevProgram.main)
    none none false input output [] [] [] [] []

private def liftUnaryCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineVerifierBodyLabel) (c : BuilderCfg P) :
    BuilderCfg affineVerifierBodyRevProgram where
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

private def liftTransitionCfg
    (c : BuilderCfg affineTransitionFamilyRevProgram) :
    BuilderCfg affineVerifierBodyRevProgram where
  label := c.label.map .transition
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

private theorem relabelUnary_stepOp
    {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineVerifierBodyLabel)
    (op : Op UnaryFrameSym CircuitSym P.Label) (c : BuilderCfg P) :
    stepOp (affineStmtRelabelOp tag AffineVerifierBodyLabel.invalid op)
        (liftUnaryCfg tag c) =
      liftUnaryCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases input <;> cases work₁ <;> cases work₂ <;>
    cases counter₁ <;> cases counter₂ <;> cases counter₃ <;>
    cases op <;> rfl

private theorem relabelTransition_stepOp
    (op : Op AffineStmtScriptSym CircuitSym AffineTransitionFamilyLabel)
    (c : BuilderCfg affineTransitionFamilyRevProgram) :
    stepOp (affineTransitionRelabelSameOp
        AffineVerifierBodyLabel.transition op)
        (liftTransitionCfg c) =
      liftTransitionCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases input <;> cases work₁ <;> cases work₂ <;>
    cases counter₁ <;> cases counter₂ <;> cases counter₃ <;>
    cases op <;> rfl

private theorem outer_op_validity (label : AffineValidityRowFamilyLabel)
    (hfinish : label ≠ .finish) :
    affineVerifierBodyRevProgram.op (.validity label) =
      affineStmtRelabelOp .validity .invalid
        (affineValidityRowFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineVerifierBodyRevProgram] <;> rfl

private theorem outer_op_tail (label : AffineVerifierTailLabel) :
    affineVerifierBodyRevProgram.op (.tail label) =
      affineStmtRelabelOp .tail .invalid
        (affineVerifierTailRevProgram.op label) := rfl

private theorem liftValidity_step
    (c : BuilderCfg affineValidityRowFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineVerifierBodyRevProgram (liftUnaryCfg .validity c) =
      Option.map (liftUnaryCfg .validity)
        (step affineValidityRowFamilyRevProgram c) := by
  unfold step
  rw [show (liftUnaryCfg AffineVerifierBodyLabel.validity c).label =
    c.label.map .validity by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hfinish : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [outer_op_validity label hfinish]
      exact congrArg some
        (relabelUnary_stepOp .validity
          (affineValidityRowFamilyRevProgram.op label) c)

private theorem liftTail_step (c : BuilderCfg affineVerifierTailRevProgram) :
    step affineVerifierBodyRevProgram (liftUnaryCfg .tail c) =
      Option.map (liftUnaryCfg .tail)
        (step affineVerifierTailRevProgram c) := by
  unfold step
  rw [show (liftUnaryCfg AffineVerifierBodyLabel.tail c).label =
    c.label.map .tail by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      rw [outer_op_tail label]
      exact congrArg some
        (relabelUnary_stepOp .tail
          (affineVerifierTailRevProgram.op label) c)

private theorem iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem haltExit_no_return {Γ Δ : Type} {P : Program Γ Δ}
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

private theorem liftValidity_iterations_to_finish
    {a b : BuilderCfg affineValidityRowFamilyRevProgram}
    (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind (step affineValidityRowFamilyRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineVerifierBodyRevProgram))^[n]
        (some (liftUnaryCfg .validity a)) =
          some (liftUnaryCfg .validity b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineValidityRowFamilyRevProgram))^[n]
        (step affineValidityRowFamilyRevProgram a) = some b at h
      change (flip Option.bind (step affineVerifierBodyRevProgram))^[n]
        (step affineVerifierBodyRevProgram (liftUnaryCfg .validity a)) =
          some (liftUnaryCfg .validity b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact haltExit_no_return AffineValidityRowFamilyLabel.finish
          AffineValidityRowFamilyLabel.finish rfl a b ha hb n h
      cases hsource : step affineValidityRowFamilyRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftValidity_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def liftValidity_run
    {a b : BuilderCfg affineValidityRowFamilyRevProgram}
    (hb : b.label = some .finish) (m : Nat)
    (sourceRun : EvalsToInTime (step affineValidityRowFamilyRevProgram)
      a (some b) m) :
    EvalsToInTime (step affineVerifierBodyRevProgram)
      (liftUnaryCfg .validity a) (some (liftUnaryCfg .validity b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact liftValidity_iterations_to_finish hb sourceRun.steps
    sourceRun.evals_in_steps

private theorem liftTail_iterations
    {a b : BuilderCfg affineVerifierTailRevProgram} : ∀ n : Nat,
    (flip Option.bind (step affineVerifierTailRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineVerifierBodyRevProgram))^[n]
        (some (liftUnaryCfg .tail a)) = some (liftUnaryCfg .tail b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineVerifierTailRevProgram))^[n]
        (step affineVerifierTailRevProgram a) = some b at h
      change (flip Option.bind (step affineVerifierBodyRevProgram))^[n]
        (step affineVerifierBodyRevProgram (liftUnaryCfg .tail a)) =
          some (liftUnaryCfg .tail b)
      cases hsource : step affineVerifierTailRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftTail_step a
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def liftTail_run
    {a b : BuilderCfg affineVerifierTailRevProgram} (m : Nat)
    (sourceRun : EvalsToInTime (step affineVerifierTailRevProgram)
      a (some b) m) :
    EvalsToInTime (step affineVerifierBodyRevProgram)
      (liftUnaryCfg .tail a) (some (liftUnaryCfg .tail b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact liftTail_iterations sourceRun.steps sourceRun.evals_in_steps

private def transitionBoundaryBad
    (c : BuilderCfg affineTransitionFamilyRevProgram) : Prop :=
  c.label = some .check ∧
    ∃ tail, c.input = .data .separator :: tail

private theorem liftTransition_step
    (c : BuilderCfg affineTransitionFamilyRevProgram)
    (hsafe : ¬ transitionBoundaryBad c) :
    step affineVerifierBodyRevProgram (liftTransitionCfg c) =
      Option.map liftTransitionCfg
        (step affineTransitionFamilyRevProgram c) := by
  unfold step
  rw [show (liftTransitionCfg c).label = c.label.map .transition by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
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
            | oneHotMap => rfl
            | oneHotPredicate => rfl
            | oneHotPairMap => rfl
            | pop => rfl
            | mux => rfl
            | data symbol =>
                cases symbol with
                | tick => rfl
                | frameEnd => rfl
                | separator =>
                    exfalso
                    apply hsafe
                    exact ⟨rfl, ⟨tail, rfl⟩⟩
      · have hop : affineVerifierBodyRevProgram.op (.transition label) =
            affineTransitionRelabelSameOp .transition
              (affineTransitionFamilyRevProgram.op label) := by
          cases label <;> simp_all [affineVerifierBodyRevProgram] <;> rfl
        rw [hop]
        exact congrArg some
          (relabelTransition_stepOp
            (affineTransitionFamilyRevProgram.op label) c)

private theorem transitionBoundaryBad_step
    (c : BuilderCfg affineTransitionFamilyRevProgram)
    (hbad : transitionBoundaryBad c) :
    ∃ d : BuilderCfg affineTransitionFamilyRevProgram,
      step affineTransitionFamilyRevProgram c = some d ∧
        d.label = some .invalid := by
  rcases hbad with ⟨hlabel, ⟨tail, hinput⟩⟩
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at hlabel hinput
  subst label
  subst input
  refine ⟨_, rfl, rfl⟩

private theorem liftTransition_iterations_avoiding
    {a b : BuilderCfg affineTransitionFamilyRevProgram}
    (hb : b.label = some .check) : ∀ n : Nat,
    (flip Option.bind (step affineTransitionFamilyRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineVerifierBodyRevProgram))^[n]
        (some (liftTransitionCfg a)) = some (liftTransitionCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simpa [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineTransitionFamilyRevProgram))^[n]
        (step affineTransitionFamilyRevProgram a) = some b at h
      change (flip Option.bind (step affineVerifierBodyRevProgram))^[n]
        (step affineVerifierBodyRevProgram (liftTransitionCfg a)) =
          some (liftTransitionCfg b)
      have hasafe : ¬ transitionBoundaryBad a := by
        intro hbad
        obtain ⟨d, hbadStep, hdlabel⟩ := transitionBoundaryBad_step a hbad
        cases n with
        | zero =>
            rw [hbadStep] at h
            injection h with hdb
            have hlabels := congrArg (fun cfg => cfg.label) hdb
            simp [hdlabel, hb] at hlabels
        | succ n =>
            rw [Function.iterate_succ_apply, hbadStep] at h
            change (flip Option.bind
              (step affineTransitionFamilyRevProgram))^[n]
                (step affineTransitionFamilyRevProgram d) = some b at h
            exact haltExit_no_return AffineTransitionFamilyLabel.invalid
              AffineTransitionFamilyLabel.check rfl
              d b hdlabel hb n h
      cases hsource : step affineTransitionFamilyRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftTransition_step a hasafe
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def liftTransition_run
    {a b : BuilderCfg affineTransitionFamilyRevProgram}
    (hb : b.label = some .check) (m : Nat)
    (sourceRun : EvalsToInTime (step affineTransitionFamilyRevProgram)
      a (some b) m) :
    EvalsToInTime (step affineVerifierBodyRevProgram)
      (liftTransitionCfg a) (some (liftTransitionCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact liftTransition_iterations_avoiding hb sourceRun.steps
    sourceRun.evals_in_steps

/-- Exact number of fixed-controller steps for the full verifier body. -/
def affineVerifierBodyRevSteps (script : AffineVerifierBodyScript) : Nat :=
  affineValidityRowFamilyUntilFinishSteps script.validityFrames + 1 +
    affineTransitionFamilyBodySteps script.transitionScripts + 2 +
    affineVerifierTailRevSteps script.tailScript

/-- Exact continuous execution of validity, transitions, and verifier tail. -/
def affineVerifierBody_run (script : AffineVerifierBodyScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineVerifierBodyRevProgram)
      (affineVerifierBodyLoopCfg
        (encodeAffineVerifierBodyScript script) output)
      (some (haltCfg affineVerifierBodyRevProgram
        ((affineVerifierBodyGateStream script).reverse ++ output)))
      (affineVerifierBodyRevSteps script) := by
  let tailInput := encodeAffineVerifierTailScript script.tailScript
  let transitionTail := .separator :: tailInput
  let validityTail :=
    encodeAffineTransitionFamilyUnary script.transitionScripts ++
      transitionTail
  let afterValidity :=
    (affineValidityRowFamilyGateStream script.validityFrames).reverse ++
      output
  let afterTransition :=
    (affineTransitionFamilyGateStream script.transitionScripts).reverse ++
      afterValidity
  let validityDone := liftUnaryCfg .validity
    (affineValidityRowFamilyFinishCfg validityTail afterValidity)
  let transitionStart := liftTransitionCfg
    (affineTransitionFamilyLoopCfg
      (encodeAffineTransitionFamily script.transitionScripts ++
        transitionTail.map .data) afterValidity)
  let transitionDone := liftTransitionCfg
    (affineTransitionFamilyLoopCfg (transitionTail.map .data)
      afterTransition)
  let tailStart := liftUnaryCfg .tail
    (affineVerifierTailLoopCfg tailInput afterTransition)
  have hvalidSource := affineValidityRowFamily_runToFinish
    script.validityFrames validityTail output
  have hvalid : EvalsToInTime (step affineVerifierBodyRevProgram)
      (affineVerifierBodyLoopCfg
        (encodeAffineVerifierBodyScript script) output)
      (some validityDone)
      (affineValidityRowFamilyUntilFinishSteps
        script.validityFrames) := by
    have hlift := liftValidity_run rfl _ hvalidSource
    simpa [affineVerifierBodyLoopCfg, encodeAffineVerifierBodyScript,
      encodeAffineVerifierBodyUnary, encodeAffineValidityRowFamilyInput,
      validityDone, validityTail, transitionTail, tailInput, afterValidity,
      liftUnaryCfg, affineValidityRowFamilyLoopCfg,
      affineValidityRowFamilyCfg, affineVerifierBodyCfg,
      affineValidityRowFamilyRevProgram,
      List.map_append, List.append_assoc] using hlift
  have htoTransition : EvalsToInTime (step affineVerifierBodyRevProgram)
      validityDone (some transitionStart) 1 := by
    exact ⟨⟨1, by
      simp only [validityDone, transitionStart, validityTail,
        transitionTail, afterValidity, liftUnaryCfg, liftTransitionCfg,
        affineValidityRowFamilyFinishCfg, affineValidityRowFamilyCfg,
        affineTransitionFamilyLoopCfg, affineTransitionFamilyCfg]
      simp [encodeAffineTransitionFamily, List.map_append]
      rfl⟩, le_rfl⟩
  have htransitionSource := affineTransitionFamily_runToCheckWithTail
    script.transitionScripts transitionTail afterValidity
  have htransition : EvalsToInTime (step affineVerifierBodyRevProgram)
      transitionStart (some transitionDone)
      (affineTransitionFamilyBodySteps
        script.transitionScripts) := by
    simpa [transitionStart, transitionDone, afterTransition] using
      liftTransition_run rfl _ htransitionSource
  have htoTail : EvalsToInTime (step affineVerifierBodyRevProgram)
      transitionDone (some tailStart) 2 := by
    exact ⟨⟨2, by
      simp only [transitionDone, tailStart, transitionTail, tailInput,
        afterTransition, liftTransitionCfg, liftUnaryCfg,
        affineTransitionFamilyLoopCfg, affineTransitionFamilyCfg,
        affineVerifierTailLoopCfg, affineVerifierTailCfg]
      rfl⟩, le_rfl⟩
  have htailSource := affineVerifierTail_run script.tailScript afterTransition
  have htail : EvalsToInTime (step affineVerifierBodyRevProgram)
      tailStart
      (some (haltCfg affineVerifierBodyRevProgram
        ((affineVerifierTailGateStream script.tailScript).reverse ++
          afterTransition)))
      (affineVerifierTailRevSteps script.tailScript) := by
    have hlift := liftTail_run _ htailSource
    simpa [tailStart, tailInput, liftUnaryCfg, haltCfg] using hlift
  let throughValidityRaw := EvalsToInTime.trans
    (step affineVerifierBodyRevProgram)
    (affineValidityRowFamilyUntilFinishSteps script.validityFrames) 1
    _ validityDone _ hvalid htoTransition
  have throughValidity : EvalsToInTime (step affineVerifierBodyRevProgram)
      (affineVerifierBodyLoopCfg
        (encodeAffineVerifierBodyScript script) output)
      (some transitionStart)
      (affineValidityRowFamilyUntilFinishSteps script.validityFrames + 1) := by
    simpa [Nat.add_comm] using throughValidityRaw
  let throughTransitionRaw := EvalsToInTime.trans
    (step affineVerifierBodyRevProgram)
    (affineValidityRowFamilyUntilFinishSteps script.validityFrames + 1)
    (affineTransitionFamilyBodySteps script.transitionScripts)
    _ transitionStart _ throughValidity htransition
  have throughTransition : EvalsToInTime (step affineVerifierBodyRevProgram)
      (affineVerifierBodyLoopCfg
        (encodeAffineVerifierBodyScript script) output)
      (some transitionDone)
      (affineValidityRowFamilyUntilFinishSteps script.validityFrames + 1 +
        affineTransitionFamilyBodySteps script.transitionScripts) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      throughTransitionRaw
  let throughBoundaryRaw := EvalsToInTime.trans
    (step affineVerifierBodyRevProgram)
    (affineValidityRowFamilyUntilFinishSteps script.validityFrames + 1 +
      affineTransitionFamilyBodySteps script.transitionScripts)
    2 _ transitionDone _ throughTransition htoTail
  have throughBoundary : EvalsToInTime (step affineVerifierBodyRevProgram)
      (affineVerifierBodyLoopCfg
        (encodeAffineVerifierBodyScript script) output)
      (some tailStart)
      (affineValidityRowFamilyUntilFinishSteps script.validityFrames + 1 +
        affineTransitionFamilyBodySteps script.transitionScripts + 2) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      throughBoundaryRaw
  let fullRaw := EvalsToInTime.trans
    (step affineVerifierBodyRevProgram)
    (affineValidityRowFamilyUntilFinishSteps script.validityFrames + 1 +
      affineTransitionFamilyBodySteps script.transitionScripts + 2)
    (affineVerifierTailRevSteps script.tailScript)
    _ tailStart _ throughBoundary htail
  have full : EvalsToInTime (step affineVerifierBodyRevProgram)
      (affineVerifierBodyLoopCfg
        (encodeAffineVerifierBodyScript script) output)
      (some (haltCfg affineVerifierBodyRevProgram
        ((affineVerifierTailGateStream script.tailScript).reverse ++
          afterTransition)))
      (affineVerifierBodyRevSteps script) := by
    simpa [affineVerifierBodyRevSteps, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using fullRaw
  convert full using 1
  · simp [affineVerifierBodyGateStream, afterTransition, afterValidity,
      List.reverse_append, List.append_assoc]

/-- Coarse polynomial envelope in the exact encoded body length. -/
theorem affineVerifierBody_steps_le (script : AffineVerifierBodyScript) :
    affineVerifierBodyRevSteps script ≤
      10000 * (encodeAffineVerifierBodyScript script).length ^ 2 + 200 := by
  let v := (encodeAffineValidityRowFamilyInput
    script.validityFrames).length
  let t := (encodeAffineTransitionFamily
    script.transitionScripts).length
  let u := (encodeAffineVerifierTailScript script.tailScript).length
  let n := (encodeAffineVerifierBodyScript script).length
  have hn : n = v + t + 1 + u := by
    simp [n, v, t, u, encodeAffineVerifierBodyScript,
      encodeAffineVerifierBodyUnary, encodeAffineTransitionFamily]
    omega
  have hv : v ≤ n := by omega
  have ht : t ≤ n := by omega
  have hu : u ≤ n := by omega
  have hnpos : 1 ≤ n := by omega
  have hvalidBase := affineValidityRowFamilyRev_steps_le
    script.validityFrames
  have hvalid :
      affineValidityRowFamilyUntilFinishSteps script.validityFrames ≤
        2600 * v ^ 2 + 2 := by
    calc
      affineValidityRowFamilyUntilFinishSteps script.validityFrames ≤
          affineValidityRowFamilyRevSteps script.validityFrames := by
            simp [affineValidityRowFamilyRevSteps]
      _ ≤ 2600 * v ^ 2 + 2 := by simpa [v] using hvalidBase
  have htransitionBase := affineTransitionFamilyBody_steps_le
    script.transitionScripts
  have htransition :
      affineTransitionFamilyBodySteps script.transitionScripts ≤
        500 * t := by simpa [t] using htransitionBase
  have htail : affineVerifierTailRevSteps script.tailScript ≤
      5000 * u ^ 2 + 100 := by
    simpa [u] using affineVerifierTailRev_steps_le script.tailScript
  have hvsquare : v ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hv 2
  have husquare : u ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hu 2
  have hlinear : 500 * n ≤ 500 * n ^ 2 := by nlinarith
  simp only [affineVerifierBodyRevSteps]
  nlinarith

/-- The compiled fixed controller computes the reversed verifier-body stream
in polynomial time from the canonical structured operand encoding. -/
noncomputable def affineVerifierBodyRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineVerifierBodyScript id
      (fun script : AffineVerifierBodyScript =>
        (affineVerifierBodyGateStream script).reverse) where
  tm := compile affineVerifierBodyRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 10000 * Polynomial.X ^ 2 + 200
  outputsFun := fun script => by
    have builderRun := affineVerifierBody_run script []
    have compiledRun := compile_evalsToInTime
      affineVerifierBodyRevProgram builderRun
    rw [show affineVerifierBodyLoopCfg
        (encodeAffineVerifierBodyScript script) [] =
          initialCfg affineVerifierBodyRevProgram
            (encodeAffineVerifierBodyScript script) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineVerifierBodyRevProgram).step
        (_root_.Turing.initList (compile affineVerifierBodyRevProgram)
          (encodeAffineVerifierBodyScript script))
        (some (_root_.Turing.haltList
          (compile affineVerifierBodyRevProgram)
          (affineVerifierBodyGateStream script).reverse))
        (affineVerifierBodyRevSteps script) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime :
        affineVerifierBodyRevSteps script ≤
          (10000 * Polynomial.X ^ 2 + 200).eval
            (encodeAffineVerifierBodyScript script).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineVerifierBody_steps_le script
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineVerifierBodyRevProgram).step
        (_root_.Turing.initList (compile affineVerifierBodyRevProgram)
          (encodeAffineVerifierBodyScript script))
        (some (_root_.Turing.haltList
          (compile affineVerifierBodyRevProgram)
          (affineVerifierBodyGateStream script).reverse))
        ((10000 * Polynomial.X ^ 2 + 200).eval
          (encodeAffineVerifierBodyScript script).length) :=
      ⟨machineRun.toEvalsTo, le_trans machineRun.steps_le_m htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the preceding concrete output gives the forward semantic
verifier-body gate stream under a concrete polynomial-time TM2. -/
noncomputable def affineVerifierBodyGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineVerifierBodyScript id affineVerifierBodyGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineVerifierBodyRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
