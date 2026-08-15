import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NotFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionalConjunctionFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin

/-!
# Continuous verifier-input shape controller

One fixed program executes the separator NOT family, the optional conjunction
family, and the final false-seeded disjunction without an intermediate halt.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

structure AffineInputShapeScript where
  separatorSources : List Nat
  armFrames : List (Option AffineConjunctionFrame)
  finalOrStart : Nat
  finalOrWires : List Nat

def affineInputShapeFinalOrFrames (script : AffineInputShapeScript) :
    List AffineOrFinPairFrame :=
  affineOrFinCanonicalFrames script.finalOrStart script.finalOrWires

/-- The first explicit boundary ends the NOT family; the optional arm encoder
already contains its own distinct final boundary. -/
def encodeAffineInputShapeScript (script : AffineInputShapeScript) :
    List UnaryFrameSym :=
  encodeAffineNotFamilySources script.separatorSources ++ [.frameEnd] ++
    encodeAffineOptionalConjunctionFamily script.armFrames ++
    encodeAffineOrFinFrames (affineInputShapeFinalOrFrames script)

def affineInputShapeGateStream (script : AffineInputShapeScript) :
    List CircuitSym :=
  affineNotFamilyGateStream script.separatorSources ++
    affineOptionalConjunctionFamilyGateStream script.armFrames ++
    affineOrFinGateStream (affineInputShapeFinalOrFrames script)

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

inductive AffineInputShapeLabel
  | notFamily (label : AffineNotFamilyLabel)
  | arms (label : AffineOptionalConjunctionFamilyLabel)
  | finalOr (label : AffineOrFinLabel)
  | finish | invalid
deriving DecidableEq, Fintype

def affineInputShapeRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineInputShapeLabel
  main := .notFamily .check
  op
    | .notFamily .finish =>
        .popWork₁ (.arms affineOptionalConjunctionFamilyRevProgram.main)
          (fun _ => .invalid)
    | .notFamily label => relabelOp .notFamily
        (affineNotFamilyRevProgram.op label)
    | .arms .finish =>
        .popWork₁ (.finalOr affineOrFinRevProgram.main) (fun _ => .invalid)
    | .arms label => relabelOp .arms
        (affineOptionalConjunctionFamilyRevProgram.op label)
    | .finalOr .finish => .jump .finish
    | .finalOr label => relabelOp .finalOr (affineOrFinRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

def affineInputShapeCfg (label : AffineInputShapeLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) : BuilderCfg affineInputShapeRevProgram where
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

def affineInputShapeLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineInputShapeRevProgram :=
  affineInputShapeCfg (.notFamily .check)
    none none false input output [] [] [] [] []

def affineInputShapeFinishCfg (output : List CircuitSym) :
    BuilderCfg affineInputShapeRevProgram :=
  affineInputShapeCfg .finish none none false [] output [] [] [] [] []

private def relabelCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineInputShapeLabel) (c : BuilderCfg P) :
    BuilderCfg affineInputShapeRevProgram where
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

private def liftNotCfg (c : BuilderCfg affineNotFamilyRevProgram) :
    BuilderCfg affineInputShapeRevProgram := relabelCfg .notFamily c

private def liftArmsCfg
    (c : BuilderCfg affineOptionalConjunctionFamilyRevProgram) :
    BuilderCfg affineInputShapeRevProgram := relabelCfg .arms c

private def liftOrCfg (c : BuilderCfg affineOrFinRevProgram) :
    BuilderCfg affineInputShapeRevProgram := relabelCfg .finalOr c

private theorem relabel_stepOp {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineInputShapeLabel)
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

private theorem outer_op_not (label : AffineNotFamilyLabel)
    (hexit : label ≠ .finish) :
    affineInputShapeRevProgram.op (.notFamily label) =
      relabelOp .notFamily (affineNotFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineInputShapeRevProgram] <;> rfl

private theorem outer_op_arms (label : AffineOptionalConjunctionFamilyLabel)
    (hexit : label ≠ .finish) :
    affineInputShapeRevProgram.op (.arms label) =
      relabelOp .arms
        (affineOptionalConjunctionFamilyRevProgram.op label) := by
  cases label <;> simp_all [affineInputShapeRevProgram] <;> rfl

private theorem outer_op_or (label : AffineOrFinLabel)
    (hexit : label ≠ .finish) :
    affineInputShapeRevProgram.op (.finalOr label) =
      relabelOp .finalOr (affineOrFinRevProgram.op label) := by
  cases label <;> simp_all [affineInputShapeRevProgram] <;> rfl

private theorem liftNot_step (c : BuilderCfg affineNotFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineInputShapeRevProgram (liftNotCfg c) =
      Option.map liftNotCfg (step affineNotFamilyRevProgram c) := by
  unfold step
  rw [show (liftNotCfg c).label = c.label.map .notFamily by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [outer_op_not label hlabelExit]
      exact congrArg some
        (relabel_stepOp .notFamily (affineNotFamilyRevProgram.op label) c)

private theorem liftArms_step
    (c : BuilderCfg affineOptionalConjunctionFamilyRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineInputShapeRevProgram (liftArmsCfg c) =
      Option.map liftArmsCfg
        (step affineOptionalConjunctionFamilyRevProgram c) := by
  unfold step
  rw [show (liftArmsCfg c).label = c.label.map .arms by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [outer_op_arms label hlabelExit]
      exact congrArg some (relabel_stepOp .arms
        (affineOptionalConjunctionFamilyRevProgram.op label) c)

private theorem liftOr_step (c : BuilderCfg affineOrFinRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineInputShapeRevProgram (liftOrCfg c) =
      Option.map liftOrCfg (step affineOrFinRevProgram c) := by
  unfold step
  rw [show (liftOrCfg c).label = c.label.map .finalOr by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [outer_op_or label hlabelExit]
      exact congrArg some
        (relabel_stepOp .finalOr (affineOrFinRevProgram.op label) c)

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
      rw [hnone, iterate_bind_none]
      simp

private theorem lift_iterations_to_haltExit
    {P : Program UnaryFrameSym CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg affineInputShapeRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineInputShapeRevProgram (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineInputShapeRevProgram))^[n]
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
      change (flip Option.bind (step affineInputShapeRevProgram))^[n]
        (step affineInputShapeRevProgram (tr a)) = some (tr b)
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

private def liftNot_run (sources : List Nat) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineInputShapeRevProgram)
      (liftNotCfg (affineNotFamilyLoopCfg
        (encodeAffineNotFamilySources sources ++ .frameEnd :: tail) output))
      (some (liftNotCfg (affineNotFamilyFinishInputCfg tail
        ((affineNotFamilyGateStream sources).reverse ++ output))))
      (affineNotFamilyUntilFinishSteps sources) := by
  have sourceRun := affineNotFamily_runToFinishWithTail sources tail output
  have htarget : (affineNotFamilyFinishInputCfg tail
      ((affineNotFamilyGateStream sources).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineNotFamilyLabel.finish rfl
    liftNotCfg liftNot_step htarget sourceRun.steps sourceRun.evals_in_steps

private def liftArms_run (frames : List (Option AffineConjunctionFrame))
    (tail : List UnaryFrameSym) (output : List CircuitSym) :
    EvalsToInTime (step affineInputShapeRevProgram)
      (liftArmsCfg (affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionFamily frames ++ tail) output))
      (some (liftArmsCfg
        (affineOptionalConjunctionFamilyFinishInputCfg tail
          ((affineOptionalConjunctionFamilyGateStream frames).reverse ++
            output))))
      (affineOptionalConjunctionFamilyUntilFinishSteps frames) := by
  have sourceRun := affineOptionalConjunctionFamily_runToFinishWithTail
    frames tail output
  have htarget : (affineOptionalConjunctionFamilyFinishInputCfg tail
      ((affineOptionalConjunctionFamilyGateStream frames).reverse ++
        output)).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit
    AffineOptionalConjunctionFamilyLabel.finish rfl
    liftArmsCfg liftArms_step htarget sourceRun.steps sourceRun.evals_in_steps

private def liftOr_run (frames : List AffineOrFinPairFrame)
    (output : List CircuitSym) :
    EvalsToInTime (step affineInputShapeRevProgram)
      (liftOrCfg (affineOrFinLoopCfg (encodeAffineOrFinFrames frames) output))
      (some (liftOrCfg (affineOrFinFinishCfg
        ((affineOrFinGateStream frames).reverse ++ output))))
      (affineOrFinUntilFinishSteps frames) := by
  have sourceRun := affineOrFin_runToFinish frames output
  have htarget : (affineOrFinFinishCfg
      ((affineOrFinGateStream frames).reverse ++ output)).label =
        some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact lift_iterations_to_haltExit AffineOrFinLabel.finish rfl
    liftOrCfg liftOr_step htarget sourceRun.steps sourceRun.evals_in_steps

def affineInputShapeRevSteps (script : AffineInputShapeScript) : Nat :=
  affineNotFamilyUntilFinishSteps script.separatorSources + 1 +
    affineOptionalConjunctionFamilyUntilFinishSteps script.armFrames + 1 +
    affineOrFinUntilFinishSteps (affineInputShapeFinalOrFrames script) + 2

/-- Exact continuous execution of all three input-shape phases. -/
def affineInputShape_run (script : AffineInputShapeScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineInputShapeRevProgram)
      (affineInputShapeLoopCfg (encodeAffineInputShapeScript script) output)
      (some (haltCfg affineInputShapeRevProgram
        ((affineInputShapeGateStream script).reverse ++ output)))
      (affineInputShapeRevSteps script) := by
  let orInput := encodeAffineOrFinFrames
    (affineInputShapeFinalOrFrames script)
  let armInput := encodeAffineOptionalConjunctionFamily script.armFrames
  let afterNot := (affineNotFamilyGateStream script.separatorSources).reverse ++
    output
  let afterArms :=
    (affineOptionalConjunctionFamilyGateStream script.armFrames).reverse ++
      afterNot
  let afterOr :=
    (affineOrFinGateStream (affineInputShapeFinalOrFrames script)).reverse ++
      afterArms
  let notDone := liftNotCfg (affineNotFamilyFinishInputCfg
    (armInput ++ orInput) afterNot)
  let armsStart := liftArmsCfg (affineOptionalConjunctionFamilyLoopCfg
    (armInput ++ orInput) afterNot)
  let armsDone := liftArmsCfg
    (affineOptionalConjunctionFamilyFinishInputCfg orInput afterArms)
  let orStart := liftOrCfg
    (affineOrFinLoopCfg orInput afterArms)
  let orDone := liftOrCfg (affineOrFinFinishCfg afterOr)
  have hnot : EvalsToInTime (step affineInputShapeRevProgram)
      (affineInputShapeLoopCfg (encodeAffineInputShapeScript script) output)
      (some notDone)
      (affineNotFamilyUntilFinishSteps script.separatorSources) := by
    simpa [affineInputShapeLoopCfg, encodeAffineInputShapeScript,
      notDone, armInput, orInput, afterNot, liftNotCfg, relabelCfg,
      affineNotFamilyLoopCfg, affineNotFamilyCfg, affineInputShapeCfg,
      List.append_assoc] using
      liftNot_run script.separatorSources (armInput ++ orInput) output
  have htoArms : EvalsToInTime (step affineInputShapeRevProgram)
      notDone (some armsStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have harms : EvalsToInTime (step affineInputShapeRevProgram)
      armsStart (some armsDone)
      (affineOptionalConjunctionFamilyUntilFinishSteps script.armFrames) := by
    simpa [armsStart, armsDone, armInput, orInput, afterNot, afterArms] using
      liftArms_run script.armFrames orInput afterNot
  have htoOr : EvalsToInTime (step affineInputShapeRevProgram)
      armsDone (some orStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hor : EvalsToInTime (step affineInputShapeRevProgram)
      orStart (some orDone)
      (affineOrFinUntilFinishSteps
        (affineInputShapeFinalOrFrames script)) := by
    simpa [orStart, orDone, orInput, afterArms, afterOr] using
      liftOr_run (affineInputShapeFinalOrFrames script) afterArms
  have hfinish : EvalsToInTime (step affineInputShapeRevProgram)
      orDone (some (affineInputShapeFinishCfg afterOr)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hhalt : EvalsToInTime (step affineInputShapeRevProgram)
      (affineInputShapeFinishCfg afterOr)
      (some (haltCfg affineInputShapeRevProgram afterOr)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step affineInputShapeRevProgram) _ 1 _
    notDone _ hnot htoArms
  let t₂ := EvalsToInTime.trans (step affineInputShapeRevProgram) _ _ _
    armsStart _ t₁ harms
  let t₃ := EvalsToInTime.trans (step affineInputShapeRevProgram) _ 1 _
    armsDone _ t₂ htoOr
  let t₄ := EvalsToInTime.trans (step affineInputShapeRevProgram) _ _ _
    orStart _ t₃ hor
  let t₅ := EvalsToInTime.trans (step affineInputShapeRevProgram) _ 1 _
    orDone _ t₄ hfinish
  let full := EvalsToInTime.trans (step affineInputShapeRevProgram) _ 1 _
    (affineInputShapeFinishCfg afterOr) _ t₅ hhalt
  convert full using 1
  · simp [affineInputShapeGateStream, afterOr, afterArms, afterNot,
      List.reverse_append, List.append_assoc]
  · simp [affineInputShapeRevSteps]
    omega

/-- Coarse uniform polynomial envelope for the continuous controller. -/
theorem affineInputShapeRev_steps_le (script : AffineInputShapeScript) :
    affineInputShapeRevSteps script ≤
      1200 * (encodeAffineInputShapeScript script).length ^ 2 + 20 := by
  let a := (encodeAffineNotFamilySources script.separatorSources).length
  let b := (encodeAffineOptionalConjunctionFamily script.armFrames).length
  let c := (encodeAffineOrFinFrames
    (affineInputShapeFinalOrFrames script)).length
  let n := (encodeAffineInputShapeScript script).length
  have hn : n = a + 1 + b + c := by
    simp [n, a, b, c, encodeAffineInputShapeScript]
    omega
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  have hc : c ≤ n := by omega
  have hnpos : 1 ≤ n := by omega
  have hnotBase := affineNotFamilyRev_steps_le script.separatorSources
  have hnot : affineNotFamilyUntilFinishSteps script.separatorSources ≤
      20 * a + 2 := by
    calc
      affineNotFamilyUntilFinishSteps script.separatorSources ≤
          affineNotFamilyRevSteps script.separatorSources := by
            simp [affineNotFamilyRevSteps]
      _ ≤ 20 * a + 2 := by simpa [a] using hnotBase
  have harmsBase := affineOptionalConjunctionFamilyRev_steps_le
    script.armFrames
  have harms :
      affineOptionalConjunctionFamilyUntilFinishSteps script.armFrames ≤
        1005 * b ^ 2 + 2 := by
    calc
      affineOptionalConjunctionFamilyUntilFinishSteps script.armFrames ≤
          affineOptionalConjunctionFamilyRevSteps script.armFrames := by
            simp [affineOptionalConjunctionFamilyRevSteps]
      _ ≤ 1005 * b ^ 2 + 2 := by simpa [b] using harmsBase
  have horBase := affineOrFinRev_steps_le
    (affineInputShapeFinalOrFrames script)
  have hor : affineOrFinUntilFinishSteps
      (affineInputShapeFinalOrFrames script) ≤ 100 * c + 3 := by
    calc
      affineOrFinUntilFinishSteps (affineInputShapeFinalOrFrames script) ≤
          affineOrFinRevSteps (affineInputShapeFinalOrFrames script) := by
            simp [affineOrFinRevSteps]
      _ ≤ 100 * c + 3 := by simpa [c] using horBase
  have hbsquare : b ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hb 2
  have hlinear : 120 * n ≤ 120 * n ^ 2 := by nlinarith
  simp only [affineInputShapeRevSteps]
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
