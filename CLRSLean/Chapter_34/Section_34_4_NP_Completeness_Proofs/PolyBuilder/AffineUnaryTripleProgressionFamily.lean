import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Runtime families of affine unary triple progressions

The one-progression controller already preserves an arbitrary input tail and
exposes a clean redirectable finish label.  This module supplies the fixed
outer loop that repeatedly enters that controller.  All bases, strides, row
counts, and the number of progression descriptors remain runtime unary data.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Concatenated seven-field descriptors in row order. -/
def encodeAffineUnaryTripleProgressionFamily :
    List AffineUnaryTripleProgression → List UnaryFrameSym
  | [] => []
  | progression :: rest =>
      encodeAffineUnaryTripleProgression progression ++
        encodeAffineUnaryTripleProgressionFamily rest

/-- Concatenated semantic triple streams in the same row order. -/
def affineUnaryTripleProgressionFamilyFrameStream :
    List AffineUnaryTripleProgression → List UnaryFrameSym
  | [] => []
  | progression :: rest =>
      affineUnaryTripleProgressionFrameStream progression ++
        affineUnaryTripleProgressionFamilyFrameStream rest

/-- Finite phases of the nonempty-input check and relabeled progression body. -/
inductive AffineUnaryTripleProgressionFamilyLabel
  | check
  | save (symbol : UnaryFrameSym)
  | restore
  | clearBuffer
  | body (label : AffineUnaryTripleProgressionLabel)
  | finish
deriving DecidableEq, Fintype

private def progressionFamilyRelabelOp :
    Op UnaryFrameSym UnaryFrameSym AffineUnaryTripleProgressionLabel →
      Op UnaryFrameSym UnaryFrameSym
        AffineUnaryTripleProgressionFamilyLabel
  | .pushOutput symbol next => .pushOutput symbol (.body next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.body next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.body next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .inc₁ next => .inc₁ (.body next)
  | .inc₂ next => .inc₂ (.body next)
  | .inc₃ next => .inc₃ (.body next)
  | .dec₁ nextZero nextSucc => .dec₁ (.body nextZero) (.body nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.body nextZero) (.body nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.body nextZero) (.body nextSucc)
  | .jump next => .jump (.body next)
  | .halt => .halt

/-- One fixed program iterates the unchanged progression controller over an
arbitrary runtime descriptor stream. -/
def affineUnaryTripleProgressionFamilyRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineUnaryTripleProgressionFamilyLabel
  main := .check
  op
    | .check => .popInput .finish fun symbol => .save symbol
    | .save symbol => .pushWork₁ symbol .restore
    | .restore => .moveWork₁Input .finish (fun _ => .clearBuffer)
    | .clearBuffer => .popWork₁
        (.body affineUnaryTripleProgressionRevProgram.main)
        (fun _ => .finish)
    | .body .halt => .jump .check
    | .body label => progressionFamilyRelabelOp
        (affineUnaryTripleProgressionRevProgram.op label)
    | .finish => .halt

private def affineUnaryTripleProgressionFamilyCfg
    (label : AffineUnaryTripleProgressionFamilyLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineUnaryTripleProgressionFamilyRevProgram where
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

/-- Clean entry for a descriptor-family suffix. -/
def affineUnaryTripleProgressionFamilyLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineUnaryTripleProgressionFamilyRevProgram :=
  affineUnaryTripleProgressionFamilyCfg .check none none false
    input output [] [] [] [] []

/-- Clean pre-halt family exit. -/
def affineUnaryTripleProgressionFamilyFinishCfg
    (output : List UnaryFrameSym) :
    BuilderCfg affineUnaryTripleProgressionFamilyRevProgram :=
  affineUnaryTripleProgressionFamilyCfg .finish none none false
    [] output [] [] [] [] []

private def liftProgressionFamilyBodyCfg
    (c : BuilderCfg affineUnaryTripleProgressionRevProgram) :
    BuilderCfg affineUnaryTripleProgressionFamilyRevProgram where
  label := c.label.map .body
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

private theorem progressionFamilyRelabel_stepOp
    (op : Op UnaryFrameSym UnaryFrameSym
      AffineUnaryTripleProgressionLabel)
    (c : BuilderCfg affineUnaryTripleProgressionRevProgram) :
    stepOp (progressionFamilyRelabelOp op)
        (liftProgressionFamilyBodyCfg c) =
      liftProgressionFamilyBodyCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [progressionFamilyRelabelOp,
      liftProgressionFamilyBodyCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem progressionFamily_op_body
    (label : AffineUnaryTripleProgressionLabel)
    (hexit : label ≠ .halt) :
    affineUnaryTripleProgressionFamilyRevProgram.op (.body label) =
      progressionFamilyRelabelOp
        (affineUnaryTripleProgressionRevProgram.op label) := by
  cases label <;>
    simp_all [affineUnaryTripleProgressionFamilyRevProgram]

private theorem liftProgressionFamilyBody_step
    (c : BuilderCfg affineUnaryTripleProgressionRevProgram)
    (hexit : c.label ≠ some .halt) :
    step affineUnaryTripleProgressionFamilyRevProgram
        (liftProgressionFamilyBodyCfg c) =
      Option.map liftProgressionFamilyBodyCfg
        (step affineUnaryTripleProgressionRevProgram c) := by
  unfold step
  rw [show (liftProgressionFamilyBodyCfg c).label =
      c.label.map .body by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .halt := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [progressionFamily_op_body label hlabelExit]
      exact congrArg some
        (progressionFamilyRelabel_stepOp
          (affineUnaryTripleProgressionRevProgram.op label) c)

private theorem progressionFamily_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem progressionFamily_haltExit_no_return
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
      rw [hnone, progressionFamily_iterate_bind_none]
      simp

private theorem progressionFamily_lift_iterations_to_finish
    {a b : BuilderCfg affineUnaryTripleProgressionRevProgram}
    (hb : b.label = some .halt) : ∀ n : Nat,
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind
        (step affineUnaryTripleProgressionFamilyRevProgram))^[n]
          (some (liftProgressionFamilyBodyCfg a)) =
            some (liftProgressionFamilyBodyCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      subst a
      rfl
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind
        (step affineUnaryTripleProgressionRevProgram))^[n]
          (step affineUnaryTripleProgressionRevProgram a) = some b at h
      change (flip Option.bind
        (step affineUnaryTripleProgressionFamilyRevProgram))^[n]
          (step affineUnaryTripleProgressionFamilyRevProgram
            (liftProgressionFamilyBodyCfg a)) =
              some (liftProgressionFamilyBodyCfg b)
      have haexit : a.label ≠ some .halt := by
        intro ha
        exact progressionFamily_haltExit_no_return
          (.halt : AffineUnaryTripleProgressionLabel) rfl a b ha hb n h
      cases hsource : step affineUnaryTripleProgressionRevProgram a with
      | none =>
          rw [hsource, progressionFamily_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftProgressionFamilyBody_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def progressionFamily_dispatch_run
    (input output : List UnaryFrameSym) (hinput : input ≠ []) :
    EvalsToInTime (step affineUnaryTripleProgressionFamilyRevProgram)
      (affineUnaryTripleProgressionFamilyLoopCfg input output)
      (some (liftProgressionFamilyBodyCfg
        (affineUnaryTripleProgressionLoopCfg input output))) 4 := by
  cases input with
  | nil => contradiction
  | cons symbol rest => exact ⟨⟨4, rfl⟩, le_rfl⟩

private def progressionFamily_body_run
    (progression : AffineUnaryTripleProgression)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineUnaryTripleProgressionFamilyRevProgram)
      (liftProgressionFamilyBodyCfg
        (affineUnaryTripleProgressionLoopCfg
          (encodeAffineUnaryTripleProgression progression ++ tail) output))
      (some (liftProgressionFamilyBodyCfg
        (affineUnaryTripleProgressionFinishCfg tail
          ((affineUnaryTripleProgressionFrameStream progression).reverse ++
            output))))
      (affineUnaryTripleProgressionBodySteps progression) := by
  have sourceRun := affineUnaryTripleProgression_runToFinishWithTail
    progression tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact progressionFamily_lift_iterations_to_finish rfl
    sourceRun.steps sourceRun.evals_in_steps

/-- Exact runtime to the family pre-halt state. -/
def affineUnaryTripleProgressionFamilyStepsToFinish :
    List AffineUnaryTripleProgression → Nat
  | [] => 1
  | progression :: rest =>
      4 + affineUnaryTripleProgressionBodySteps progression + 1 +
        affineUnaryTripleProgressionFamilyStepsToFinish rest

/-- Exact continuous execution of a runtime descriptor family. -/
def affineUnaryTripleProgressionFamily_runToFinish
    (progressions : List AffineUnaryTripleProgression)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step affineUnaryTripleProgressionFamilyRevProgram)
      (affineUnaryTripleProgressionFamilyLoopCfg
        (encodeAffineUnaryTripleProgressionFamily progressions) output)
      (some (affineUnaryTripleProgressionFamilyFinishCfg
        ((affineUnaryTripleProgressionFamilyFrameStream progressions).reverse ++
          output)))
      (affineUnaryTripleProgressionFamilyStepsToFinish progressions) := by
  induction progressions generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons progression rest ih =>
      let restInput := encodeAffineUnaryTripleProgressionFamily rest
      let headOutput :=
        (affineUnaryTripleProgressionFrameStream progression).reverse ++ output
      let bodyStart := liftProgressionFamilyBodyCfg
        (affineUnaryTripleProgressionLoopCfg
          (encodeAffineUnaryTripleProgression progression ++ restInput) output)
      let bodyDone := liftProgressionFamilyBodyCfg
        (affineUnaryTripleProgressionFinishCfg restInput headOutput)
      let restStart := affineUnaryTripleProgressionFamilyLoopCfg
        restInput headOutput
      have hdescriptor :
          encodeAffineUnaryTripleProgression progression ++ restInput ≠ [] := by
        apply List.append_ne_nil_of_left_ne_nil
        exact List.ne_nil_of_length_pos (by
          simp [encodeAffineUnaryTripleProgression])
      have hdispatch : EvalsToInTime
          (step affineUnaryTripleProgressionFamilyRevProgram)
          (affineUnaryTripleProgressionFamilyLoopCfg
            (encodeAffineUnaryTripleProgression progression ++ restInput)
            output)
          (some bodyStart) 4 := by
        simpa [bodyStart] using progressionFamily_dispatch_run
          _ output hdescriptor
      have hbody : EvalsToInTime
          (step affineUnaryTripleProgressionFamilyRevProgram)
          bodyStart (some bodyDone)
          (affineUnaryTripleProgressionBodySteps progression) := by
        simpa [bodyStart, bodyDone, headOutput] using
          progressionFamily_body_run progression restInput output
      have hbridge : EvalsToInTime
          (step affineUnaryTripleProgressionFamilyRevProgram)
          bodyDone (some restStart) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hrest := ih headOutput
      let h₁ := EvalsToInTime.trans
        (step affineUnaryTripleProgressionFamilyRevProgram)
        4 _ _ bodyStart _ hdispatch hbody
      let h₂ := EvalsToInTime.trans
        (step affineUnaryTripleProgressionFamilyRevProgram)
        _ 1 _ bodyDone _ h₁ hbridge
      let full := EvalsToInTime.trans
        (step affineUnaryTripleProgressionFamilyRevProgram)
        _ _ _ restStart _ h₂ hrest
      convert full using 1
      · simp [encodeAffineUnaryTripleProgressionFamily, restInput]
      · simp [affineUnaryTripleProgressionFamilyFrameStream, headOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineUnaryTripleProgressionFamilyStepsToFinish]
        omega

/-- Every descriptor has seven nonempty field terminators. -/
theorem encodeAffineUnaryTripleProgression_length_pos
    (progression : AffineUnaryTripleProgression) :
    0 < (encodeAffineUnaryTripleProgression progression).length := by
  simp [encodeAffineUnaryTripleProgression]

/-- The continuous family run is cubic in the complete explicit descriptor
stream. -/
theorem affineUnaryTripleProgressionFamilyStepsToFinish_le
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFamilyStepsToFinish progressions ≤
      205 * (encodeAffineUnaryTripleProgressionFamily progressions).length ^ 3 +
        1 := by
  induction progressions with
  | nil => simp [affineUnaryTripleProgressionFamilyStepsToFinish,
      encodeAffineUnaryTripleProgressionFamily]
  | cons progression rest ih =>
      let headLength :=
        (encodeAffineUnaryTripleProgression progression).length
      let restLength :=
        (encodeAffineUnaryTripleProgressionFamily rest).length
      have hheadPos : 1 ≤ headLength := by
        have hpos := encodeAffineUnaryTripleProgression_length_pos progression
        change 1 ≤
          (encodeAffineUnaryTripleProgression progression).length
        omega
      have hbody := affineUnaryTripleProgressionBody_steps_le progression
      have hhead :
          4 + affineUnaryTripleProgressionBodySteps progression + 1 ≤
            205 * headLength ^ 3 := by
        have hcubePos : 0 < headLength ^ 3 :=
          pow_pos (by omega) _
        have hbody' :
            affineUnaryTripleProgressionBodySteps progression ≤
              100 * headLength ^ 3 + 100 := by
          simpa only [headLength] using hbody
        omega
      have hcross : headLength ^ 3 + restLength ^ 3 ≤
          (headLength + restLength) ^ 3 := by
        calc
          headLength ^ 3 + restLength ^ 3 ≤
              headLength ^ 3 + restLength ^ 3 +
                (3 * headLength ^ 2 * restLength +
                  3 * headLength * restLength ^ 2) :=
            Nat.le_add_right _ _
          _ = (headLength + restLength) ^ 3 := by ring
      calc
        affineUnaryTripleProgressionFamilyStepsToFinish
            (progression :: rest) =
            4 + affineUnaryTripleProgressionBodySteps progression + 1 +
              affineUnaryTripleProgressionFamilyStepsToFinish rest := by rfl
        _ ≤ 205 * headLength ^ 3 +
              (205 * restLength ^ 3 + 1) := Nat.add_le_add hhead (by
                simpa [restLength] using ih)
        _ = 205 * (headLength ^ 3 + restLength ^ 3) + 1 := by ring
        _ ≤ 205 * (headLength + restLength) ^ 3 + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 205 hcross) 1
        _ = 205 *
              (encodeAffineUnaryTripleProgressionFamily
                (progression :: rest)).length ^ 3 + 1 := by
            simp [headLength, restLength,
              encodeAffineUnaryTripleProgressionFamily]

/-- Standalone reverse-output family run, including the final halt step. -/
def affineUnaryTripleProgressionFamilyRev_run
    (progressions : List AffineUnaryTripleProgression) :
    EvalsToInTime (step affineUnaryTripleProgressionFamilyRevProgram)
      (initialCfg affineUnaryTripleProgressionFamilyRevProgram
        (encodeAffineUnaryTripleProgressionFamily progressions))
      (some (haltCfg affineUnaryTripleProgressionFamilyRevProgram
        (affineUnaryTripleProgressionFamilyFrameStream progressions).reverse))
      (affineUnaryTripleProgressionFamilyStepsToFinish progressions + 1) := by
  have body := affineUnaryTripleProgressionFamily_runToFinish progressions []
  have haltStep : EvalsToInTime
      (step affineUnaryTripleProgressionFamilyRevProgram)
      (affineUnaryTripleProgressionFamilyFinishCfg
        (affineUnaryTripleProgressionFamilyFrameStream progressions).reverse)
      (some (haltCfg affineUnaryTripleProgressionFamilyRevProgram
        (affineUnaryTripleProgressionFamilyFrameStream progressions).reverse))
      1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have body' : EvalsToInTime
      (step affineUnaryTripleProgressionFamilyRevProgram)
      (affineUnaryTripleProgressionFamilyLoopCfg
        (encodeAffineUnaryTripleProgressionFamily progressions) [])
      (some (affineUnaryTripleProgressionFamilyFinishCfg
        (affineUnaryTripleProgressionFamilyFrameStream progressions).reverse))
      (affineUnaryTripleProgressionFamilyStepsToFinish progressions) := by
    simpa using body
  let full := EvalsToInTime.trans
    (step affineUnaryTripleProgressionFamilyRevProgram)
    (affineUnaryTripleProgressionFamilyStepsToFinish progressions) 1 _ _ _
    body' haltStep
  convert full using 1
  · rfl
  · omega

/-- Compiled fixed TM2 for the reversed concatenated triple stream. -/
noncomputable def
    affineUnaryTripleProgressionFamilyRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgressionFamily id
      (fun progressions =>
        (affineUnaryTripleProgressionFamilyFrameStream progressions).reverse) where
  tm := compile affineUnaryTripleProgressionFamilyRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 205 * Polynomial.X ^ 3 + 2
  outputsFun := fun progressions => by
    have builderRun := affineUnaryTripleProgressionFamilyRev_run progressions
    have compiledRun := compile_evalsToInTime
      affineUnaryTripleProgressionFamilyRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineUnaryTripleProgressionFamilyRevProgram).step
        (_root_.Turing.initList
          (compile affineUnaryTripleProgressionFamilyRevProgram)
          (encodeAffineUnaryTripleProgressionFamily progressions))
        (some (_root_.Turing.haltList
          (compile affineUnaryTripleProgressionFamilyRevProgram)
          (affineUnaryTripleProgressionFamilyFrameStream progressions).reverse))
        (affineUnaryTripleProgressionFamilyStepsToFinish progressions + 1) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime :
        affineUnaryTripleProgressionFamilyStepsToFinish progressions + 1 ≤
          (205 * Polynomial.X ^ 3 + 2).eval
            (encodeAffineUnaryTripleProgressionFamily progressions).length := by
      have hbound :=
        affineUnaryTripleProgressionFamilyStepsToFinish_le progressions
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineUnaryTripleProgressionFamilyRevProgram).step
        (_root_.Turing.initList
          (compile affineUnaryTripleProgressionFamilyRevProgram)
          (encodeAffineUnaryTripleProgressionFamily progressions))
        (some (_root_.Turing.haltList
          (compile affineUnaryTripleProgressionFamilyRevProgram)
          (affineUnaryTripleProgressionFamilyFrameStream progressions).reverse))
        ((205 * Polynomial.X ^ 3 + 2).eval
          (encodeAffineUnaryTripleProgressionFamily progressions).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward row-major family stream. -/
noncomputable def
    affineUnaryTripleProgressionFamilyFrameStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgressionFamily id
      affineUnaryTripleProgressionFamilyFrameStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineUnaryTripleProgressionFamilyRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
