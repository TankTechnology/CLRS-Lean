import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Family wrapper for the compact validity-tail source

The established compact validity-tail source handles one row and exposes a
clean redirectable finish configuration.  This module supplies the reusable
finite-control wrapper that restarts that source until the input is empty.
No row data or runtime dimension is stored in finite control.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private noncomputable instance validityTailSourceLabelDecidableEq
    (blankSteps : List Nat) :
    DecidableEq (affineValidityTailSourceRevProgram blankSteps).Label :=
  (affineValidityTailSourceRevProgram blankSteps).labelDecidableEq

private noncomputable instance validityTailSourceLabelFintype
    (blankSteps : List Nat) :
    Fintype (affineValidityTailSourceRevProgram blankSteps).Label :=
  (affineValidityTailSourceRevProgram blankSteps).labelFintype

/-- Concatenated compact invocations in row order. -/
def encodeAffineValidityTailSourceInvocationFamily :
    List AffineValidityTailSourceFrame → List UnaryFrameSym
  | [] => []
  | frame :: rest =>
      encodeAffineValidityTailSourceInvocation frame ++
        encodeAffineValidityTailSourceInvocationFamily rest

/-- Concatenated semantic tail-frame encodings in the same row order. -/
def affineValidityTailSourceFamilyStream (blankSteps : List Nat) :
    List AffineValidityTailSourceFrame → List UnaryFrameSym
  | [] => []
  | frame :: rest =>
      encodeAffineValidityTailFrame
          (affineValidityTailSourceFrame blankSteps frame) ++
        affineValidityTailSourceFamilyStream blankSteps rest

/-- Outer dispatch and the relabeled one-row source. -/
inductive AffineValidityTailSourceFamilyLabel (blankSteps : List Nat)
  | check
  | save (symbol : UnaryFrameSym)
  | restore
  | clearBuffer
  | body (label : (affineValidityTailSourceRevProgram blankSteps).Label)
  | finish
deriving DecidableEq, Fintype

private def validityTailSourceFamilyRelabelOp
    {blankSteps : List Nat} :
    Op UnaryFrameSym UnaryFrameSym
        (affineValidityTailSourceRevProgram blankSteps).Label →
      Op UnaryFrameSym UnaryFrameSym
        (AffineValidityTailSourceFamilyLabel blankSteps)
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

/-- Fixed family controller.  Empty input is the family terminator; a
nonempty input is restored before entering the unchanged one-row source. -/
def affineValidityTailSourceFamilyRevProgram (blankSteps : List Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineValidityTailSourceFamilyLabel blankSteps
  main := .check
  op
    | .check => .popInput .finish fun symbol => .save symbol
    | .save symbol => .pushWork₁ symbol .restore
    | .restore => .moveWork₁Input .finish (fun _ => .clearBuffer)
    | .clearBuffer => .popWork₁
        (.body (affineValidityTailSourceRevProgram blankSteps).main)
        (fun _ => .finish)
    | .body (.inr .finish) => .popWork₁ .check (fun _ => .check)
    | .body label => validityTailSourceFamilyRelabelOp
        ((affineValidityTailSourceRevProgram blankSteps).op label)
    | .finish => .halt

private def affineValidityTailSourceFamilyCfg {blankSteps : List Nat}
    (label : AffineValidityTailSourceFamilyLabel blankSteps)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineValidityTailSourceFamilyRevProgram blankSteps) where
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

/-- Clean entry for a family suffix. -/
def affineValidityTailSourceFamilyLoopCfg (blankSteps : List Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineValidityTailSourceFamilyRevProgram blankSteps) :=
  affineValidityTailSourceFamilyCfg .check none none false
    input output [] [] [] [] []

/-- Clean pre-halt family exit. -/
def affineValidityTailSourceFamilyFinishCfg (blankSteps : List Nat)
    (output : List UnaryFrameSym) :
    BuilderCfg (affineValidityTailSourceFamilyRevProgram blankSteps) :=
  affineValidityTailSourceFamilyCfg .finish none none false
    [] output [] [] [] [] []

private def liftValidityTailSourceFamilyBodyCfg {blankSteps : List Nat}
    (c : BuilderCfg (affineValidityTailSourceRevProgram blankSteps)) :
    BuilderCfg (affineValidityTailSourceFamilyRevProgram blankSteps) where
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

private theorem validityTailSourceFamilyRelabel_stepOp
    {blankSteps : List Nat}
    (op : Op UnaryFrameSym UnaryFrameSym
      (affineValidityTailSourceRevProgram blankSteps).Label)
    (c : BuilderCfg (affineValidityTailSourceRevProgram blankSteps)) :
    stepOp (validityTailSourceFamilyRelabelOp op)
        (liftValidityTailSourceFamilyBodyCfg c) =
      liftValidityTailSourceFamilyBodyCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [validityTailSourceFamilyRelabelOp,
      liftValidityTailSourceFamilyBodyCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private def affineValidityTailSourceExitLabel (blankSteps : List Nat) :
    (affineValidityTailSourceRevProgram blankSteps).Label :=
  .inr (.finish : AffineValidityFinalConjunctionSourceLabel blankSteps.length)

private theorem affineValidityTailSourceFamily_op_body
    (blankSteps : List Nat)
    (label : (affineValidityTailSourceRevProgram blankSteps).Label)
    (hexit : label ≠ affineValidityTailSourceExitLabel blankSteps) :
    (affineValidityTailSourceFamilyRevProgram blankSteps).op (.body label) =
      validityTailSourceFamilyRelabelOp
        ((affineValidityTailSourceRevProgram blankSteps).op label) := by
  rcases label with label | label
  · rfl
  · cases label <;>
      simp_all [affineValidityTailSourceFamilyRevProgram,
        affineValidityTailSourceExitLabel]

private theorem liftValidityTailSourceFamilyBody_step
    {blankSteps : List Nat}
    (c : BuilderCfg (affineValidityTailSourceRevProgram blankSteps))
    (hexit : c.label ≠ some (affineValidityTailSourceExitLabel blankSteps)) :
    step (affineValidityTailSourceFamilyRevProgram blankSteps)
        (liftValidityTailSourceFamilyBodyCfg c) =
      Option.map liftValidityTailSourceFamilyBodyCfg
        (step (affineValidityTailSourceRevProgram blankSteps) c) := by
  unfold step
  rw [show (liftValidityTailSourceFamilyBodyCfg c).label =
      c.label.map .body by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit :
          label ≠ affineValidityTailSourceExitLabel blankSteps := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineValidityTailSourceFamily_op_body blankSteps label hlabelExit]
      exact congrArg some
        (validityTailSourceFamilyRelabel_stepOp
          ((affineValidityTailSourceRevProgram blankSteps).op label) c)

private theorem validityTailSourceFamily_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem validityTailSourceFamily_haltExit_no_return
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
      rw [hnone, validityTailSourceFamily_iterate_bind_none]
      simp

private theorem validityTailSourceFamily_lift_iterations_to_finish
    {blankSteps : List Nat}
    {a b : BuilderCfg (affineValidityTailSourceRevProgram blankSteps)}
    (hb : b.label = some (affineValidityTailSourceExitLabel blankSteps)) :
    ∀ n : Nat,
    (flip Option.bind
      (step (affineValidityTailSourceRevProgram blankSteps)))^[n]
        (some a) = some b →
      (flip Option.bind
        (step (affineValidityTailSourceFamilyRevProgram blankSteps)))^[n]
          (some (liftValidityTailSourceFamilyBodyCfg a)) =
            some (liftValidityTailSourceFamilyBodyCfg b) := by
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
        (step (affineValidityTailSourceRevProgram blankSteps)))^[n]
          (step (affineValidityTailSourceRevProgram blankSteps) a) = some b at h
      change (flip Option.bind
        (step (affineValidityTailSourceFamilyRevProgram blankSteps)))^[n]
          (step (affineValidityTailSourceFamilyRevProgram blankSteps)
            (liftValidityTailSourceFamilyBodyCfg a)) =
              some (liftValidityTailSourceFamilyBodyCfg b)
      have haexit :
          a.label ≠ some (affineValidityTailSourceExitLabel blankSteps) := by
        intro ha
        exact validityTailSourceFamily_haltExit_no_return
          (affineValidityTailSourceExitLabel blankSteps) rfl a b ha hb n h
      cases hsource : step (affineValidityTailSourceRevProgram blankSteps) a with
      | none =>
          rw [hsource, validityTailSourceFamily_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftValidityTailSourceFamilyBody_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def validityTailSourceFamily_dispatch_run
    (blankSteps : List Nat) (input output : List UnaryFrameSym)
    (hinput : input ≠ []) :
    EvalsToInTime (step (affineValidityTailSourceFamilyRevProgram blankSteps))
      (affineValidityTailSourceFamilyLoopCfg blankSteps input output)
      (some (liftValidityTailSourceFamilyBodyCfg
        (affineValidityTailSourceLoopCfg blankSteps input output))) 4 := by
  cases input with
  | nil => contradiction
  | cons symbol rest => exact ⟨⟨4, rfl⟩, le_rfl⟩

private def validityTailSourceFamily_body_run
    (blankSteps : List Nat) (frame : AffineValidityTailSourceFrame)
    (tail output : List UnaryFrameSym)
    (hlength : frame.stackSeeds.length = blankSteps.length) :
    EvalsToInTime (step (affineValidityTailSourceFamilyRevProgram blankSteps))
      (liftValidityTailSourceFamilyBodyCfg
        (affineValidityTailSourceLoopCfg blankSteps
          (encodeAffineValidityTailSourceInvocation frame ++ tail) output))
      (some (liftValidityTailSourceFamilyBodyCfg
        (affineValidityTailSourceFinishCfg blankSteps tail
          ((encodeAffineValidityTailFrame
            (affineValidityTailSourceFrame blankSteps frame)).reverse ++
              output))))
      (affineValidityTailSourceSteps blankSteps frame) := by
  have sourceRun := affineValidityTailSource_runToFinish
    blankSteps frame tail output hlength
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact validityTailSourceFamily_lift_iterations_to_finish rfl
    sourceRun.steps sourceRun.evals_in_steps

/-- Exact runtime to the family pre-halt state. -/
def affineValidityTailSourceFamilyStepsToFinish (blankSteps : List Nat) :
    List AffineValidityTailSourceFrame → Nat
  | [] => 1
  | frame :: rest =>
      4 + affineValidityTailSourceSteps blankSteps frame + 1 +
        affineValidityTailSourceFamilyStepsToFinish blankSteps rest

/-- Exact family run, preserving row order after reversing the accumulated
prepend-order output. -/
def affineValidityTailSourceFamily_runToFinish
    (blankSteps : List Nat) (frames : List AffineValidityTailSourceFrame)
    (output : List UnaryFrameSym)
    (hlength : ∀ frame ∈ frames,
      frame.stackSeeds.length = blankSteps.length) :
    EvalsToInTime (step (affineValidityTailSourceFamilyRevProgram blankSteps))
      (affineValidityTailSourceFamilyLoopCfg blankSteps
        (encodeAffineValidityTailSourceInvocationFamily frames) output)
      (some (affineValidityTailSourceFamilyFinishCfg blankSteps
        ((affineValidityTailSourceFamilyStream blankSteps frames).reverse ++
          output)))
      (affineValidityTailSourceFamilyStepsToFinish blankSteps frames) := by
  induction frames generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest ih =>
      let restInput := encodeAffineValidityTailSourceInvocationFamily rest
      let headOutput :=
        (encodeAffineValidityTailFrame
          (affineValidityTailSourceFrame blankSteps frame)).reverse ++ output
      let bodyStart := liftValidityTailSourceFamilyBodyCfg
        (affineValidityTailSourceLoopCfg blankSteps
          (encodeAffineValidityTailSourceInvocation frame ++ restInput) output)
      let bodyDone := liftValidityTailSourceFamilyBodyCfg
        (affineValidityTailSourceFinishCfg blankSteps restInput headOutput)
      let restStart := affineValidityTailSourceFamilyLoopCfg
        blankSteps restInput headOutput
      have hinvocation :
          encodeAffineValidityTailSourceInvocation frame ++ restInput ≠ [] := by
        simp [encodeAffineValidityTailSourceInvocation,
          encodeAffineValidityFinalConjunctionSourceInvocation,
          encodeUnaryFrameBlock]
      have hdispatch : EvalsToInTime
          (step (affineValidityTailSourceFamilyRevProgram blankSteps))
          (affineValidityTailSourceFamilyLoopCfg blankSteps
            (encodeAffineValidityTailSourceInvocation frame ++ restInput)
            output)
          (some bodyStart) 4 := by
        simpa [bodyStart] using validityTailSourceFamily_dispatch_run
          blankSteps _ output hinvocation
      have hbody : EvalsToInTime
          (step (affineValidityTailSourceFamilyRevProgram blankSteps))
          bodyStart (some bodyDone)
          (affineValidityTailSourceSteps blankSteps frame) := by
        simpa [bodyStart, bodyDone, headOutput] using
          validityTailSourceFamily_body_run blankSteps frame restInput output
            (hlength frame (by simp))
      have hbridge : EvalsToInTime
          (step (affineValidityTailSourceFamilyRevProgram blankSteps))
          bodyDone (some restStart) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step (affineValidityTailSourceFamilyRevProgram blankSteps)
          bodyDone = some restStart
        change step (affineValidityTailSourceFamilyRevProgram blankSteps)
          (affineValidityTailSourceFamilyCfg
            (.body (.inr (.finish :
              AffineValidityFinalConjunctionSourceLabel blankSteps.length)))
            (some .frameEnd) none false restInput headOutput [] [] [] [] []) =
          some (affineValidityTailSourceFamilyLoopCfg
            blankSteps restInput headOutput)
        rfl
      have hrest := ih headOutput
        (fun tail htail => hlength tail (by simp [htail]))
      let h₁ := EvalsToInTime.trans
        (step (affineValidityTailSourceFamilyRevProgram blankSteps))
        4 _ _ bodyStart _ hdispatch hbody
      let h₂ := EvalsToInTime.trans
        (step (affineValidityTailSourceFamilyRevProgram blankSteps))
        _ 1 _ bodyDone _ h₁ hbridge
      let full := EvalsToInTime.trans
        (step (affineValidityTailSourceFamilyRevProgram blankSteps))
        _ _ _ restStart _ h₂ hrest
      convert full using 1
      · simp [encodeAffineValidityTailSourceInvocationFamily, restInput]
      · simp [affineValidityTailSourceFamilyStream, headOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineValidityTailSourceFamilyStepsToFinish]
        omega

/-- Each compact invocation is nonempty. -/
theorem encodeAffineValidityTailSourceInvocation_length_pos
    (frame : AffineValidityTailSourceFrame) :
    0 < (encodeAffineValidityTailSourceInvocation frame).length := by
  simp [encodeAffineValidityTailSourceInvocation,
    encodeAffineValidityFinalConjunctionSourceInvocation,
    encodeUnaryFrameBlock]

/-- Fixed coefficient for the family wrapper's quadratic bound. -/
def affineValidityTailSourceFamilyStepCoeff (blankSteps : List Nat) : Nat :=
  4 * affineValidityTailSourceStepCoeff blankSteps + 5

/-- The complete family run to pre-halt is quadratic in the concatenated
compact invocation length. -/
theorem affineValidityTailSourceFamilyStepsToFinish_le
    (blankSteps : List Nat) (frames : List AffineValidityTailSourceFrame)
    (hlength : ∀ frame ∈ frames,
      frame.stackSeeds.length = blankSteps.length) :
    affineValidityTailSourceFamilyStepsToFinish blankSteps frames ≤
      affineValidityTailSourceFamilyStepCoeff blankSteps *
        (encodeAffineValidityTailSourceInvocationFamily frames).length ^ 2 +
          1 := by
  induction frames with
  | nil => simp [affineValidityTailSourceFamilyStepsToFinish,
      encodeAffineValidityTailSourceInvocationFamily]
  | cons frame rest ih =>
      let headLength :=
        (encodeAffineValidityTailSourceInvocation frame).length
      let restLength :=
        (encodeAffineValidityTailSourceInvocationFamily rest).length
      let coeff := affineValidityTailSourceStepCoeff blankSteps
      let familyCoeff := affineValidityTailSourceFamilyStepCoeff blankSteps
      have hheadPos : 1 ≤ headLength := by
        have hpos := encodeAffineValidityTailSourceInvocation_length_pos frame
        simp only [headLength] at hpos ⊢
        omega
      have hhead := affineValidityTailSource_steps_le blankSteps frame
        (hlength frame (by simp))
      have hheadSquare : (headLength + 1) ^ 2 ≤ 4 * headLength ^ 2 := by
        nlinarith
      have hheadBound :
          affineValidityTailSourceSteps blankSteps frame ≤
            4 * coeff * headLength ^ 2 := by
        calc
          affineValidityTailSourceSteps blankSteps frame ≤
              coeff * (headLength + 1) ^ 2 := by
            simpa [coeff, headLength] using hhead
          _ ≤ coeff * (4 * headLength ^ 2) :=
            Nat.mul_le_mul_left coeff hheadSquare
          _ = 4 * coeff * headLength ^ 2 := by ring
      have hrest := ih (fun tail htail => hlength tail (by simp [htail]))
      have hrestBound :
          affineValidityTailSourceFamilyStepsToFinish blankSteps rest ≤
            familyCoeff * restLength ^ 2 + 1 := by
        simpa [familyCoeff, restLength] using hrest
      have hcross : headLength ^ 2 + restLength ^ 2 ≤
          (headLength + restLength) ^ 2 := by
        nlinarith [Nat.zero_le (2 * headLength * restLength)]
      calc
        affineValidityTailSourceFamilyStepsToFinish blankSteps
            (frame :: rest) =
            4 + affineValidityTailSourceSteps blankSteps frame + 1 +
              affineValidityTailSourceFamilyStepsToFinish blankSteps rest := by
                rfl
        _ ≤ 5 + 4 * coeff * headLength ^ 2 +
              (familyCoeff * restLength ^ 2 + 1) := by
            omega
        _ ≤ familyCoeff * headLength ^ 2 +
              familyCoeff * restLength ^ 2 + 1 := by
            simp [familyCoeff,
              affineValidityTailSourceFamilyStepCoeff]
            nlinarith
        _ = familyCoeff * (headLength ^ 2 + restLength ^ 2) + 1 := by
            ring
        _ ≤ familyCoeff * (headLength + restLength) ^ 2 + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left familyCoeff hcross) 1
        _ = affineValidityTailSourceFamilyStepCoeff blankSteps *
              (encodeAffineValidityTailSourceInvocationFamily
                (frame :: rest)).length ^ 2 + 1 := by
            simp [familyCoeff, headLength, restLength,
              encodeAffineValidityTailSourceInvocationFamily]

/-- Well-formed typed family used by the total compiled machine. -/
structure AffineValidityTailSourceFamily (blankSteps : List Nat) where
  frames : List AffineValidityTailSourceFrame
  stack_lengths : ∀ frame ∈ frames,
    frame.stackSeeds.length = blankSteps.length

/-- Concrete encoding of a well-formed compact family. -/
def encodeAffineValidityTailSourceFamily {blankSteps : List Nat}
    (family : AffineValidityTailSourceFamily blankSteps) :
    List UnaryFrameSym :=
  encodeAffineValidityTailSourceInvocationFamily family.frames

/-- The family controller computes the reversed semantic tail stream in
quadratic time. -/
noncomputable def affineValidityTailSourceFamilyRev_computableInPolyTime
    (blankSteps : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineValidityTailSourceFamily id
      (fun family : AffineValidityTailSourceFamily blankSteps =>
        (affineValidityTailSourceFamilyStream
          blankSteps family.frames).reverse) where
  tm := compile (affineValidityTailSourceFamilyRevProgram blankSteps)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C
      (affineValidityTailSourceFamilyStepCoeff blankSteps) *
    Polynomial.X ^ 2 + 2
  outputsFun := fun family => by
    have finishRun := affineValidityTailSourceFamily_runToFinish
      blankSteps family.frames [] family.stack_lengths
    have haltStep : EvalsToInTime
        (step (affineValidityTailSourceFamilyRevProgram blankSteps))
        (affineValidityTailSourceFamilyFinishCfg blankSteps
          (affineValidityTailSourceFamilyStream
            blankSteps family.frames).reverse)
        (some (haltCfg (affineValidityTailSourceFamilyRevProgram blankSteps)
          (affineValidityTailSourceFamilyStream
            blankSteps family.frames).reverse)) 1 :=
      ⟨⟨1, rfl⟩, le_rfl⟩
    have builderRun := EvalsToInTime.trans
      (step (affineValidityTailSourceFamilyRevProgram blankSteps))
      _ 1 _ _ _ (by simpa using finishRun) haltStep
    have compiledRun := compile_evalsToInTime
      (affineValidityTailSourceFamilyRevProgram blankSteps) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile (affineValidityTailSourceFamilyRevProgram blankSteps)).step
        (_root_.Turing.initList
          (compile (affineValidityTailSourceFamilyRevProgram blankSteps))
          (encodeAffineValidityTailSourceInvocationFamily family.frames))
        (some (_root_.Turing.haltList
          (compile (affineValidityTailSourceFamilyRevProgram blankSteps))
          (affineValidityTailSourceFamilyStream
            blankSteps family.frames).reverse))
        (affineValidityTailSourceFamilyStepsToFinish
          blankSteps family.frames + 1) := by
      have hinitial :
          affineValidityTailSourceFamilyLoopCfg blankSteps
              (encodeAffineValidityTailSourceInvocationFamily family.frames)
              [] =
            initialCfg (affineValidityTailSourceFamilyRevProgram blankSteps)
              (encodeAffineValidityTailSourceInvocationFamily family.frames) :=
        rfl
      rw [hinitial] at compiledRun
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        Nat.add_comm] using
        compiledRun
    have htime :
        affineValidityTailSourceFamilyStepsToFinish
              blankSteps family.frames + 1 ≤
          (Polynomial.C
              (affineValidityTailSourceFamilyStepCoeff blankSteps) *
            Polynomial.X ^ 2 + 2).eval
              (encodeAffineValidityTailSourceInvocationFamily
                family.frames).length := by
      have hbound := affineValidityTailSourceFamilyStepsToFinish_le
        blankSteps family.frames family.stack_lengths
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_ofNat]
      omega
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile (affineValidityTailSourceFamilyRevProgram blankSteps)).step
        (_root_.Turing.initList
          (compile (affineValidityTailSourceFamilyRevProgram blankSteps))
          (encodeAffineValidityTailSourceInvocationFamily family.frames))
        (some (_root_.Turing.haltList
          (compile (affineValidityTailSourceFamilyRevProgram blankSteps))
          (affineValidityTailSourceFamilyStream
            blankSteps family.frames).reverse))
        ((Polynomial.C
              (affineValidityTailSourceFamilyStepCoeff blankSteps) *
            Polynomial.X ^ 2 + 2).eval
              (encodeAffineValidityTailSourceInvocationFamily
                family.frames).length) := by
      exact ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [encodeAffineValidityTailSourceFamily,
      _root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward semantic tail-family source. -/
noncomputable def affineValidityTailSourceFamily_computableInPolyTime
    (blankSteps : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineValidityTailSourceFamily id
      (fun family : AffineValidityTailSourceFamily blankSteps =>
        affineValidityTailSourceFamilyStream blankSteps family.frames) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineValidityTailSourceFamilyRev_computableInPolyTime blankSteps)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
