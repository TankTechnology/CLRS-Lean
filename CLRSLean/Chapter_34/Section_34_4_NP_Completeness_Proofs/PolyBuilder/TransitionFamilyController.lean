import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-!
# Runtime-length family of Cook--Levin local-transition scripts

One fixed outer controller repeatedly enters the verified local-transition
controller.  The family length and every gate operand remain runtime unary
data; the finite control contains no tableau dimension or generated gate.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Pure-unary payload of one local transition, including the terminator
consumed by `affineTransition_runToFinishWithTail`. -/
def encodeAffineTransitionLocalUnary (script : AffineTransitionScript) :
    List UnaryFrameSym :=
  encodeAffineStmtControllerScript script.dispatch ++
    affineStmtTransitionBoundaryCode ++
    encodeAffineTransitionTail script ++ [.frameEnd]

theorem encodeAffineTransitionScriptWithTail_eq_map
    (script : AffineTransitionScript) (tail : List UnaryFrameSym) :
    encodeAffineTransitionScriptWithTail script tail =
      (encodeAffineTransitionLocalUnary script ++ tail).map .data := by
  simp [encodeAffineTransitionScriptWithTail,
    encodeAffineTransitionLocalUnary, encodeAffineStmtTransitionInput,
    encodeAffineTransitionTail, List.map_append, List.append_assoc]

/-- Unary family protocol. A leading `frameEnd` announces each local script;
the local payload contains its own trailing `frameEnd` terminator. -/
def encodeAffineTransitionFamilyUnary :
    List AffineTransitionScript → List UnaryFrameSym
  | [] => []
  | script :: rest =>
      .frameEnd ::
        (encodeAffineTransitionLocalUnary script ++
          encodeAffineTransitionFamilyUnary rest)

def encodeAffineTransitionFamily (scripts : List AffineTransitionScript) :
    List AffineStmtScriptSym :=
  (encodeAffineTransitionFamilyUnary scripts).map .data

def affineTransitionFamilyGateStream
    (scripts : List AffineTransitionScript) : List CircuitSym :=
  scripts.flatMap affineTransitionGateStream

inductive AffineTransitionFamilyLabel
  | check
  | clearStart
  | local (label : AffineTransitionControllerLabel)
  | finish
  | invalid
deriving DecidableEq, Fintype

def affineTransitionFamilyCheckTarget :
    AffineStmtScriptSym → AffineTransitionFamilyLabel
  | .data .frameEnd => .clearStart
  | _ => .invalid

/-- Fixed controller for an arbitrary runtime-length transition family. -/
def affineTransitionFamilyRevProgram :
    Program AffineStmtScriptSym CircuitSym where
  Label := AffineTransitionFamilyLabel
  main := .check
  op
    | .check => .popInput .finish affineTransitionFamilyCheckTarget
    | .clearStart =>
        .popWork₁ (.local affineTransitionRevProgram.main) (fun _ => .invalid)
    | .local .finish => .jump .check
    | .local .invalid => .halt
    | .local label => affineTransitionRelabelSameOp .local
        (affineTransitionRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

def affineTransitionFamilyCfg (label : AffineTransitionFamilyLabel)
    (buffer₁ buffer₂ : Option AffineStmtScriptSym) (test : Bool)
    (input : List AffineStmtScriptSym) (output : List CircuitSym)
    (work₁ work₂ : List AffineStmtScriptSym)
    (first second third : List Unit) :
    BuilderCfg affineTransitionFamilyRevProgram where
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

def affineTransitionFamilyLoopCfg (input : List AffineStmtScriptSym)
    (output : List CircuitSym) :
    BuilderCfg affineTransitionFamilyRevProgram :=
  affineTransitionFamilyCfg .check none none false input output
    [] [] [] [] []

def affineTransitionFamilyFinishCfg (output : List CircuitSym) :
    BuilderCfg affineTransitionFamilyRevProgram :=
  affineTransitionFamilyCfg .finish none none false [] output
    [] [] [] [] []

def affineTransitionFamilyLiftCfg
    (c : BuilderCfg affineTransitionRevProgram) :
    BuilderCfg affineTransitionFamilyRevProgram where
  label := c.label.map .local
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

private theorem affineTransitionFamilyRelabel_stepOp
    (op : Op AffineStmtScriptSym CircuitSym
      AffineTransitionControllerLabel)
    (c : BuilderCfg affineTransitionRevProgram) :
    stepOp (affineTransitionRelabelSameOp
        AffineTransitionFamilyLabel.local op)
        (affineTransitionFamilyLiftCfg c) =
      affineTransitionFamilyLiftCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases input <;> cases work₁ <;> cases work₂ <;>
    cases counter₁ <;> cases counter₂ <;> cases counter₃ <;>
    cases op <;> rfl

private theorem affineTransitionFamily_op_local
    (label : AffineTransitionControllerLabel) (hfinish : label ≠ .finish) :
    affineTransitionFamilyRevProgram.op (.local label) =
      affineTransitionRelabelSameOp .local
        (affineTransitionRevProgram.op label) := by
  cases label <;> simp_all [affineTransitionFamilyRevProgram,
    affineTransitionRevProgram, affineTransitionRelabelSameOp]

theorem affineTransitionFamilyLift_step
    (c : BuilderCfg affineTransitionRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineTransitionFamilyRevProgram
        (affineTransitionFamilyLiftCfg c) =
      Option.map affineTransitionFamilyLiftCfg
        (step affineTransitionRevProgram c) := by
  unfold step
  rw [show (affineTransitionFamilyLiftCfg c).label =
    c.label.map .local by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hfinish : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineTransitionFamily_op_local label hfinish]
      exact congrArg some
        (affineTransitionFamilyRelabel_stepOp
          (affineTransitionRevProgram.op label) c)

private theorem affineTransitionFamily_iterate_none {σ : Type}
    (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem affineTransitionFamily_halt_no_return
    (a b : BuilderCfg affineTransitionRevProgram)
    (ha : a.label = some .finish) (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind (step affineTransitionRevProgram))^[n]
      (step affineTransitionRevProgram a) ≠ some b := by
  intro n
  let halted : BuilderCfg affineTransitionRevProgram :=
    { a with label := none, buffer₁ := none, buffer₂ := none, test := false }
  have hstep : step affineTransitionRevProgram a = some halted := by
    unfold step
    rw [ha]
    simp [affineTransitionRevProgram, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step affineTransitionRevProgram))^[n]
        (step affineTransitionRevProgram halted) ≠ some b
      have hnone : step affineTransitionRevProgram halted = none := rfl
      rw [hnone, affineTransitionFamily_iterate_none]
      simp

private theorem affineTransitionFamily_lift_iterations
    {a b : BuilderCfg affineTransitionRevProgram}
    (hb : b.label = some .finish) : ∀ n : Nat,
    (flip Option.bind (step affineTransitionRevProgram))^[n] (some a) = some b →
      (flip Option.bind (step affineTransitionFamilyRevProgram))^[n]
        (some (affineTransitionFamilyLiftCfg a)) =
          some (affineTransitionFamilyLiftCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineTransitionRevProgram))^[n]
        (step affineTransitionRevProgram a) = some b at h
      change (flip Option.bind (step affineTransitionFamilyRevProgram))^[n]
        (step affineTransitionFamilyRevProgram
          (affineTransitionFamilyLiftCfg a)) =
          some (affineTransitionFamilyLiftCfg b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact affineTransitionFamily_halt_no_return a b ha hb n h
      cases hsource : step affineTransitionRevProgram a with
      | none =>
          rw [hsource, affineTransitionFamily_iterate_none] at h
          contradiction
      | some c =>
          have hsim := affineTransitionFamilyLift_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineTransitionFamilyLift_runToFinish
    {a b : BuilderCfg affineTransitionRevProgram}
    (hb : b.label = some .finish) (m : Nat)
    (sourceRun : EvalsToInTime (step affineTransitionRevProgram)
      a (some b) m) :
    EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyLiftCfg a)
      (some (affineTransitionFamilyLiftCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineTransitionFamily_lift_iterations hb
    sourceRun.steps sourceRun.evals_in_steps

/-- Exact runtime through the redirectable family finish. -/
def affineTransitionFamilyRunSteps : List AffineTransitionScript → Nat
  | [] => 1
  | script :: rest =>
      2 + affineTransitionRunToFinishSteps script + 1 +
        affineTransitionFamilyRunSteps rest

/-- Exact runtime through every local transition while stopping at the outer
family check, before the controller inspects the first symbol of a following
phase. -/
def affineTransitionFamilyBodySteps : List AffineTransitionScript → Nat
  | [] => 0
  | script :: rest =>
      2 + affineTransitionRunToFinishSteps script + 1 +
        affineTransitionFamilyBodySteps rest

/-- Execute a runtime-length transition family and return to the clean outer
check state without consuming the following unary suffix. -/
def affineTransitionFamily_runToCheckWithTail
    (scripts : List AffineTransitionScript) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyLoopCfg
        (encodeAffineTransitionFamily scripts ++ tail.map .data) output)
      (some (affineTransitionFamilyLoopCfg (tail.map .data)
        ((affineTransitionFamilyGateStream scripts).reverse ++ output)))
      (affineTransitionFamilyBodySteps scripts) := by
  induction scripts generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons script rest ih =>
      let familyTail := encodeAffineTransitionFamilyUnary rest ++ tail
      let localOutput :=
        (affineTransitionGateStream script).reverse ++ output
      have hinput :
          encodeAffineTransitionFamily (script :: rest) ++ tail.map .data =
            .data .frameEnd ::
              encodeAffineTransitionScriptWithTail script familyTail := by
        simp [encodeAffineTransitionFamily,
          encodeAffineTransitionFamilyUnary, familyTail,
          encodeAffineTransitionScriptWithTail_eq_map, List.map_append,
          List.append_assoc]
      have hstart : EvalsToInTime (step affineTransitionFamilyRevProgram)
          (affineTransitionFamilyLoopCfg
            (encodeAffineTransitionFamily (script :: rest) ++ tail.map .data)
            output)
          (some (affineTransitionFamilyLiftCfg
            (affineTransitionLoopCfg
              (encodeAffineTransitionScriptWithTail script familyTail)
              output))) 2 := by
        rw [hinput]
        exact ⟨⟨2, rfl⟩, le_rfl⟩
      have hsource := affineTransition_runToFinishWithTail
        script familyTail output
      have hlocal := affineTransitionFamilyLift_runToFinish rfl _ hsource
      have htail : familyTail.map .data =
          encodeAffineTransitionFamily rest ++ tail.map .data := by
        simp [familyTail, encodeAffineTransitionFamily, List.map_append]
      have hreturn : EvalsToInTime (step affineTransitionFamilyRevProgram)
          (affineTransitionFamilyLiftCfg
            (affineTransitionFinishInputCfg familyTail localOutput))
          (some (affineTransitionFamilyLoopCfg
            (encodeAffineTransitionFamily rest ++ tail.map .data)
            localOutput)) 1 := by
        rw [← htail]
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hrest := ih localOutput
      let throughLocal := EvalsToInTime.trans
        (step affineTransitionFamilyRevProgram) 2
        (affineTransitionRunToFinishSteps script) _ _ _ hstart
        (by simpa [localOutput] using hlocal)
      let throughReturn := EvalsToInTime.trans
        (step affineTransitionFamilyRevProgram)
        (2 + affineTransitionRunToFinishSteps script) 1 _
        (affineTransitionFamilyLiftCfg
          (affineTransitionFinishInputCfg familyTail localOutput)) _
        (by
          convert throughLocal using 1
          omega)
        hreturn
      let full := EvalsToInTime.trans
        (step affineTransitionFamilyRevProgram)
        (2 + affineTransitionRunToFinishSteps script + 1)
        (affineTransitionFamilyBodySteps rest) _
        (affineTransitionFamilyLoopCfg
          (encodeAffineTransitionFamily rest ++ tail.map .data)
          localOutput) _
        (by
          convert throughReturn using 1
          omega)
        hrest
      convert full using 1
      · simp [affineTransitionFamilyGateStream, localOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineTransitionFamilyBodySteps]
        omega

/-- A single fixed controller executes every local script in a runtime-length
family and stops at a clean outer finish. -/
def affineTransitionFamily_runToFinish
    (scripts : List AffineTransitionScript) (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyLoopCfg
        (encodeAffineTransitionFamily scripts) output)
      (some (affineTransitionFamilyFinishCfg
        ((affineTransitionFamilyGateStream scripts).reverse ++ output)))
      (affineTransitionFamilyRunSteps scripts) := by
  induction scripts generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons script rest ih =>
      let familyTail := encodeAffineTransitionFamilyUnary rest
      let localOutput :=
        (affineTransitionGateStream script).reverse ++ output
      have hstart : EvalsToInTime (step affineTransitionFamilyRevProgram)
          (affineTransitionFamilyLoopCfg
            (encodeAffineTransitionFamily (script :: rest)) output)
          (some (affineTransitionFamilyLiftCfg
            (affineTransitionLoopCfg
              (encodeAffineTransitionScriptWithTail script familyTail)
              output))) 2 := by
        have hinput : encodeAffineTransitionFamily (script :: rest) =
            .data .frameEnd ::
              encodeAffineTransitionScriptWithTail script familyTail := by
          simp [encodeAffineTransitionFamily,
            encodeAffineTransitionFamilyUnary, familyTail,
            encodeAffineTransitionScriptWithTail_eq_map, List.map_append]
        rw [hinput]
        exact ⟨⟨2, rfl⟩, le_rfl⟩
      have hsource := affineTransition_runToFinishWithTail
        script familyTail output
      have hlocal := affineTransitionFamilyLift_runToFinish rfl _ hsource
      have hreturn : EvalsToInTime (step affineTransitionFamilyRevProgram)
          (affineTransitionFamilyLiftCfg
            (affineTransitionFinishInputCfg familyTail localOutput))
          (some (affineTransitionFamilyLoopCfg
            (encodeAffineTransitionFamily rest) localOutput)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hrest := ih localOutput
      let throughLocal := EvalsToInTime.trans
        (step affineTransitionFamilyRevProgram) 2
        (affineTransitionRunToFinishSteps script) _ _ _ hstart
        (by simpa [localOutput] using hlocal)
      let throughReturn := EvalsToInTime.trans
        (step affineTransitionFamilyRevProgram)
        (2 + affineTransitionRunToFinishSteps script) 1 _
        (affineTransitionFamilyLiftCfg
          (affineTransitionFinishInputCfg familyTail localOutput)) _
        (by
          convert throughLocal using 1
          omega)
        hreturn
      let full := EvalsToInTime.trans
        (step affineTransitionFamilyRevProgram)
        (2 + affineTransitionRunToFinishSteps script + 1)
        (affineTransitionFamilyRunSteps rest) _
        (affineTransitionFamilyLoopCfg
          (encodeAffineTransitionFamily rest) localOutput) _
        (by
          convert throughReturn using 1
          omega)
        hrest
      convert full using 1
      · simp [affineTransitionFamilyGateStream, localOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineTransitionFamilyRunSteps]
        omega

/-- Standalone family runtime, including the final halt instruction. -/
def affineTransitionFamilyTotalSteps
    (scripts : List AffineTransitionScript) : Nat :=
  affineTransitionFamilyRunSteps scripts + 1

def affineTransitionFamily_run
    (scripts : List AffineTransitionScript) (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyLoopCfg
        (encodeAffineTransitionFamily scripts) output)
      (some (haltCfg affineTransitionFamilyRevProgram
        ((affineTransitionFamilyGateStream scripts).reverse ++ output)))
      (affineTransitionFamilyTotalSteps scripts) := by
  let gateOutput :=
    (affineTransitionFamilyGateStream scripts).reverse ++ output
  have hfinish := affineTransitionFamily_runToFinish scripts output
  have hhalt : EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyFinishCfg gateOutput)
      (some (haltCfg affineTransitionFamilyRevProgram gateOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step affineTransitionFamilyRevProgram)
    (affineTransitionFamilyRunSteps scripts) 1 _
    (affineTransitionFamilyFinishCfg gateOutput) _
    (by simpa [gateOutput] using hfinish) hhalt
  simpa [affineTransitionFamilyTotalSteps, gateOutput, Nat.add_comm] using full

theorem affineTransitionRunToFinish_steps_le
    (script : AffineTransitionScript) :
    affineTransitionRunToFinishSteps script ≤
      500 * (encodeAffineTransitionLocalUnary script).length + 20 := by
  have hstmt := affineStmtScriptFinish_steps_le script.dispatch
  have hnarrow' := affineOrThenNotRev_steps_le
    script.narrowFrames script.narrowSource
  have heq : affineEqFinBodySteps script.eqFrames ≤
      113 * (encodeAffineEqFinFrames script.eqFrames).length := by
    induction script.eqFrames with
    | nil => rfl
    | cons frame rest ih =>
        have hframe := affineEqFinPair_steps_le frame
        simp only [affineEqFinBodySteps, encodeAffineEqFinFrames,
          List.flatMap_cons, List.length_append] at *
        omega
  have hand := affineAndFinBody_steps_le [script.finalAnd]
  have hlen : (encodeAffineTransitionLocalUnary script).length =
      (encodeAffineStmtControllerInput script.dispatch).length + 3 +
        (encodeAffineOrThenNotInput script.narrowFrames
          script.narrowSource).length + 1 +
        (encodeAffineEqFinFrames script.eqFrames).length + 1 +
        (encodeAffineAndFinFrames [script.finalAnd]).length + 1 := by
    simp [encodeAffineTransitionLocalUnary, encodeAffineTransitionTail,
      affineStmtTransitionBoundaryCode, encodeAffineStmtControllerInput,
      List.length_append]
    omega
  simp [affineOrThenNotRevSteps] at hnarrow'
  simp only [affineTransitionRunToFinishSteps]
  omega

/-- The transition-family body is linear in the exact family encoding and
does not charge the following phase separator. -/
theorem affineTransitionFamilyBody_steps_le
    (scripts : List AffineTransitionScript) :
    affineTransitionFamilyBodySteps scripts ≤
      500 * (encodeAffineTransitionFamily scripts).length := by
  induction scripts with
  | nil => simp [affineTransitionFamilyBodySteps,
      encodeAffineTransitionFamily, encodeAffineTransitionFamilyUnary]
  | cons script rest ih =>
      have hscript := affineTransitionRunToFinish_steps_le script
      simp [affineTransitionFamilyBodySteps, encodeAffineTransitionFamily,
        encodeAffineTransitionFamilyUnary, List.length_append] at *
      omega

/-- The family runtime is linear in its exact delimiter-bearing unary input. -/
theorem affineTransitionFamily_steps_le
    (scripts : List AffineTransitionScript) :
    affineTransitionFamilyTotalSteps scripts ≤
      500 * (encodeAffineTransitionFamily scripts).length + 2 := by
  induction scripts with
  | nil => simp [affineTransitionFamilyTotalSteps,
      affineTransitionFamilyRunSteps, encodeAffineTransitionFamily,
      encodeAffineTransitionFamilyUnary]
  | cons script rest ih =>
      have hscript := affineTransitionRunToFinish_steps_le script
      simp [affineTransitionFamilyTotalSteps,
        affineTransitionFamilyRunSteps, encodeAffineTransitionFamily,
        encodeAffineTransitionFamilyUnary, List.length_append] at *
      omega

/-- The compiled fixed family controller computes the reversed transition
gate stream in polynomial time from the exact runtime script encoding. -/
noncomputable def affineTransitionFamilyRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineTransitionFamily id
      (fun scripts : List AffineTransitionScript =>
        (affineTransitionFamilyGateStream scripts).reverse) where
  tm := compile affineTransitionFamilyRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 500 * Polynomial.X + 2
  outputsFun := fun scripts => by
    have builderRun := affineTransitionFamily_run scripts []
    have compiledRun := compile_evalsToInTime
      affineTransitionFamilyRevProgram builderRun
    rw [show affineTransitionFamilyLoopCfg
        (encodeAffineTransitionFamily scripts) [] =
          initialCfg affineTransitionFamilyRevProgram
            (encodeAffineTransitionFamily scripts) by rfl] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineTransitionFamilyRevProgram).step
        (_root_.Turing.initList (compile affineTransitionFamilyRevProgram)
          (encodeAffineTransitionFamily scripts))
        (some (_root_.Turing.haltList
          (compile affineTransitionFamilyRevProgram)
          (affineTransitionFamilyGateStream scripts).reverse))
        (affineTransitionFamilyTotalSteps scripts) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime :
        affineTransitionFamilyTotalSteps scripts ≤
          (500 * Polynomial.X + 2).eval
            (encodeAffineTransitionFamily scripts).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineTransitionFamily_steps_le scripts
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineTransitionFamilyRevProgram).step
        (_root_.Turing.initList (compile affineTransitionFamilyRevProgram)
          (encodeAffineTransitionFamily scripts))
        (some (_root_.Turing.haltList
          (compile affineTransitionFamilyRevProgram)
          (affineTransitionFamilyGateStream scripts).reverse))
        ((500 * Polynomial.X + 2).eval
          (encodeAffineTransitionFamily scripts).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the prepend-based output gives the forward transition-family
gate stream under a concrete polynomial-time TM2. -/
noncomputable def affineTransitionFamilyGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineTransitionFamily id affineTransitionFamilyGateStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineTransitionFamilyRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
