import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionController

/-!
# Optional complete-family equality controller

Some total Cook--Levin boundary constructors append a complete `EqFin` trace
when their target is representable and append no gates otherwise.  This fixed
controller implements both cases without selecting a different program.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

def encodeAffineOptionalEqFin :
    Option (List AffineEqFinPairFrame) → List UnaryFrameSym
  | none => []
  | some frames => .frameEnd :: encodeAffineEqFinFrames frames

def affineOptionalEqFinGateStream :
    Option (List AffineEqFinPairFrame) → List CircuitSym
  | none => []
  | some frames => affineEqFinGateStream frames

inductive AffineOptionalEqFinLabel
  | check
  | clearStart
  | eqFin (label : AffineEqFinLabel)
  | finish
  | invalid
deriving DecidableEq, Fintype

def affineOptionalEqFinCheckTarget :
    UnaryFrameSym → AffineOptionalEqFinLabel
  | .frameEnd => .clearStart
  | _ => .invalid

/-- One fixed program selects the zero-gate or complete-equality branch from
its runtime marker. -/
def affineOptionalEqFinRevProgram : Program UnaryFrameSym CircuitSym where
  Label := AffineOptionalEqFinLabel
  main := .check
  op
    | .check => .popInput .finish affineOptionalEqFinCheckTarget
    | .clearStart =>
        .popWork₁ (.eqFin affineEqFinRevProgram.main) (fun _ => .invalid)
    | .eqFin label => affineTransitionRelabelSameOp .eqFin
        (affineEqFinRevProgram.op label)
    | .finish => .halt
    | .invalid => .halt

def affineOptionalEqFinCfg (label : AffineOptionalEqFinLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CircuitSym)
    (work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineOptionalEqFinRevProgram where
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

def affineOptionalEqFinLoopCfg (input : List UnaryFrameSym)
    (output : List CircuitSym) :
    BuilderCfg affineOptionalEqFinRevProgram :=
  affineOptionalEqFinCfg .check none none false input output
    [] [] [] [] []

def affineOptionalEqFinLiftCfg (c : BuilderCfg affineEqFinRevProgram) :
    BuilderCfg affineOptionalEqFinRevProgram where
  label := c.label.map .eqFin
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

private theorem affineOptionalEqFinRelabel_stepOp
    (op : Op UnaryFrameSym CircuitSym AffineEqFinLabel)
    (c : BuilderCfg affineEqFinRevProgram) :
    stepOp (affineTransitionRelabelSameOp
        AffineOptionalEqFinLabel.eqFin op)
        (affineOptionalEqFinLiftCfg c) =
      affineOptionalEqFinLiftCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases input <;> cases work₁ <;> cases work₂ <;>
    cases counter₁ <;> cases counter₂ <;> cases counter₃ <;>
    cases op <;> rfl

private theorem affineOptionalEqFinLift_step
    (c : BuilderCfg affineEqFinRevProgram) :
    step affineOptionalEqFinRevProgram (affineOptionalEqFinLiftCfg c) =
      Option.map affineOptionalEqFinLiftCfg
        (step affineEqFinRevProgram c) := by
  unfold step
  rw [show (affineOptionalEqFinLiftCfg c).label =
    c.label.map .eqFin by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      exact congrArg some
        (affineOptionalEqFinRelabel_stepOp
          (affineEqFinRevProgram.op label) c)

private theorem affineOptionalEqFinLift_transition
    (state : Option (BuilderCfg affineEqFinRevProgram)) :
    (flip Option.bind (step affineOptionalEqFinRevProgram))
        (Option.map affineOptionalEqFinLiftCfg state) =
      Option.map affineOptionalEqFinLiftCfg
        ((flip Option.bind (step affineEqFinRevProgram)) state) := by
  cases state with
  | none => rfl
  | some c => exact affineOptionalEqFinLift_step c

private theorem affineOptionalEqFinLift_iterations (n : Nat)
    (state : Option (BuilderCfg affineEqFinRevProgram)) :
    (flip Option.bind (step affineOptionalEqFinRevProgram))^[n]
        (Option.map affineOptionalEqFinLiftCfg state) =
      Option.map affineOptionalEqFinLiftCfg
        ((flip Option.bind (step affineEqFinRevProgram))^[n] state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        affineOptionalEqFinLift_transition]
      exact ih _

private def affineOptionalEqFinLift_run
    {a : BuilderCfg affineEqFinRevProgram}
    {b : Option (BuilderCfg affineEqFinRevProgram)} (m : Nat)
    (sourceRun : EvalsToInTime (step affineEqFinRevProgram) a b m) :
    EvalsToInTime (step affineOptionalEqFinRevProgram)
      (affineOptionalEqFinLiftCfg a)
      (Option.map affineOptionalEqFinLiftCfg b) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have hlift := affineOptionalEqFinLift_iterations sourceRun.steps (some a)
  have hsource :
      (flip Option.bind (step affineEqFinRevProgram))^[sourceRun.steps]
          (some a) = b := sourceRun.evals_in_steps
  rw [hsource] at hlift
  simpa using hlift

def affineOptionalEqFinSteps :
    Option (List AffineEqFinPairFrame) → Nat
  | none => 2
  | some frames => 2 + affineEqFinRevSteps frames

/-- Exact execution of both total-boundary cases. -/
def affineOptionalEqFin_run
    (optionalFrames : Option (List AffineEqFinPairFrame))
    (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalEqFinRevProgram)
      (affineOptionalEqFinLoopCfg
        (encodeAffineOptionalEqFin optionalFrames) output)
      (some (haltCfg affineOptionalEqFinRevProgram
        ((affineOptionalEqFinGateStream optionalFrames).reverse ++ output)))
      (affineOptionalEqFinSteps optionalFrames) := by
  cases optionalFrames with
  | none => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | some frames =>
      have hstart : EvalsToInTime (step affineOptionalEqFinRevProgram)
          (affineOptionalEqFinLoopCfg
            (encodeAffineOptionalEqFin (some frames)) output)
          (some (affineOptionalEqFinLiftCfg
            (affineEqFinLoopCfg (encodeAffineEqFinFrames frames) output))) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      have hsource := affineEqFin_run frames output
      have hlift := affineOptionalEqFinLift_run _ hsource
      let full := EvalsToInTime.trans (step affineOptionalEqFinRevProgram)
        2 (affineEqFinRevSteps frames) _
        (affineOptionalEqFinLiftCfg
          (affineEqFinLoopCfg (encodeAffineEqFinFrames frames) output)) _
        hstart hlift
      convert full using 1
      · rfl
      · simp [affineOptionalEqFinSteps, Nat.add_comm]

/-- The optional wrapper remains linear in its exact marker-bearing input. -/
theorem affineOptionalEqFin_steps_le
    (optionalFrames : Option (List AffineEqFinPairFrame)) :
    affineOptionalEqFinSteps optionalFrames ≤
      113 * (encodeAffineOptionalEqFin optionalFrames).length + 5 := by
  cases optionalFrames with
  | none => norm_num [affineOptionalEqFinSteps, encodeAffineOptionalEqFin]
  | some frames =>
      have h := affineEqFinRev_steps_le frames
      simp [affineOptionalEqFinSteps, encodeAffineOptionalEqFin]
      omega

end CLRS.Chapter34.Turing.PolyBuilder
