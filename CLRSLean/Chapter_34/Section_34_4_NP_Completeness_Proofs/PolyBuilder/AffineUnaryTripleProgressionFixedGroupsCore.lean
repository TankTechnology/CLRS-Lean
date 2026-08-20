import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionFamily

/-!
# Fixed-size groups of affine triple progressions: controller core

This file lifts the verified one-progression controller under a finite group
cursor.  The arithmetic progression body is unchanged; the outer cursor only
records after which descriptor a group boundary must be emitted.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite phases of the descriptor loop, indexed by the current position in
a group of size `groupLast + 1`. -/
inductive AffineUnaryTripleProgressionFixedGroupLabel (groupLast : Nat)
  | check (position : Fin (groupLast + 1))
  | save (position : Fin (groupLast + 1)) (symbol : UnaryFrameSym)
  | restore (position : Fin (groupLast + 1))
  | clearBuffer (position : Fin (groupLast + 1))
  | body (position : Fin (groupLast + 1))
      (label : AffineUnaryTripleProgressionLabel)
  | finish
deriving DecidableEq, Fintype

private def fixedGroupRelabelOp (groupLast : Nat)
    (position : Fin (groupLast + 1)) :
    Op UnaryFrameSym UnaryFrameSym AffineUnaryTripleProgressionLabel →
      Op UnaryFrameSym UnaryFrameSym
        (AffineUnaryTripleProgressionFixedGroupLabel groupLast)
  | .pushOutput symbol next => .pushOutput symbol (.body position next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.body position next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.body position next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.body position nextEmpty)
        (fun symbol => .body position (nextMoved symbol))
  | .inc₁ next => .inc₁ (.body position next)
  | .inc₂ next => .inc₂ (.body position next)
  | .inc₃ next => .inc₃ (.body position next)
  | .dec₁ nextZero nextSucc =>
      .dec₁ (.body position nextZero) (.body position nextSucc)
  | .dec₂ nextZero nextSucc =>
      .dec₂ (.body position nextZero) (.body position nextSucc)
  | .dec₃ nextZero nextSucc =>
      .dec₃ (.body position nextZero) (.body position nextSucc)
  | .jump next => .jump (.body position next)
  | .halt => .halt

def fixedGroupNextPosition (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (hnotLast : position.val ≠ groupLast) : Fin (groupLast + 1) :=
  ⟨position.val + 1, by omega⟩

/-- The fixed controller executes adjacent descriptors and emits one outer
`frameEnd` after every `groupLast + 1` completed descriptors. -/
def affineUnaryTripleProgressionFixedGroupRevProgram (groupLast : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineUnaryTripleProgressionFixedGroupLabel groupLast
  main := .check ⟨0, by omega⟩
  op
    | .check position => .popInput .finish fun symbol =>
        .save position symbol
    | .save position symbol => .pushWork₁ symbol (.restore position)
    | .restore position => .moveWork₁Input .finish
        (fun _ => .clearBuffer position)
    | .clearBuffer position => .popWork₁
        (.body position affineUnaryTripleProgressionRevProgram.main)
        (fun _ => .finish)
    | .body position .halt =>
        if hlast : position.val = groupLast then
          .pushOutput .frameEnd (.check ⟨0, by omega⟩)
        else
          .jump (.check (fixedGroupNextPosition groupLast position hlast))
    | .body position label => fixedGroupRelabelOp groupLast position
        (affineUnaryTripleProgressionRevProgram.op label)
    | .finish => .halt

private def affineUnaryTripleProgressionFixedGroupCfg (groupLast : Nat)
    (label : AffineUnaryTripleProgressionFixedGroupLabel groupLast)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast) where
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

/-- Clean entry at an arbitrary finite group position. -/
def affineUnaryTripleProgressionFixedGroupLoopCfg (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast) :=
  affineUnaryTripleProgressionFixedGroupCfg groupLast (.check position)
    none none false input output [] [] [] [] []

/-- Clean pre-halt exit of the fixed-group controller. -/
def affineUnaryTripleProgressionFixedGroupFinishCfg (groupLast : Nat)
    (output : List UnaryFrameSym) :
    BuilderCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast) :=
  affineUnaryTripleProgressionFixedGroupCfg groupLast .finish
    none none false [] output [] [] [] [] []

/-- The public loop entry at group position zero is exactly the standard
initial configuration of the fixed-group program. -/
@[simp] theorem affineUnaryTripleProgressionFixedGroup_initialCfg_eq_loop
    (groupLast : Nat) (input : List UnaryFrameSym) :
    initialCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
        input =
      affineUnaryTripleProgressionFixedGroupLoopCfg groupLast
        ⟨0, by omega⟩ input [] := rfl

private def liftFixedGroupBodyCfg (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (c : BuilderCfg affineUnaryTripleProgressionRevProgram) :
    BuilderCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast) where
  label := c.label.map (.body position)
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

/-- Lifted entry configuration of one progression body. -/
def affineUnaryTripleProgressionFixedGroupBodyLoopCfg (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast) :=
  liftFixedGroupBodyCfg groupLast position
    (affineUnaryTripleProgressionLoopCfg input output)

/-- Lifted body exit before the fixed group cursor advances. -/
def affineUnaryTripleProgressionFixedGroupBodyFinishCfg (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (tail output : List UnaryFrameSym) :
    BuilderCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast) :=
  liftFixedGroupBodyCfg groupLast position
    (affineUnaryTripleProgressionFinishCfg tail output)

private theorem fixedGroupRelabel_stepOp (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (op : Op UnaryFrameSym UnaryFrameSym
      AffineUnaryTripleProgressionLabel)
    (c : BuilderCfg affineUnaryTripleProgressionRevProgram) :
    stepOp (fixedGroupRelabelOp groupLast position op)
        (liftFixedGroupBodyCfg groupLast position c) =
      liftFixedGroupBodyCfg groupLast position (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [fixedGroupRelabelOp, liftFixedGroupBodyCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem fixedGroup_op_body (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (label : AffineUnaryTripleProgressionLabel)
    (hexit : label ≠ .halt) :
    (affineUnaryTripleProgressionFixedGroupRevProgram groupLast).op
        (.body position label) =
      fixedGroupRelabelOp groupLast position
        (affineUnaryTripleProgressionRevProgram.op label) := by
  cases label <;>
    simp_all [affineUnaryTripleProgressionFixedGroupRevProgram]

private theorem liftFixedGroupBody_step (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (c : BuilderCfg affineUnaryTripleProgressionRevProgram)
    (hexit : c.label ≠ some .halt) :
    step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
        (liftFixedGroupBodyCfg groupLast position c) =
      Option.map (liftFixedGroupBodyCfg groupLast position)
        (step affineUnaryTripleProgressionRevProgram c) := by
  unfold step
  rw [show (liftFixedGroupBodyCfg groupLast position c).label =
      c.label.map (.body position) by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .halt := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [fixedGroup_op_body groupLast position label hlabelExit]
      exact congrArg some
        (fixedGroupRelabel_stepOp groupLast position
          (affineUnaryTripleProgressionRevProgram.op label) c)

private theorem fixedGroup_iterate_bind_none {σ : Type}
    (f : σ → Option σ) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem fixedGroup_haltExit_no_return
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
      rw [hnone, fixedGroup_iterate_bind_none]
      simp

private theorem fixedGroup_lift_iterations_to_finish (groupLast : Nat)
    (position : Fin (groupLast + 1))
    {a b : BuilderCfg affineUnaryTripleProgressionRevProgram}
    (hb : b.label = some .halt) : ∀ n : Nat,
    (flip Option.bind (step affineUnaryTripleProgressionRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind
        (step (affineUnaryTripleProgressionFixedGroupRevProgram
          groupLast)))^[n]
          (some (liftFixedGroupBodyCfg groupLast position a)) =
            some (liftFixedGroupBodyCfg groupLast position b) := by
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
      change (flip Option.bind (step
        (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)))^[n]
          (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
            (liftFixedGroupBodyCfg groupLast position a)) =
              some (liftFixedGroupBodyCfg groupLast position b)
      have haexit : a.label ≠ some .halt := by
        intro ha
        exact fixedGroup_haltExit_no_return
          (.halt : AffineUnaryTripleProgressionLabel) rfl a b ha hb n h
      cases hsource : step affineUnaryTripleProgressionRevProgram a with
      | none =>
          rw [hsource, fixedGroup_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftFixedGroupBody_step groupLast position a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

/-- Four-step dispatch from a nonempty descriptor suffix into the unchanged
progression body. -/
def affineUnaryTripleProgressionFixedGroup_dispatch_run (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (input output : List UnaryFrameSym) (hinput : input ≠ []) :
    EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (affineUnaryTripleProgressionFixedGroupLoopCfg groupLast position
        input output)
      (some (affineUnaryTripleProgressionFixedGroupBodyLoopCfg groupLast
        position input output)) 4 := by
  cases input with
  | nil => contradiction
  | cons symbol rest => exact ⟨⟨4, rfl⟩, le_rfl⟩

/-- Contextual execution of one descriptor under the finite group cursor. -/
def affineUnaryTripleProgressionFixedGroup_body_run (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (progression : AffineUnaryTripleProgression)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (affineUnaryTripleProgressionFixedGroupBodyLoopCfg groupLast position
        (encodeAffineUnaryTripleProgression progression ++ tail) output)
      (some (affineUnaryTripleProgressionFixedGroupBodyFinishCfg groupLast
        position tail
        ((affineUnaryTripleProgressionFrameStream progression).reverse ++
          output)))
      (affineUnaryTripleProgressionBodySteps progression) := by
  have sourceRun := affineUnaryTripleProgression_runToFinishWithTail
    progression tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  change
    (flip Option.bind
      (step (affineUnaryTripleProgressionFixedGroupRevProgram
        groupLast)))^[sourceRun.steps]
      (some (liftFixedGroupBodyCfg groupLast position
        (affineUnaryTripleProgressionLoopCfg
          (encodeAffineUnaryTripleProgression progression ++ tail) output))) =
    some (liftFixedGroupBodyCfg groupLast position
      (affineUnaryTripleProgressionFinishCfg tail
        ((affineUnaryTripleProgressionFrameStream progression).reverse ++
          output)))
  exact fixedGroup_lift_iterations_to_finish groupLast position rfl
    sourceRun.steps sourceRun.evals_in_steps

/-- Boundary bridge after the last descriptor of a fixed-size group. -/
def affineUnaryTripleProgressionFixedGroup_lastBridge_run (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (hlast : position.val = groupLast)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (affineUnaryTripleProgressionFixedGroupBodyFinishCfg groupLast
        position tail output)
      (some (affineUnaryTripleProgressionFixedGroupLoopCfg groupLast
        ⟨0, by omega⟩ tail (UnaryFrameSym.frameEnd :: output))) 1 := by
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  change
    step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
        (affineUnaryTripleProgressionFixedGroupCfg groupLast
          (.body position .halt) none none false tail output [] [] [] [] []) =
      some (affineUnaryTripleProgressionFixedGroupCfg groupLast
        (.check ⟨0, by omega⟩) none none false tail
        (UnaryFrameSym.frameEnd :: output) [] [] [] [] [])
  simp [step, stepOp,
    affineUnaryTripleProgressionFixedGroupRevProgram, hlast,
    affineUnaryTripleProgressionFixedGroupCfg]

/-- Ordinary bridge between two descriptors inside one fixed-size group. -/
def affineUnaryTripleProgressionFixedGroup_nextBridge_run (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (hnotLast : position.val ≠ groupLast)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (affineUnaryTripleProgressionFixedGroupBodyFinishCfg groupLast
        position tail output)
      (some (affineUnaryTripleProgressionFixedGroupLoopCfg groupLast
        (fixedGroupNextPosition groupLast position hnotLast)
        tail output)) 1 := by
  refine ⟨⟨1, ?_⟩, le_rfl⟩
  change
    step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
        (affineUnaryTripleProgressionFixedGroupCfg groupLast
          (.body position .halt) none none false tail output [] [] [] [] []) =
      some (affineUnaryTripleProgressionFixedGroupCfg groupLast
        (.check (fixedGroupNextPosition groupLast position hnotLast))
        none none false tail output [] [] [] [] [])
  simp [step, stepOp,
    affineUnaryTripleProgressionFixedGroupRevProgram, hnotLast,
    affineUnaryTripleProgressionFixedGroupCfg]

end CLRS.Chapter34.Turing.PolyBuilder
