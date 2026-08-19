import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import Mathlib.Tactic

/-!
# Self-contained runtime source for one validity-tail stack

The lower stack source assumes that its three cell-coordinate counters are
already loaded.  This layer supplies the missing runtime boundary: it loads
those counters from an explicit unary triple, executes the whole stack frame,
and clears all counters before exposing a continuation.  Consequently the
component can be iterated by a fixed finite stack-family controller.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Fully explicit source invocation for one runtime stack. -/
def encodeAffineRuntimeStackStandaloneInvocation
    (seed : AffineRuntimeStackSourceSeed) : List UnaryFrameSym :=
  encodeUnaryFrame [seed.cellRight, seed.cellLeft, seed.cellBlank] ++
    encodeAffineRuntimeStackSourceInvocation seed

/-- Loader, stack kernel, and counter-cleanup phases. -/
inductive AffineRuntimeStackStandaloneLabel (blankStep : Nat)
  | loader (label : UnaryTripleLoaderLabel)
  | stack (label : AffineRuntimeStackSourceLabel blankStep)
  | clearRight | clearLeft | clearBlank
  | finish | invalid
deriving DecidableEq, Fintype

private def standaloneStackRelabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
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

/-- One fixed controller from the explicit source invocation to a clean
post-stack continuation. -/
def affineRuntimeStackStandaloneRevProgram (blankStep : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineRuntimeStackStandaloneLabel blankStep
  main := .loader .load₁
  op
    | .loader .ready =>
        .popWork₁ (.stack (affineRuntimeStackSourceRevProgram blankStep).main)
          (fun _ => .invalid)
    | .loader label => standaloneStackRelabelOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label)
    | .stack .finish => .popWork₁ .clearRight (fun _ => .invalid)
    | .stack label => standaloneStackRelabelOp .stack
        ((affineRuntimeStackSourceRevProgram blankStep).op label)
    | .clearRight => .dec₁ .clearLeft .clearRight
    | .clearLeft => .dec₂ .clearBlank .clearLeft
    | .clearBlank => .dec₃ .finish .clearBlank
    | .finish => .halt
    | .invalid => .halt

private def affineRuntimeStackStandaloneCfg {blankStep : Nat}
    (label : AffineRuntimeStackStandaloneLabel blankStep)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (right left blank : List Unit) :
    BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := right
  counter₂ := left
  counter₃ := blank

/-- Clean entry with all local counters empty. -/
def affineRuntimeStackStandaloneLoopCfg (blankStep : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep) :=
  affineRuntimeStackStandaloneCfg (.loader .load₁) none none false
    input output [] [] [] [] []

/-- Clean redirectable exit after one complete stack invocation. -/
def affineRuntimeStackStandaloneFinishCfg (blankStep : Nat)
    (tail output : List UnaryFrameSym) :
    BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep) :=
  affineRuntimeStackStandaloneCfg .finish none none false
    tail output [] [] [] [] []

private def standaloneStackRelabelCfg {blankStep : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → AffineRuntimeStackStandaloneLabel blankStep)
    (c : BuilderCfg P) :
    BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep) where
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

private def liftStandaloneLoaderCfg {blankStep : Nat}
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep) :=
  standaloneStackRelabelCfg .loader c

private def liftStandaloneStackCfg {blankStep : Nat}
    (c : BuilderCfg (affineRuntimeStackSourceRevProgram blankStep)) :
    BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep) :=
  standaloneStackRelabelCfg .stack c

private theorem standaloneStackRelabel_stepOp {blankStep : Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label → AffineRuntimeStackStandaloneLabel blankStep)
    (op : Op UnaryFrameSym UnaryFrameSym P.Label) (c : BuilderCfg P) :
    stepOp (standaloneStackRelabelOp tag op)
        (standaloneStackRelabelCfg tag c) =
      standaloneStackRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [standaloneStackRelabelOp, standaloneStackRelabelCfg,
      stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineRuntimeStackStandalone_op_loader {blankStep : Nat}
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    (affineRuntimeStackStandaloneRevProgram blankStep).op (.loader label) =
      standaloneStackRelabelOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) := by
  cases label <;>
    simp_all [affineRuntimeStackStandaloneRevProgram] <;> rfl

private theorem affineRuntimeStackStandalone_op_stack {blankStep : Nat}
    (label : AffineRuntimeStackSourceLabel blankStep)
    (hexit : label ≠ .finish) :
    (affineRuntimeStackStandaloneRevProgram blankStep).op (.stack label) =
      standaloneStackRelabelOp .stack
        ((affineRuntimeStackSourceRevProgram blankStep).op label) := by
  cases label <;>
    simp_all [affineRuntimeStackStandaloneRevProgram] <;> rfl

private theorem liftStandaloneLoader_step {blankStep : Nat}
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym))
    (hexit : c.label ≠ some .ready) :
    step (affineRuntimeStackStandaloneRevProgram blankStep)
        (liftStandaloneLoaderCfg c) =
      Option.map liftStandaloneLoaderCfg
        (step (unaryTripleLoaderProgramFor UnaryFrameSym) c) := by
  unfold step
  rw [show (liftStandaloneLoaderCfg c).label = c.label.map .loader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineRuntimeStackStandalone_op_loader label hlabelExit]
      exact congrArg some
        (standaloneStackRelabel_stepOp .loader
          ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) c)

private theorem liftStandaloneStack_step {blankStep : Nat}
    (c : BuilderCfg (affineRuntimeStackSourceRevProgram blankStep))
    (hexit : c.label ≠ some .finish) :
    step (affineRuntimeStackStandaloneRevProgram blankStep)
        (liftStandaloneStackCfg c) =
      Option.map liftStandaloneStackCfg
        (step (affineRuntimeStackSourceRevProgram blankStep) c) := by
  unfold step
  rw [show (liftStandaloneStackCfg c).label = c.label.map .stack by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineRuntimeStackStandalone_op_stack label hlabelExit]
      exact congrArg some
        (standaloneStackRelabel_stepOp .stack
          ((affineRuntimeStackSourceRevProgram blankStep).op label) c)

private theorem standaloneStack_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem standaloneStack_haltExit_no_return
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
      rw [hnone, standaloneStack_iterate_bind_none]
      simp

private theorem standaloneStack_lift_iterations_to_haltExit
    {blankStep : Nat} {P : Program UnaryFrameSym UnaryFrameSym}
    (exit : P.Label) (hop : P.op exit = .halt)
    (tr : BuilderCfg P →
      BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep))
    (hstep : ∀ c, c.label ≠ some exit →
      step (affineRuntimeStackStandaloneRevProgram blankStep) (tr c) =
        Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind
        (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[n]
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
      change (flip Option.bind
        (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[n]
          (step (affineRuntimeStackStandaloneRevProgram blankStep) (tr a)) =
            some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact standaloneStack_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, standaloneStack_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineRuntimeStackStandalone_loader_run (blankStep : Nat)
    (seed : AffineRuntimeStackSourceSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step (affineRuntimeStackStandaloneRevProgram blankStep))
      (liftStandaloneLoaderCfg
        (unaryTripleLoaderCfgFor .load₁ none
          (encodeUnaryFrame [seed.cellRight, seed.cellLeft, seed.cellBlank] ++
            (encodeAffineRuntimeStackSourceInvocation seed ++ tail))
          output [] [] [] [] []))
      (some (liftStandaloneLoaderCfg
        (unaryTripleLoaderReadyCfgFor seed.cellRight seed.cellLeft
          seed.cellBlank
          (encodeAffineRuntimeStackSourceInvocation seed ++ tail)
          output [] [])))
      (unaryTripleLoaderSteps seed.cellRight seed.cellLeft seed.cellBlank) := by
  have sourceRun := unaryTripleLoader_runFor seed.cellRight seed.cellLeft
    seed.cellBlank (encodeAffineRuntimeStackSourceInvocation seed ++ tail)
    output [] []
  have htarget :
      (unaryTripleLoaderReadyCfgFor seed.cellRight seed.cellLeft
        seed.cellBlank (encodeAffineRuntimeStackSourceInvocation seed ++ tail)
        output [] []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact standaloneStack_lift_iterations_to_haltExit
    UnaryTripleLoaderLabel.ready rfl
    liftStandaloneLoaderCfg liftStandaloneLoader_step htarget
    sourceRun.steps sourceRun.evals_in_steps

private def affineRuntimeStackStandalone_stack_run (blankStep : Nat)
    (seed : AffineRuntimeStackSourceSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step (affineRuntimeStackStandaloneRevProgram blankStep))
      (liftStandaloneStackCfg
        (affineRuntimeStackSourceLoadedCfgWithTail blankStep seed tail output))
      (some (liftStandaloneStackCfg
        (affineRuntimeStackSourceFinishCfgWithTail blankStep seed tail
          ((encodeAffineStackFrame
            (affineRuntimeStackSourceFrame blankStep seed)).reverse ++ output))))
      (affineRuntimeStackSourceSteps blankStep seed) := by
  have sourceRun := affineRuntimeStackSource_runToFinishWithTail blankStep seed
    tail output
  have htarget :
      (affineRuntimeStackSourceFinishCfgWithTail blankStep seed tail
        ((encodeAffineStackFrame
          (affineRuntimeStackSourceFrame blankStep seed)).reverse ++ output)
        ).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact standaloneStack_lift_iterations_to_haltExit
    (AffineRuntimeStackSourceLabel.finish (blankStep := blankStep)) rfl
    liftStandaloneStackCfg liftStandaloneStack_step htarget
    sourceRun.steps sourceRun.evals_in_steps

private theorem affineRuntimeStackStandalone_clearRight_eval
    {blankStep : Nat} (value : Nat)
    (buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (left blank : List Unit) :
    (flip Option.bind
      (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[value + 1]
      (some (affineRuntimeStackStandaloneCfg .clearRight none buffer₂ test
        input output work₁ work₂ (List.replicate value ()) left blank)) =
      some (affineRuntimeStackStandaloneCfg .clearLeft none buffer₂ false
        input output work₁ work₂ [] left blank) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[value + 1]
          (some (affineRuntimeStackStandaloneCfg .clearRight none buffer₂ true
            input output work₁ work₂ (List.replicate value ()) left blank)) = _
      simpa using ih true

private theorem affineRuntimeStackStandalone_clearLeft_eval
    {blankStep : Nat} (value : Nat)
    (buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (blank : List Unit) :
    (flip Option.bind
      (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[value + 1]
      (some (affineRuntimeStackStandaloneCfg .clearLeft none buffer₂ test
        input output work₁ work₂ [] (List.replicate value ()) blank)) =
      some (affineRuntimeStackStandaloneCfg .clearBlank none buffer₂ false
        input output work₁ work₂ [] [] blank) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[value + 1]
          (some (affineRuntimeStackStandaloneCfg .clearLeft none buffer₂ true
            input output work₁ work₂ [] (List.replicate value ()) blank)) = _
      simpa using ih true

private theorem affineRuntimeStackStandalone_clearBlank_eval
    {blankStep : Nat} (value : Nat)
    (buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[value + 1]
      (some (affineRuntimeStackStandaloneCfg .clearBlank none buffer₂ test
        input output work₁ work₂ [] [] (List.replicate value ()))) =
      some (affineRuntimeStackStandaloneCfg .finish none buffer₂ false
        input output work₁ work₂ [] [] []) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineRuntimeStackStandaloneRevProgram blankStep)))^[value + 1]
          (some (affineRuntimeStackStandaloneCfg .clearBlank none buffer₂ true
            input output work₁ work₂ [] [] (List.replicate value ()))) = _
      simpa using ih true

private def affineRuntimeStackStandalone_clear_run (blankStep : Nat)
    (right left blank : Nat) (initialTest : Bool)
    (input output : List UnaryFrameSym) :
    EvalsToInTime (step (affineRuntimeStackStandaloneRevProgram blankStep))
      (affineRuntimeStackStandaloneCfg .clearRight none none initialTest
        input output [] [] (List.replicate right ())
        (List.replicate left ()) (List.replicate blank ()))
      (some (affineRuntimeStackStandaloneFinishCfg blankStep input output))
      ((right + 1) + (left + 1) + (blank + 1)) := by
  let afterRight := affineRuntimeStackStandaloneCfg
    (blankStep := blankStep) .clearLeft none none false input output [] [] []
    (List.replicate left ()) (List.replicate blank ())
  let afterLeft := affineRuntimeStackStandaloneCfg
    (blankStep := blankStep) .clearBlank none none false input output [] [] [] []
    (List.replicate blank ())
  have hright : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep))
      (affineRuntimeStackStandaloneCfg .clearRight none none initialTest
        input output [] [] (List.replicate right ())
        (List.replicate left ()) (List.replicate blank ()))
      (some afterRight) (right + 1) :=
    ⟨⟨right + 1, by
      simpa [afterRight] using
        affineRuntimeStackStandalone_clearRight_eval (blankStep := blankStep)
          right none initialTest input output [] [] (List.replicate left ())
          (List.replicate blank ())⟩, le_rfl⟩
  have hleft : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep)) afterRight
      (some afterLeft) (left + 1) :=
    ⟨⟨left + 1, by
      simpa [afterRight, afterLeft] using
        affineRuntimeStackStandalone_clearLeft_eval (blankStep := blankStep)
          left none false input output [] [] (List.replicate blank ())⟩,
      le_rfl⟩
  have hblank : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep)) afterLeft
      (some (affineRuntimeStackStandaloneFinishCfg blankStep input output))
      (blank + 1) :=
    ⟨⟨blank + 1, by
      simpa [afterLeft, affineRuntimeStackStandaloneFinishCfg] using
        affineRuntimeStackStandalone_clearBlank_eval (blankStep := blankStep)
          blank none false input output [] []⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step (affineRuntimeStackStandaloneRevProgram blankStep))
    (right + 1) (left + 1) _ afterRight _ hright hleft
  let full := EvalsToInTime.trans
    (step (affineRuntimeStackStandaloneRevProgram blankStep))
    ((left + 1) + (right + 1)) (blank + 1) _ afterLeft _ h₁ hblank
  convert full using 1
  omega

/-- Exact runtime of the self-contained stack source. -/
def affineRuntimeStackStandaloneSteps (blankStep : Nat)
    (seed : AffineRuntimeStackSourceSeed) : Nat :=
  unaryTripleLoaderSteps seed.cellRight seed.cellLeft seed.cellBlank + 1 +
    affineRuntimeStackSourceSteps blankStep seed + 1 +
    ((seed.cellRight + 6 * seed.count + 1) +
      (seed.cellLeft - seed.count + 1) +
      (seed.cellBlank + blankStep * seed.count + 1))

/-- The self-contained fixed controller emits exactly one complete stack and
returns with empty counters, ready for an adjacent invocation. -/
def affineRuntimeStackStandalone_runToFinish (blankStep : Nat)
    (seed : AffineRuntimeStackSourceSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step (affineRuntimeStackStandaloneRevProgram blankStep))
      (affineRuntimeStackStandaloneLoopCfg blankStep
        (encodeAffineRuntimeStackStandaloneInvocation seed ++ tail) output)
      (some (affineRuntimeStackStandaloneFinishCfg blankStep tail
        ((encodeAffineStackFrame
          (affineRuntimeStackSourceFrame blankStep seed)).reverse ++ output)))
      (affineRuntimeStackStandaloneSteps blankStep seed) := by
  let invocation := encodeAffineRuntimeStackSourceInvocation seed
  let stackOutput :=
    (encodeAffineStackFrame
      (affineRuntimeStackSourceFrame blankStep seed)).reverse ++ output
  let loaderStart := liftStandaloneLoaderCfg (blankStep := blankStep)
    (unaryTripleLoaderCfgFor .load₁ none
      (encodeUnaryFrame [seed.cellRight, seed.cellLeft, seed.cellBlank] ++
        invocation ++ tail) output [] [] [] [] [])
  let loaderDone := liftStandaloneLoaderCfg (blankStep := blankStep)
    (unaryTripleLoaderReadyCfgFor seed.cellRight seed.cellLeft seed.cellBlank
      (invocation ++ tail) output [] [])
  let stackStart := liftStandaloneStackCfg
    (affineRuntimeStackSourceLoadedCfgWithTail blankStep seed tail output)
  let stackDone := liftStandaloneStackCfg
    (affineRuntimeStackSourceFinishCfgWithTail blankStep seed tail stackOutput)
  let clearStart := affineRuntimeStackStandaloneCfg
    (blankStep := blankStep) .clearRight none none
    (affineCellProgressionSourceFinishTest seed.count false)
    tail stackOutput [] []
    (List.replicate (seed.cellRight + 6 * seed.count) ())
    (List.replicate (seed.cellLeft - seed.count) ())
    (List.replicate (seed.cellBlank + blankStep * seed.count) ())
  have hloader : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep)) loaderStart
      (some loaderDone)
      (unaryTripleLoaderSteps seed.cellRight seed.cellLeft seed.cellBlank) := by
    simpa [loaderStart, loaderDone, invocation, List.append_assoc] using
      affineRuntimeStackStandalone_loader_run blankStep seed tail output
  have hloaderBridge : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep)) loaderDone
      (some stackStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hstack : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep)) stackStart
      (some stackDone) (affineRuntimeStackSourceSteps blankStep seed) := by
    simpa [stackStart, stackDone, stackOutput] using
      affineRuntimeStackStandalone_stack_run blankStep seed tail output
  have hstackBridge : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep)) stackDone
      (some clearStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hclear : EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram blankStep)) clearStart
      (some (affineRuntimeStackStandaloneFinishCfg blankStep tail stackOutput))
      (((seed.cellRight + 6 * seed.count) + 1) +
        ((seed.cellLeft - seed.count) + 1) +
        ((seed.cellBlank + blankStep * seed.count) + 1)) := by
    simpa [clearStart] using affineRuntimeStackStandalone_clear_run blankStep
      (seed.cellRight + 6 * seed.count) (seed.cellLeft - seed.count)
      (seed.cellBlank + blankStep * seed.count)
      (affineCellProgressionSourceFinishTest seed.count false)
      tail stackOutput
  let h₁ := EvalsToInTime.trans
    (step (affineRuntimeStackStandaloneRevProgram blankStep)) _ 1 _
      loaderDone _ hloader hloaderBridge
  let h₂ := EvalsToInTime.trans
    (step (affineRuntimeStackStandaloneRevProgram blankStep)) _ _ _
      stackStart _ h₁ hstack
  let h₃ := EvalsToInTime.trans
    (step (affineRuntimeStackStandaloneRevProgram blankStep)) _ 1 _
      stackDone _ h₂ hstackBridge
  let full := EvalsToInTime.trans
    (step (affineRuntimeStackStandaloneRevProgram blankStep)) _ _ _
      clearStart _ h₃ hclear
  convert full using 1
  · simp [affineRuntimeStackStandaloneLoopCfg,
      encodeAffineRuntimeStackStandaloneInvocation, loaderStart, invocation,
      liftStandaloneLoaderCfg, standaloneStackRelabelCfg,
      unaryTripleLoaderCfgFor, affineRuntimeStackStandaloneCfg,
      List.append_assoc]
  · simp [affineRuntimeStackStandaloneSteps]
    omega

/-- Quadratic bound in the full unary payload of the self-contained source. -/
theorem affineRuntimeStackStandaloneSteps_le (blankStep : Nat)
    (seed : AffineRuntimeStackSourceSeed) :
    affineRuntimeStackStandaloneSteps blankStep seed ≤
      100 * (blankStep + 1) *
        ((encodeUnaryFrame [seed.count, seed.maskStart,
            seed.maskBase + seed.count]).length + seed.count +
          seed.cellRight + seed.cellLeft + seed.cellBlank + 1) ^ 2 := by
  let headerLength := (encodeUnaryFrame [seed.count, seed.maskStart,
    seed.maskBase + seed.count]).length
  let payload := headerLength + seed.count + seed.cellRight +
    seed.cellLeft + seed.cellBlank + 1
  have hpayload : 1 ≤ payload := by simp [payload]
  have hcount : seed.count ≤ payload := by dsimp only [payload]; omega
  have hright : seed.cellRight ≤ payload := by dsimp only [payload]; omega
  have hleft : seed.cellLeft ≤ payload := by dsimp only [payload]; omega
  have hblank : seed.cellBlank ≤ payload := by dsimp only [payload]; omega
  have hsource := affineRuntimeStackSourceSteps_le blankStep seed
  have hrest :
      unaryTripleLoaderSteps seed.cellRight seed.cellLeft seed.cellBlank + 2 +
          ((seed.cellRight + 6 * seed.count + 1) +
            (seed.cellLeft - seed.count + 1) +
            (seed.cellBlank + blankStep * seed.count + 1)) ≤
        30 * (blankStep + 1) * payload ^ 2 := by
    simp only [unaryTripleLoaderSteps]
    have hsub : seed.cellLeft - seed.count ≤ seed.cellLeft := Nat.sub_le _ _
    have hblankProduct : blankStep * seed.count ≤ blankStep * payload :=
      Nat.mul_le_mul_left blankStep hcount
    have hlinearRaw :
        2 * (seed.cellRight + seed.cellLeft + seed.cellBlank) + 3 + 2 +
            ((seed.cellRight + 6 * seed.count + 1) +
              (seed.cellLeft - seed.count + 1) +
              (seed.cellBlank + blankStep * seed.count + 1)) ≤
          blankStep * payload + 18 * payload + 8 := by
      omega
    have hlinear :
        blankStep * payload + 18 * payload + 8 =
          (blankStep + 18) * payload + 8 := by ring
    have hpayloadSquare : payload ≤ payload ^ 2 := by nlinarith
    have hcoeff : blankStep + 26 ≤ 30 * (blankStep + 1) := by omega
    calc
      2 * (seed.cellRight + seed.cellLeft + seed.cellBlank) + 3 + 2 +
            ((seed.cellRight + 6 * seed.count + 1) +
              (seed.cellLeft - seed.count + 1) +
              (seed.cellBlank + blankStep * seed.count + 1)) ≤
          (blankStep + 18) * payload + 8 := by
        simpa [hlinear] using hlinearRaw
      _ ≤ (blankStep + 26) * payload := by nlinarith
      _ ≤ (30 * (blankStep + 1)) * payload :=
        Nat.mul_le_mul_right payload hcoeff
      _ ≤ 30 * (blankStep + 1) * payload ^ 2 := by
        exact Nat.mul_le_mul_left (30 * (blankStep + 1)) hpayloadSquare
  calc
    affineRuntimeStackStandaloneSteps blankStep seed =
        affineRuntimeStackSourceSteps blankStep seed +
          (unaryTripleLoaderSteps seed.cellRight seed.cellLeft seed.cellBlank +
            2 + ((seed.cellRight + 6 * seed.count + 1) +
              (seed.cellLeft - seed.count + 1) +
              (seed.cellBlank + blankStep * seed.count + 1))) := by
      simp [affineRuntimeStackStandaloneSteps]
      omega
    _ ≤ 70 * (blankStep + 1) * payload ^ 2 +
          30 * (blankStep + 1) * payload ^ 2 :=
      Nat.add_le_add (by simpa [payload, headerLength] using hsource) hrest
    _ = 100 * (blankStep + 1) * payload ^ 2 := by ring

/-- The same quadratic bound stated directly in the explicit invocation
length, suitable for outer-family accounting. -/
theorem affineRuntimeStackStandaloneSteps_le_encoding (blankStep : Nat)
    (seed : AffineRuntimeStackSourceSeed) :
    affineRuntimeStackStandaloneSteps blankStep seed ≤
      100 * (blankStep + 1) *
        (encodeAffineRuntimeStackStandaloneInvocation seed).length ^ 2 := by
  have hsource := affineRuntimeStackStandaloneSteps_le blankStep seed
  have hlength :
      (encodeUnaryFrame [seed.count, seed.maskStart,
          seed.maskBase + seed.count]).length + seed.count +
        seed.cellRight + seed.cellLeft + seed.cellBlank + 1 ≤
        (encodeAffineRuntimeStackStandaloneInvocation seed).length := by
    simp [encodeAffineRuntimeStackStandaloneInvocation,
      encodeAffineRuntimeStackSourceInvocation, encodeUnaryFrame_length]
    omega
  exact hsource.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left hlength 2))

/-! ## Fixed finite family of self-contained stack sources -/

/-- Concatenated source invocations for a runtime stack-seed family. -/
def encodeAffineRuntimeStackStandaloneInvocationFamily :
    List AffineRuntimeStackSourceSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      encodeAffineRuntimeStackStandaloneInvocation seed ++
        encodeAffineRuntimeStackStandaloneInvocationFamily rest

/-- Stack frames obtained by pairing fixed blank strides with runtime seeds.
The exact-run theorem requires equal list lengths, so neither truncation case
is reachable in a successful invocation. -/
def affineRuntimeStackSourceFamilyFrames :
    List Nat → List AffineRuntimeStackSourceSeed → List AffineStackFrame
  | blankStep :: blankSteps, seed :: seeds =>
      affineRuntimeStackSourceFrame blankStep seed ::
        affineRuntimeStackSourceFamilyFrames blankSteps seeds
  | _, _ => []

/-- Pairwise mapping form of the fixed-stride/runtime-seed frame family. -/
theorem affineRuntimeStackSourceFamilyFrames_map
    {index : Type} (indices : List index)
    (blankStep : index → Nat)
    (seed : index → AffineRuntimeStackSourceSeed) :
    affineRuntimeStackSourceFamilyFrames
        (indices.map blankStep) (indices.map seed) =
      indices.map fun i =>
        affineRuntimeStackSourceFrame (blankStep i) (seed i) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp [affineRuntimeStackSourceFamilyFrames, ih]

/-- Empty-family control writes the outer stack-family terminator. -/
inductive AffineRuntimeStackEmptyFamilyLabel
  | emitEnd | finish
deriving DecidableEq, Fintype

/-- Nested finite-control sum of the fixed per-stack programs. -/
abbrev AffineRuntimeStackFamilySourceLabel : List Nat → Type
  | [] => AffineRuntimeStackEmptyFamilyLabel
  | blankStep :: rest =>
      Sum (affineRuntimeStackStandaloneRevProgram blankStep).Label
        (AffineRuntimeStackFamilySourceLabel rest)

private instance affineRuntimeStackFamilySourceLabelDecidableEq
    (blankSteps : List Nat) :
    DecidableEq (AffineRuntimeStackFamilySourceLabel blankSteps) := by
  induction blankSteps with
  | nil =>
      simp only [AffineRuntimeStackFamilySourceLabel]
      infer_instance
  | cons blankStep rest ih =>
      simp only [AffineRuntimeStackFamilySourceLabel]
      letI := ih
      letI := (affineRuntimeStackStandaloneRevProgram blankStep).labelDecidableEq
      infer_instance

private instance affineRuntimeStackFamilySourceLabelFintype
    (blankSteps : List Nat) :
    Fintype (AffineRuntimeStackFamilySourceLabel blankSteps) := by
  induction blankSteps with
  | nil =>
      simp only [AffineRuntimeStackFamilySourceLabel]
      infer_instance
  | cons blankStep rest ih =>
      simp only [AffineRuntimeStackFamilySourceLabel]
      letI := ih
      letI := (affineRuntimeStackStandaloneRevProgram blankStep).labelFintype
      infer_instance

private def affineRuntimeStackFamilySourceMain :
    (blankSteps : List Nat) → AffineRuntimeStackFamilySourceLabel blankSteps
  | [] => .emitEnd
  | blankStep :: _ =>
      .inl (affineRuntimeStackStandaloneRevProgram blankStep).main

private def affineRuntimeStackFamilySourceOp :
    (blankSteps : List Nat) →
      AffineRuntimeStackFamilySourceLabel blankSteps →
        Op UnaryFrameSym UnaryFrameSym
          (AffineRuntimeStackFamilySourceLabel blankSteps)
  | [], .emitEnd => .pushOutput .frameEnd .finish
  | [], .finish => .halt
  | _blankStep :: rest, .inl .finish =>
      .jump (.inr (affineRuntimeStackFamilySourceMain rest))
  | blankStep :: _, .inl label =>
      standaloneStackRelabelOp .inl
        ((affineRuntimeStackStandaloneRevProgram blankStep).op label)
  | _ :: rest, .inr label =>
      standaloneStackRelabelOp .inr
        (affineRuntimeStackFamilySourceOp rest label)

/-- Fixed finite-control assembly of all runtime stack sources. -/
abbrev affineRuntimeStackFamilySourceRevProgram
    (blankSteps : List Nat) : Program UnaryFrameSym UnaryFrameSym where
  Label := AffineRuntimeStackFamilySourceLabel blankSteps
  main := affineRuntimeStackFamilySourceMain blankSteps
  op := affineRuntimeStackFamilySourceOp blankSteps

/-- Public terminal label nested through the fixed stack list. -/
def affineRuntimeStackFamilySourceFinishLabel :
    (blankSteps : List Nat) →
      (affineRuntimeStackFamilySourceRevProgram blankSteps).Label
  | [] => .finish
  | _ :: rest => .inr (affineRuntimeStackFamilySourceFinishLabel rest)

@[simp] theorem affineRuntimeStackFamilySource_op_finish
    (blankSteps : List Nat) :
    (affineRuntimeStackFamilySourceRevProgram blankSteps).op
        (affineRuntimeStackFamilySourceFinishLabel blankSteps) = .halt := by
  induction blankSteps with
  | nil => rfl
  | cons blankStep rest ih =>
      change affineRuntimeStackFamilySourceOp rest
        (affineRuntimeStackFamilySourceFinishLabel rest) = .halt at ih
      simp [affineRuntimeStackFamilySourceRevProgram,
        affineRuntimeStackFamilySourceFinishLabel,
        affineRuntimeStackFamilySourceOp, standaloneStackRelabelOp, ih]

private def affineRuntimeStackFamilySourceCfg {blankSteps : List Nat}
    (label : (affineRuntimeStackFamilySourceRevProgram blankSteps).Label)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineRuntimeStackFamilySourceRevProgram blankSteps) where
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

/-- Clean entry for the complete fixed stack family. -/
def affineRuntimeStackFamilySourceLoopCfg (blankSteps : List Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineRuntimeStackFamilySourceRevProgram blankSteps) :=
  affineRuntimeStackFamilySourceCfg
    (affineRuntimeStackFamilySourceRevProgram blankSteps).main
    none none false input output [] [] [] [] []

/-- Clean continuation after the outer family terminator has been written. -/
def affineRuntimeStackFamilySourceFinishCfg (blankSteps : List Nat)
    (tail output : List UnaryFrameSym) :
    BuilderCfg (affineRuntimeStackFamilySourceRevProgram blankSteps) :=
  affineRuntimeStackFamilySourceCfg
    (affineRuntimeStackFamilySourceFinishLabel blankSteps)
    none none false tail output [] [] [] [] []

private def affineRuntimeStackFamilySourceRelabelCfg
    {blankStep : Nat} {rest : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label →
      (affineRuntimeStackFamilySourceRevProgram
        (blankStep :: rest)).Label)
    (c : BuilderCfg P) :
    BuilderCfg (affineRuntimeStackFamilySourceRevProgram
      (blankStep :: rest)) where
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

private def liftAffineRuntimeStackFamilySourceHeadCfg
    {blankStep : Nat} {rest : List Nat}
    (c : BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep)) :
    BuilderCfg (affineRuntimeStackFamilySourceRevProgram
      (blankStep :: rest)) :=
  affineRuntimeStackFamilySourceRelabelCfg .inl c

private def liftAffineRuntimeStackFamilySourceTailCfg
    {blankStep : Nat} {rest : List Nat}
    (c : BuilderCfg (affineRuntimeStackFamilySourceRevProgram rest)) :
    BuilderCfg (affineRuntimeStackFamilySourceRevProgram
      (blankStep :: rest)) :=
  affineRuntimeStackFamilySourceRelabelCfg .inr c

private theorem affineRuntimeStackFamilySourceRelabel_stepOp
    {blankStep : Nat} {rest : List Nat}
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tag : P.Label →
      (affineRuntimeStackFamilySourceRevProgram
        (blankStep :: rest)).Label)
    (op : Op UnaryFrameSym UnaryFrameSym P.Label) (c : BuilderCfg P) :
    stepOp (standaloneStackRelabelOp tag op)
        (affineRuntimeStackFamilySourceRelabelCfg tag c) =
      affineRuntimeStackFamilySourceRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [standaloneStackRelabelOp,
      affineRuntimeStackFamilySourceRelabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineRuntimeStackFamilySource_op_head
    {blankStep : Nat} {rest : List Nat}
    (label : (affineRuntimeStackStandaloneRevProgram blankStep).Label)
    (hexit : label ≠ .finish) :
    affineRuntimeStackFamilySourceOp (blankStep :: rest) (.inl label) =
      standaloneStackRelabelOp .inl
        ((affineRuntimeStackStandaloneRevProgram blankStep).op label) := by
  cases label <;>
    simp_all [affineRuntimeStackFamilySourceOp]

private theorem affineRuntimeStackFamilySource_op_tail
    {blankStep : Nat} {rest : List Nat}
    (label : (affineRuntimeStackFamilySourceRevProgram rest).Label) :
    affineRuntimeStackFamilySourceOp (blankStep :: rest) (.inr label) =
      standaloneStackRelabelOp .inr
        (affineRuntimeStackFamilySourceOp rest label) := by
  rfl

private theorem liftAffineRuntimeStackFamilySourceHead_step
    {blankStep : Nat} {rest : List Nat}
    (c : BuilderCfg (affineRuntimeStackStandaloneRevProgram blankStep))
    (hexit : c.label ≠ some .finish) :
    step (affineRuntimeStackFamilySourceRevProgram (blankStep :: rest))
        (liftAffineRuntimeStackFamilySourceHeadCfg c) =
      Option.map liftAffineRuntimeStackFamilySourceHeadCfg
        (step (affineRuntimeStackStandaloneRevProgram blankStep) c) := by
  unfold step
  rw [show (liftAffineRuntimeStackFamilySourceHeadCfg c).label =
      c.label.map .inl by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineRuntimeStackFamilySource_op_head label hlabelExit]
      exact congrArg some
        (affineRuntimeStackFamilySourceRelabel_stepOp .inl
          ((affineRuntimeStackStandaloneRevProgram blankStep).op label) c)

private theorem liftAffineRuntimeStackFamilySourceTail_step
    {blankStep : Nat} {rest : List Nat}
    (c : BuilderCfg (affineRuntimeStackFamilySourceRevProgram rest)) :
    step (affineRuntimeStackFamilySourceRevProgram (blankStep :: rest))
        (liftAffineRuntimeStackFamilySourceTailCfg c) =
      Option.map liftAffineRuntimeStackFamilySourceTailCfg
        (step (affineRuntimeStackFamilySourceRevProgram rest) c) := by
  unfold step
  rw [show (liftAffineRuntimeStackFamilySourceTailCfg c).label =
      c.label.map .inr by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      rw [affineRuntimeStackFamilySource_op_tail label]
      exact congrArg some
        (affineRuntimeStackFamilySourceRelabel_stepOp .inr
          (affineRuntimeStackFamilySourceOp rest label) c)

private theorem affineRuntimeStackFamilySource_iterate_bind_none
    {sigma : Type} (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem affineRuntimeStackFamilySource_haltExit_no_return
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
      rw [hnone, affineRuntimeStackFamilySource_iterate_bind_none]
      simp

private theorem affineRuntimeStackFamilySource_lift_iterations_to_haltExit
    {Q : Program UnaryFrameSym UnaryFrameSym} (exit : Q.Label)
    (hop : Q.op exit = .halt)
    {P : Program UnaryFrameSym UnaryFrameSym}
    (tr : BuilderCfg Q → BuilderCfg P)
    (hstep : ∀ c, c.label ≠ some exit →
      step P (tr c) = Option.map tr (step Q c))
    {a b : BuilderCfg Q} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step Q))^[n] (some a) = some b →
      (flip Option.bind (step P))^[n] (some (tr a)) = some (tr b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step Q))^[n] (step Q a) = some b at h
      change (flip Option.bind (step P))^[n] (step P (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact affineRuntimeStackFamilySource_haltExit_no_return
          exit hop a b ha hb n h
      cases hsource : step Q a with
      | none =>
          rw [hsource,
            affineRuntimeStackFamilySource_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem affineRuntimeStackFamilySource_lift_iterations
    {Q P : Program UnaryFrameSym UnaryFrameSym}
    (tr : BuilderCfg Q → BuilderCfg P)
    (hstep : ∀ c, step P (tr c) = Option.map tr (step Q c)) : ∀ n : Nat,
    {a b : BuilderCfg Q} →
    (flip Option.bind (step Q))^[n] (some a) = some b →
      (flip Option.bind (step P))^[n] (some (tr a)) = some (tr b) := by
  intro n
  induction n with
  | zero =>
      intro a b h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro a b h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step Q))^[n] (step Q a) = some b at h
      change (flip Option.bind (step P))^[n] (step P (tr a)) = some (tr b)
      rw [hstep]
      cases hsource : step Q a with
      | none =>
          rw [hsource,
            affineRuntimeStackFamilySource_iterate_bind_none] at h
          contradiction
      | some c =>
          simp only [Option.map_some]
          rw [hsource] at h
          exact ih h

private def affineRuntimeStackFamilySource_head_run
    {blankStep : Nat} {rest : List Nat}
    (seed : AffineRuntimeStackSourceSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineRuntimeStackFamilySourceRevProgram (blankStep :: rest)))
      (liftAffineRuntimeStackFamilySourceHeadCfg
        (affineRuntimeStackStandaloneLoopCfg blankStep
          (encodeAffineRuntimeStackStandaloneInvocation seed ++ tail) output))
      (some (liftAffineRuntimeStackFamilySourceHeadCfg
        (affineRuntimeStackStandaloneFinishCfg blankStep tail
          ((encodeAffineStackFrame
            (affineRuntimeStackSourceFrame blankStep seed)).reverse ++ output))))
      (affineRuntimeStackStandaloneSteps blankStep seed) := by
  have sourceRun := affineRuntimeStackStandalone_runToFinish blankStep seed
    tail output
  have htarget :
      (affineRuntimeStackStandaloneFinishCfg blankStep tail
        ((encodeAffineStackFrame
          (affineRuntimeStackSourceFrame blankStep seed)).reverse ++ output)
        ).label = some .finish := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineRuntimeStackFamilySource_lift_iterations_to_haltExit
    (AffineRuntimeStackStandaloneLabel.finish (blankStep := blankStep)) rfl
    liftAffineRuntimeStackFamilySourceHeadCfg
    liftAffineRuntimeStackFamilySourceHead_step htarget
    sourceRun.steps sourceRun.evals_in_steps

private def affineRuntimeStackFamilySource_tail_run
    {blankStep : Nat} {rest : List Nat}
    {a b : BuilderCfg (affineRuntimeStackFamilySourceRevProgram rest)}
    {steps : Nat}
    (sourceRun : EvalsToInTime
      (step (affineRuntimeStackFamilySourceRevProgram rest))
      a (some b) steps) :
    EvalsToInTime
      (step (affineRuntimeStackFamilySourceRevProgram (blankStep :: rest)))
      (liftAffineRuntimeStackFamilySourceTailCfg a)
      (some (liftAffineRuntimeStackFamilySourceTailCfg b)) steps := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineRuntimeStackFamilySource_lift_iterations
    liftAffineRuntimeStackFamilySourceTailCfg
    liftAffineRuntimeStackFamilySourceTail_step
    sourceRun.steps sourceRun.evals_in_steps

/-- Exact family runtime, including the outer `frameEnd`. -/
def affineRuntimeStackFamilySourceSteps :
    List Nat → List AffineRuntimeStackSourceSeed → Nat
  | blankStep :: blankSteps, seed :: seeds =>
      affineRuntimeStackStandaloneSteps blankStep seed + 1 +
        affineRuntimeStackFamilySourceSteps blankSteps seeds
  | _, _ => 1

/-- Fixed coefficient for the family-level quadratic bound. -/
def affineRuntimeStackFamilySourceStepCoeff : List Nat → Nat
  | [] => 1
  | blankStep :: rest =>
      101 * (blankStep + 1) +
        affineRuntimeStackFamilySourceStepCoeff rest

/-- The fixed family controller emits every stack encoding followed by the
outer family terminator, preserving the next invocation and returning clean. -/
def affineRuntimeStackFamilySource_runToFinish
    (blankSteps : List Nat) (seeds : List AffineRuntimeStackSourceSeed)
    (tail output : List UnaryFrameSym)
    (hlength : seeds.length = blankSteps.length) :
    EvalsToInTime
      (step (affineRuntimeStackFamilySourceRevProgram blankSteps))
      (affineRuntimeStackFamilySourceLoopCfg blankSteps
        (encodeAffineRuntimeStackStandaloneInvocationFamily seeds ++ tail)
        output)
      (some (affineRuntimeStackFamilySourceFinishCfg blankSteps tail
        ((encodeAffineStackFamily
          (affineRuntimeStackSourceFamilyFrames blankSteps seeds) ++
            [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (affineRuntimeStackFamilySourceSteps blankSteps seeds) := by
  induction blankSteps generalizing seeds output with
  | nil =>
      cases seeds with
      | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
      | cons seed seeds => simp at hlength
  | cons blankStep blankSteps ih =>
      cases seeds with
      | nil => simp at hlength
      | cons seed seeds =>
          have hrestLength : seeds.length = blankSteps.length := by
            simpa using hlength
          let restInput :=
            encodeAffineRuntimeStackStandaloneInvocationFamily seeds ++ tail
          let headOutput :=
            (encodeAffineStackFrame
              (affineRuntimeStackSourceFrame blankStep seed)).reverse ++ output
          let headStart := liftAffineRuntimeStackFamilySourceHeadCfg
            (rest := blankSteps)
            (affineRuntimeStackStandaloneLoopCfg blankStep
              (encodeAffineRuntimeStackStandaloneInvocation seed ++ restInput)
              output)
          let headDone := liftAffineRuntimeStackFamilySourceHeadCfg
            (rest := blankSteps)
            (affineRuntimeStackStandaloneFinishCfg blankStep restInput
              headOutput)
          let tailStart := liftAffineRuntimeStackFamilySourceTailCfg
            (blankStep := blankStep)
            (affineRuntimeStackFamilySourceLoopCfg blankSteps restInput
              headOutput)
          let tailDone := liftAffineRuntimeStackFamilySourceTailCfg
            (blankStep := blankStep)
            (affineRuntimeStackFamilySourceFinishCfg blankSteps tail
              ((encodeAffineStackFamily
                (affineRuntimeStackSourceFamilyFrames blankSteps seeds) ++
                  [UnaryFrameSym.frameEnd]).reverse ++ headOutput))
          have hhead : EvalsToInTime
              (step (affineRuntimeStackFamilySourceRevProgram
                (blankStep :: blankSteps)))
              headStart (some headDone)
              (affineRuntimeStackStandaloneSteps blankStep seed) := by
            simpa [headStart, headDone, restInput, headOutput] using
              affineRuntimeStackFamilySource_head_run
                (rest := blankSteps) seed restInput output
          have hbridge : EvalsToInTime
              (step (affineRuntimeStackFamilySourceRevProgram
                (blankStep :: blankSteps)))
              headDone (some tailStart) 1 := by
            refine ⟨⟨1, ?_⟩, le_rfl⟩
            rfl
          have htailSource := ih seeds headOutput hrestLength
          have htail : EvalsToInTime
              (step (affineRuntimeStackFamilySourceRevProgram
                (blankStep :: blankSteps)))
              tailStart (some tailDone)
              (affineRuntimeStackFamilySourceSteps blankSteps seeds) := by
            simpa [tailStart, tailDone, restInput] using
              affineRuntimeStackFamilySource_tail_run
                (blankStep := blankStep) htailSource
          let h₁ := EvalsToInTime.trans
            (step (affineRuntimeStackFamilySourceRevProgram
              (blankStep :: blankSteps))) _ 1 _ headDone _ hhead hbridge
          let full := EvalsToInTime.trans
            (step (affineRuntimeStackFamilySourceRevProgram
              (blankStep :: blankSteps))) _ _ _ tailStart _ h₁ htail
          convert full using 1
          · simp [headStart, liftAffineRuntimeStackFamilySourceHeadCfg,
              affineRuntimeStackFamilySourceRelabelCfg,
              affineRuntimeStackStandaloneLoopCfg,
              affineRuntimeStackStandaloneCfg,
              affineRuntimeStackStandaloneRevProgram,
              affineRuntimeStackFamilySourceLoopCfg,
              affineRuntimeStackFamilySourceCfg,
              affineRuntimeStackFamilySourceMain,
              restInput,
              encodeAffineRuntimeStackStandaloneInvocationFamily,
              List.append_assoc]
          · simp [tailDone, liftAffineRuntimeStackFamilySourceTailCfg,
              affineRuntimeStackFamilySourceRelabelCfg,
              affineRuntimeStackFamilySourceFinishCfg,
              affineRuntimeStackFamilySourceCfg,
              affineRuntimeStackFamilySourceFinishLabel,
              affineRuntimeStackSourceFamilyFrames,
              encodeAffineStackFamily, headOutput,
              List.reverse_append, List.append_assoc]
          · simp [affineRuntimeStackFamilySourceSteps]
            omega

/-- The complete fixed family source is quadratic in its explicit seed-stream
length; all stack-dependent widths occur only in the fixed coefficient. -/
theorem affineRuntimeStackFamilySourceSteps_le
    (blankSteps : List Nat) (seeds : List AffineRuntimeStackSourceSeed)
    (hlength : seeds.length = blankSteps.length) :
    affineRuntimeStackFamilySourceSteps blankSteps seeds ≤
      affineRuntimeStackFamilySourceStepCoeff blankSteps *
        ((encodeAffineRuntimeStackStandaloneInvocationFamily seeds).length +
          1) ^ 2 := by
  induction blankSteps generalizing seeds with
  | nil =>
      cases seeds with
      | nil => simp [affineRuntimeStackFamilySourceSteps,
          affineRuntimeStackFamilySourceStepCoeff,
          encodeAffineRuntimeStackStandaloneInvocationFamily]
      | cons seed seeds => simp at hlength
  | cons blankStep blankSteps ih =>
      cases seeds with
      | nil => simp at hlength
      | cons seed seeds =>
          have hrestLength : seeds.length = blankSteps.length := by
            simpa using hlength
          let headLength :=
            (encodeAffineRuntimeStackStandaloneInvocation seed).length
          let tailLength :=
            (encodeAffineRuntimeStackStandaloneInvocationFamily seeds).length
          let measure := headLength + tailLength + 1
          have hmeasure : 1 ≤ measure := by simp [measure]
          have hheadLength : headLength ≤ measure := by
            dsimp only [measure]
            omega
          have htailLength : tailLength + 1 ≤ measure := by
            dsimp only [measure]
            omega
          have hheadSource :=
            affineRuntimeStackStandaloneSteps_le_encoding blankStep seed
          have hheadSquare := Nat.pow_le_pow_left hheadLength 2
          have hhead :
              affineRuntimeStackStandaloneSteps blankStep seed + 1 ≤
                101 * (blankStep + 1) * measure ^ 2 := by
            have hscaled := Nat.mul_le_mul_left
              (100 * (blankStep + 1)) hheadSquare
            have hone : 1 ≤ (blankStep + 1) * measure ^ 2 := by
              nlinarith
            calc
              affineRuntimeStackStandaloneSteps blankStep seed + 1 ≤
                  100 * (blankStep + 1) * measure ^ 2 +
                    (blankStep + 1) * measure ^ 2 :=
                Nat.add_le_add (hheadSource.trans hscaled) hone
              _ = 101 * (blankStep + 1) * measure ^ 2 := by ring
          have htailSource := ih seeds hrestLength
          have htailSquare := Nat.pow_le_pow_left htailLength 2
          have htail :
              affineRuntimeStackFamilySourceSteps blankSteps seeds ≤
                affineRuntimeStackFamilySourceStepCoeff blankSteps *
                  measure ^ 2 :=
            htailSource.trans (Nat.mul_le_mul_left _ htailSquare)
          calc
            affineRuntimeStackFamilySourceSteps
                (blankStep :: blankSteps) (seed :: seeds) =
                (affineRuntimeStackStandaloneSteps blankStep seed + 1) +
                  affineRuntimeStackFamilySourceSteps blankSteps seeds := by
              rfl
            _ ≤ 101 * (blankStep + 1) * measure ^ 2 +
                  affineRuntimeStackFamilySourceStepCoeff blankSteps *
                    measure ^ 2 := Nat.add_le_add hhead htail
            _ = affineRuntimeStackFamilySourceStepCoeff
                  (blankStep :: blankSteps) * measure ^ 2 := by
              simp [affineRuntimeStackFamilySourceStepCoeff]
              ring
            _ = affineRuntimeStackFamilySourceStepCoeff
                  (blankStep :: blankSteps) *
                ((encodeAffineRuntimeStackStandaloneInvocationFamily
                  (seed :: seeds)).length + 1) ^ 2 := by
              simp [measure, headLength, tailLength,
                encodeAffineRuntimeStackStandaloneInvocationFamily]

end CLRS.Chapter34.Turing.PolyBuilder
