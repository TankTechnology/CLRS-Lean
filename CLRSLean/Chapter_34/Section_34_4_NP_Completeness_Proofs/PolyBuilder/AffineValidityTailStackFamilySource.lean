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

end CLRS.Chapter34.Turing.PolyBuilder
