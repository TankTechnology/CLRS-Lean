import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Compact source frames for affine exactly-one row families

An affine exactly-one invocation is determined by three runtime values:
`(start, sourceBase, count)`.  Its established consumer uses a four-field
wire format whose second field is the redundant value `start + 2`.  This
module gives a fixed TM2 that expands an arbitrary family of compact triples
to that exact canonical four-field input.  The expansion is independent of
the verifier and is reused by the Cook--Levin validity-row source compiler.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Three independent fields supplied by the row-major source controller. -/
def encodeAffineExactlyOneCompactFrame
    (frame : AffineExactlyOneFrame) : List UnaryFrameSym :=
  encodeUnaryFrame [frame.start, frame.rowBase, frame.count]

/-- Concatenated compact frames, with no extra sentinel. -/
def encodeAffineExactlyOneCompactFamily :
    List AffineExactlyOneFrame → List UnaryFrameSym
  | [] => []
  | frame :: rest =>
      encodeAffineExactlyOneCompactFrame frame ++
        encodeAffineExactlyOneCompactFamily rest

/-- Finite-control phases of the compact-to-canonical expander. -/
inductive AffineExactlyOneFrameExpandLabel
  | loader (label : UnaryTripleLoaderLabel)
  | pushCountSeparator | emitCount | pushCountTick
  | pushBaseSeparator | emitBase | pushBaseTick
  | pushExpandedStartSeparator | pushOffset₁ | pushOffset₂
  | emitStartCopy | saveStart | pushExpandedStartTick
  | pushStartSeparator | restoreStart | restoreStartInc
  | emitStart | pushStartTick | nextFrame
deriving DecidableEq, Fintype

/-- Relabel an operation into the expander's loader phase. -/
def relabelLoaderOp {Λ : Type} (tag : Λ →
    AffineExactlyOneFrameExpandLabel) :
    Op UnaryFrameSym UnaryFrameSym Λ →
      Op UnaryFrameSym UnaryFrameSym AffineExactlyOneFrameExpandLabel
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

/-- The fixed reverse-output expander.  The embedded loader places
`(start, sourceBase, count)` in the three unary counters. -/
def affineExactlyOneFrameExpandRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneFrameExpandLabel
  main := .loader (unaryTripleLoaderProgramFor UnaryFrameSym).main
  op
    | .loader .ready => .jump .emitStartCopy
    | .loader label => relabelLoaderOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label)
    | .pushCountSeparator => .pushOutput .separator .nextFrame
    | .emitCount => .dec₃ .pushCountSeparator .pushCountTick
    | .pushCountTick => .pushOutput .tick .emitCount
    | .pushBaseSeparator => .pushOutput .separator .emitCount
    | .emitBase => .dec₂ .pushBaseSeparator .pushBaseTick
    | .pushBaseTick => .pushOutput .tick .emitBase
    | .pushExpandedStartSeparator =>
        .pushOutput .separator .emitBase
    | .pushOffset₁ => .pushOutput .tick .pushOffset₂
    | .pushOffset₂ => .pushOutput .tick .pushExpandedStartSeparator
    | .emitStartCopy => .dec₁ .pushStartSeparator .saveStart
    | .saveStart => .pushWork₁ .tick .pushExpandedStartTick
    | .pushExpandedStartTick => .pushOutput .tick .emitStartCopy
    | .pushStartSeparator => .pushOutput .separator .restoreStart
    | .restoreStart => .popWork₁ .emitStart fun
        | .tick => .restoreStartInc
        | _ => .emitStart
    | .restoreStartInc => .inc₁ .restoreStart
    | .emitStart => .dec₁ .pushOffset₁ .pushStartTick
    | .pushStartTick => .pushOutput .tick .emitStart
    | .nextFrame => .jump (.loader .load₁)

/-- Fieldwise embedding of a loader configuration. -/
private def liftLoaderCfg
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    BuilderCfg affineExactlyOneFrameExpandRevProgram where
  label := c.label.map .loader
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

/-- Public clean entry at the next compact frame. -/
def affineExactlyOneFrameExpandLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneFrameExpandRevProgram :=
  liftLoaderCfg (unaryTripleLoaderCfgFor .load₁ none input output
    [] [] [] [] [])

private theorem relabelLoader_stepOp
    (op : Op UnaryFrameSym UnaryFrameSym UnaryTripleLoaderLabel)
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    stepOp (relabelLoaderOp .loader op) (liftLoaderCfg c) =
      liftLoaderCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [relabelLoaderOp, liftLoaderCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneFrameExpand_op_loader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineExactlyOneFrameExpandRevProgram.op (.loader label) =
      relabelLoaderOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) := by
  cases label <;>
    simp_all [affineExactlyOneFrameExpandRevProgram]

private theorem liftLoader_step
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym))
    (hexit : c.label ≠ some .ready) :
    step affineExactlyOneFrameExpandRevProgram (liftLoaderCfg c) =
      Option.map liftLoaderCfg
        (step (unaryTripleLoaderProgramFor UnaryFrameSym) c) := by
  unfold step
  rw [show (liftLoaderCfg c).label = c.label.map .loader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneFrameExpand_op_loader label hlabelExit]
      exact congrArg some
        (relabelLoader_stepOp
          ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) c)

/-- Once an option-valued transition returns `none`, later Kleisli iterations
remain `none`. -/
theorem iterate_bind_none {σ : Type} (f : σ → Option σ)
    (n : Nat) :
    (flip Option.bind f)^[n] (none : Option σ) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem loader_ready_no_return
    (a b : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym))
    (ha : a.label = some .ready) (hb : b.label = some .ready)
    (n : Nat) :
    (flip Option.bind
      (step (unaryTripleLoaderProgramFor UnaryFrameSym)))^[n]
        (step (unaryTripleLoaderProgramFor UnaryFrameSym) a) ≠ some b := by
  rcases a with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at ha
  subst label
  let halted : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym) :=
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
  have hstep : step (unaryTripleLoaderProgramFor UnaryFrameSym)
      { label := some .ready, buffer₁ := buffer₁, buffer₂ := buffer₂,
        test := test, input := input, output := output, work₁ := work₁,
        work₂ := work₂, counter₁ := counter₁, counter₂ := counter₂,
        counter₃ := counter₃ } = some halted := by
    simp [step, unaryTripleLoaderProgramFor, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind
        (step (unaryTripleLoaderProgramFor UnaryFrameSym)))^[n]
          (step (unaryTripleLoaderProgramFor UnaryFrameSym) halted) ≠ some b
      have hnone : step (unaryTripleLoaderProgramFor UnaryFrameSym) halted =
          none := rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem liftLoader_iterations_to_ready
    {a b : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)}
    (hb : b.label = some .ready) : ∀ n : Nat,
    (flip Option.bind
      (step (unaryTripleLoaderProgramFor UnaryFrameSym)))^[n]
        (some a) = some b →
      (flip Option.bind
        (step affineExactlyOneFrameExpandRevProgram))^[n]
          (some (liftLoaderCfg a)) = some (liftLoaderCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind
        (step (unaryTripleLoaderProgramFor UnaryFrameSym)))^[n]
          (step (unaryTripleLoaderProgramFor UnaryFrameSym) a) = some b at h
      change (flip Option.bind
        (step affineExactlyOneFrameExpandRevProgram))^[n]
          (step affineExactlyOneFrameExpandRevProgram (liftLoaderCfg a)) =
            some (liftLoaderCfg b)
      have haexit : a.label ≠ some .ready := by
        intro ha
        exact loader_ready_no_return a b ha hb n h
      cases hsource : step (unaryTripleLoaderProgramFor UnaryFrameSym) a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftLoader_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def frameExpandCfg
    (label : AffineExactlyOneFrameExpandLabel)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineExactlyOneFrameExpandRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := []
  counter₁ := first
  counter₂ := second
  counter₃ := third

private theorem frame_replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem emitStartCopy_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (second third : List Unit) :
    (flip Option.bind
      (step affineExactlyOneFrameExpandRevProgram))^[3 * value + 1]
        (some (frameExpandCfg .emitStartCopy buffer₁ test input output work₁
          (List.replicate value ()) second third)) =
      some (frameExpandCfg .pushStartSeparator buffer₁ false input
        (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) [] second third) := by
  induction value generalizing test output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneFrameExpandRevProgram))^[3 * value + 1]
            (some (frameExpandCfg .emitStartCopy buffer₁ true input
              (.tick :: output) (.tick :: work₁)
              (List.replicate value ()) second third)) = _
      simpa only [List.replicate_succ, frame_replicate_append_cons,
        List.cons_append] using
          ih true (.tick :: output) (.tick :: work₁)

private theorem restoreStart_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (current second third : List Unit) :
    (flip Option.bind
      (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
        (some (frameExpandCfg .restoreStart buffer₁ test input output
          (List.replicate value .tick)
          current second third)) =
      some (frameExpandCfg .emitStart none test input output []
        (List.replicate value () ++ current) second third) := by
  induction value generalizing buffer₁ current with
  | zero =>
      change step affineExactlyOneFrameExpandRevProgram
        (frameExpandCfg .restoreStart buffer₁ test input output []
          current second third) =
        some (frameExpandCfg .emitStart none test input output []
          current second third)
      rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
            (some (frameExpandCfg .restoreStart (some .tick) test input
              output (List.replicate value .tick)
              (() :: current) second third)) = _
      simpa only [List.replicate_succ, frame_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem emitStart_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (second third : List Unit) :
    (flip Option.bind
      (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
        (some (frameExpandCfg .emitStart buffer₁ test input output work₁
          (List.replicate value ()) second third)) =
      some (frameExpandCfg .pushOffset₁ buffer₁ false input
        (List.replicate value .tick ++ output) work₁ [] second third) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
            (some (frameExpandCfg .emitStart buffer₁ true input
              (.tick :: output) work₁ (List.replicate value ())
              second third)) = _
      simpa only [List.replicate_succ, frame_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output)

private theorem emitBase_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (first third : List Unit) :
    (flip Option.bind
      (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
        (some (frameExpandCfg .emitBase buffer₁ test input output work₁
          first (List.replicate value ()) third)) =
      some (frameExpandCfg .pushBaseSeparator buffer₁ false input
        (List.replicate value .tick ++ output) work₁ first [] third) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
            (some (frameExpandCfg .emitBase buffer₁ true input
              (.tick :: output) work₁ first (List.replicate value ())
              third)) = _
      simpa only [List.replicate_succ, frame_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output)

private theorem emitCount_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (first second : List Unit) :
    (flip Option.bind
      (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
        (some (frameExpandCfg .emitCount buffer₁ test input output work₁
          first second (List.replicate value ()))) =
      some (frameExpandCfg .pushCountSeparator buffer₁ false input
        (List.replicate value .tick ++ output) work₁ first second []) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneFrameExpandRevProgram))^[2 * value + 1]
            (some (frameExpandCfg .emitCount buffer₁ true input
              (.tick :: output) work₁ first second
              (List.replicate value ()))) = _
      simpa only [List.replicate_succ, frame_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output)

/-- Exact cost of loading and expanding one compact frame. -/
def affineExactlyOneFrameExpandOneSteps
    (frame : AffineExactlyOneFrame) : Nat :=
  unaryTripleLoaderSteps frame.start frame.rowBase frame.count +
    (7 * frame.start + 2 * frame.rowBase + 2 * frame.count + 13)

private def affineExactlyOneFrameExpand_one
    (frame : AffineExactlyOneFrame) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneFrameExpandRevProgram)
      (affineExactlyOneFrameExpandLoopCfg
        (encodeAffineExactlyOneCompactFrame frame ++ tail) output)
      (some (affineExactlyOneFrameExpandLoopCfg tail
        ((encodeAffineExactlyOneFrame frame).reverse ++ output)))
      (affineExactlyOneFrameExpandOneSteps frame) := by
  let first := List.replicate frame.start ()
  let second := List.replicate frame.rowBase ()
  let third := List.replicate frame.count ()
  let loaderReady := liftLoaderCfg
    (unaryTripleLoaderReadyCfgFor frame.start frame.rowBase frame.count
      tail output [] [])
  let startCopy := frameExpandCfg .emitStartCopy (some .separator) false
    tail output [] first second third
  let startSeparator := frameExpandCfg .pushStartSeparator
    (some .separator) false tail
    (List.replicate frame.start .tick ++ output)
    (List.replicate frame.start .tick) [] second third
  let restoreStart := frameExpandCfg .restoreStart (some .separator) false
    tail (.separator :: (List.replicate frame.start .tick ++ output))
    (List.replicate frame.start .tick) [] second third
  let emitStart := frameExpandCfg .emitStart none false tail
    (.separator :: (List.replicate frame.start .tick ++ output))
    [] first second third
  let offset₁ := frameExpandCfg .pushOffset₁ none false tail
    (List.replicate frame.start .tick ++
      .separator :: (List.replicate frame.start .tick ++ output))
    [] [] second third
  let offset₂ := frameExpandCfg .pushOffset₂ none false tail
    (.tick :: (List.replicate frame.start .tick ++
      .separator :: (List.replicate frame.start .tick ++ output)))
    [] [] second third
  let expandedSeparator := frameExpandCfg .pushExpandedStartSeparator none
    false tail
    (.tick :: .tick :: (List.replicate frame.start .tick ++
      .separator :: (List.replicate frame.start .tick ++ output)))
    [] [] second third
  let emitBase := frameExpandCfg .emitBase none false tail
    (.separator :: (.tick :: .tick ::
      (List.replicate frame.start .tick ++
        .separator :: (List.replicate frame.start .tick ++ output))))
    [] [] second third
  let baseSeparator := frameExpandCfg .pushBaseSeparator none false tail
    (List.replicate frame.rowBase .tick ++
      .separator :: (.tick :: .tick ::
        (List.replicate frame.start .tick ++
          .separator :: (List.replicate frame.start .tick ++ output))))
    [] [] [] third
  let emitCount := frameExpandCfg .emitCount none false tail
    (.separator :: (List.replicate frame.rowBase .tick ++
      .separator :: (.tick :: .tick ::
        (List.replicate frame.start .tick ++
          .separator :: (List.replicate frame.start .tick ++ output)))))
    [] [] [] third
  let countSeparator := frameExpandCfg .pushCountSeparator none false tail
    (List.replicate frame.count .tick ++
      .separator :: (List.replicate frame.rowBase .tick ++
        .separator :: (.tick :: .tick ::
          (List.replicate frame.start .tick ++
            .separator :: (List.replicate frame.start .tick ++ output)))))
    [] [] [] []
  let nextFrame := frameExpandCfg .nextFrame none false tail
    (.separator :: (List.replicate frame.count .tick ++
      .separator :: (List.replicate frame.rowBase .tick ++
        .separator :: (.tick :: .tick ::
          (List.replicate frame.start .tick ++
            .separator :: (List.replicate frame.start .tick ++ output))))))
    [] [] [] []
  have sourceRun := unaryTripleLoader_runFor
    frame.start frame.rowBase frame.count tail output [] []
  have htarget : (unaryTripleLoaderReadyCfgFor
      frame.start frame.rowBase frame.count tail output [] []).label =
        some .ready := rfl
  have hloader : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      (affineExactlyOneFrameExpandLoopCfg
        (encodeAffineExactlyOneCompactFrame frame ++ tail) output)
      (some loaderReady)
      (unaryTripleLoaderSteps frame.start frame.rowBase frame.count) := by
    refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
    have lifted := liftLoader_iterations_to_ready htarget sourceRun.steps
      sourceRun.evals_in_steps
    simpa [affineExactlyOneFrameExpandLoopCfg,
      encodeAffineExactlyOneCompactFrame, loaderReady] using lifted
  have hbridge : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      loaderReady (some startCopy) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hcopy : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      startCopy (some startSeparator) (3 * frame.start + 1) := by
    refine ⟨⟨3 * frame.start + 1, ?_⟩, le_rfl⟩
    simpa [startCopy, startSeparator, first, second, third] using
      emitStartCopy_eval frame.start (some .separator) false tail output []
        second third
  have hstartSeparator : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      startSeparator (some restoreStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hrestore : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      restoreStart (some emitStart) (2 * frame.start + 1) := by
    refine ⟨⟨2 * frame.start + 1, ?_⟩, le_rfl⟩
    simpa [restoreStart, emitStart, first, second, third] using
      restoreStart_eval frame.start (some .separator) false tail
        (.separator :: (List.replicate frame.start .tick ++ output))
        [] second third
  have hemitStart : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      emitStart (some offset₁) (2 * frame.start + 1) := by
    refine ⟨⟨2 * frame.start + 1, ?_⟩, le_rfl⟩
    simpa [emitStart, offset₁, first, second, third] using
      emitStart_eval frame.start none false tail
        (.separator :: (List.replicate frame.start .tick ++ output))
        [] second third
  have hoffset₁ : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      offset₁ (some offset₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hoffset₂ : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      offset₂ (some expandedSeparator) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hexpandedSeparator : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      expandedSeparator (some emitBase) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hemitBase : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      emitBase (some baseSeparator) (2 * frame.rowBase + 1) := by
    refine ⟨⟨2 * frame.rowBase + 1, ?_⟩, le_rfl⟩
    simpa [emitBase, baseSeparator, second, third] using
      emitBase_eval frame.rowBase none false tail
        (.separator :: (.tick :: .tick ::
          (List.replicate frame.start .tick ++
            .separator :: (List.replicate frame.start .tick ++ output))))
        [] [] third
  have hbaseSeparator : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      baseSeparator (some emitCount) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hemitCount : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      emitCount (some countSeparator) (2 * frame.count + 1) := by
    refine ⟨⟨2 * frame.count + 1, ?_⟩, le_rfl⟩
    simpa [emitCount, countSeparator, third] using
      emitCount_eval frame.count none false tail
        (.separator :: (List.replicate frame.rowBase .tick ++
          .separator :: (.tick :: .tick ::
            (List.replicate frame.start .tick ++
              .separator :: (List.replicate frame.start .tick ++ output)))))
        [] [] []
  have hcountSeparator : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      countSeparator (some nextFrame) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hnext : EvalsToInTime
      (step affineExactlyOneFrameExpandRevProgram)
      nextFrame
      (some (affineExactlyOneFrameExpandLoopCfg tail
        ((encodeAffineExactlyOneFrame frame).reverse ++ output))) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    have hoffset :
        UnaryFrameSym.tick :: UnaryFrameSym.tick ::
            List.replicate frame.start UnaryFrameSym.tick =
          List.replicate (frame.start + 2) UnaryFrameSym.tick := by
      rw [show frame.start + 2 = 2 + frame.start by omega,
        List.replicate_add]
      rfl
    have hoffsetAppend (suffix : List UnaryFrameSym) :
        UnaryFrameSym.tick :: UnaryFrameSym.tick ::
            (List.replicate frame.start UnaryFrameSym.tick ++ suffix) =
          List.replicate (frame.start + 2) UnaryFrameSym.tick ++ suffix := by
      simpa only [List.cons_append] using
        congrArg (fun xs => xs ++ suffix) hoffset
    simp only [nextFrame, affineExactlyOneFrameExpandLoopCfg,
      liftLoaderCfg, unaryTripleLoaderCfgFor, Function.iterate_one]
    change some (frameExpandCfg (.loader .load₁) none false tail
      (.separator :: (List.replicate frame.count .tick ++
        .separator :: (List.replicate frame.rowBase .tick ++
          .separator :: (.tick :: .tick ::
            (List.replicate frame.start .tick ++
              .separator :: (List.replicate frame.start .tick ++ output))))))
      [] [] [] []) = _
    rw [hoffsetAppend]
    simp [encodeAffineExactlyOneFrame, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.reverse_append, List.append_assoc]
    rfl
  let h₁ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ loaderReady _ hloader hbridge
  let h₂ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ startCopy _ h₁ hcopy
  let h₃ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ startSeparator _ h₂ hstartSeparator
  let h₄ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ restoreStart _ h₃ hrestore
  let h₅ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ emitStart _ h₄ hemitStart
  let h₆ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ offset₁ _ h₅ hoffset₁
  let h₇ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ offset₂ _ h₆ hoffset₂
  let h₈ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ expandedSeparator _ h₇ hexpandedSeparator
  let h₉ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ emitBase _ h₈ hemitBase
  let h₁₀ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ baseSeparator _ h₉ hbaseSeparator
  let h₁₁ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ emitCount _ h₁₀ hemitCount
  let h₁₂ := EvalsToInTime.trans (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ countSeparator _ h₁₁ hcountSeparator
  let full := EvalsToInTime.trans
    (step affineExactlyOneFrameExpandRevProgram)
    _ _ _ nextFrame _ h₁₂ hnext
  convert full using 1
  simp [affineExactlyOneFrameExpandOneSteps, unaryTripleLoaderSteps]
  omega

/-- Exact standalone cost for a compact frame family. -/
def affineExactlyOneFrameExpandRevSteps :
    List AffineExactlyOneFrame → Nat
  | [] => 2
  | frame :: rest =>
      affineExactlyOneFrameExpandOneSteps frame +
        affineExactlyOneFrameExpandRevSteps rest

private def affineExactlyOneFrameExpand_runFrom
    (frames : List AffineExactlyOneFrame) (output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneFrameExpandRevProgram)
      (affineExactlyOneFrameExpandLoopCfg
        (encodeAffineExactlyOneCompactFamily frames) output)
      (some (haltCfg affineExactlyOneFrameExpandRevProgram
        ((encodeAffineExactlyOneFamily frames).reverse ++ output)))
      (affineExactlyOneFrameExpandRevSteps frames) := by
  induction frames generalizing output with
  | nil =>
      refine ⟨⟨2, ?_⟩, le_rfl⟩
      rfl
  | cons frame rest ih =>
      let frameOutput :=
        (encodeAffineExactlyOneFrame frame).reverse ++ output
      have hfirst := affineExactlyOneFrameExpand_one frame
        (encodeAffineExactlyOneCompactFamily rest) output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans
        (step affineExactlyOneFrameExpandRevProgram)
        (affineExactlyOneFrameExpandOneSteps frame)
        (affineExactlyOneFrameExpandRevSteps rest)
        _ (affineExactlyOneFrameExpandLoopCfg
          (encodeAffineExactlyOneCompactFamily rest) frameOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineExactlyOneCompactFamily]
      · simp [encodeAffineExactlyOneFamily, frameOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneFrameExpandRevSteps]
        omega

/-- One fixed controller expands every compact frame in sequence and emits
the reverse of the canonical family byte stream. -/
def affineExactlyOneFrameExpandRev_run
    (frames : List AffineExactlyOneFrame) :
    EvalsToInTime (step affineExactlyOneFrameExpandRevProgram)
      (initialCfg affineExactlyOneFrameExpandRevProgram
        (encodeAffineExactlyOneCompactFamily frames))
      (some (haltCfg affineExactlyOneFrameExpandRevProgram
        (encodeAffineExactlyOneFamily frames).reverse))
      (affineExactlyOneFrameExpandRevSteps frames) := by
  have hinit : affineExactlyOneFrameExpandLoopCfg
      (encodeAffineExactlyOneCompactFamily frames) [] =
        initialCfg affineExactlyOneFrameExpandRevProgram
          (encodeAffineExactlyOneCompactFamily frames) := by
    rfl
  rw [← hinit]
  simpa only [List.append_nil] using
    affineExactlyOneFrameExpand_runFrom frames []

@[simp] theorem encodeAffineExactlyOneCompactFrame_length
    (frame : AffineExactlyOneFrame) :
    (encodeAffineExactlyOneCompactFrame frame).length =
      frame.start + frame.rowBase + frame.count + 3 := by
  simp [encodeAffineExactlyOneCompactFrame, encodeUnaryFrame_length]
  omega

/-- The expander is linear in its exact compact input length. -/
theorem affineExactlyOneFrameExpandRev_steps_le
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneFrameExpandRevSteps frames ≤
      9 * (encodeAffineExactlyOneCompactFamily frames).length + 2 := by
  induction frames with
  | nil => simp [affineExactlyOneFrameExpandRevSteps,
      encodeAffineExactlyOneCompactFamily]
  | cons frame rest ih =>
      have hone : affineExactlyOneFrameExpandOneSteps frame ≤
          9 * (encodeAffineExactlyOneCompactFrame frame).length := by
        simp [affineExactlyOneFrameExpandOneSteps, unaryTripleLoaderSteps,
          encodeAffineExactlyOneCompactFrame_length]
        omega
      simp only [affineExactlyOneFrameExpandRevSteps,
        encodeAffineExactlyOneCompactFamily, List.length_append]
      calc
        affineExactlyOneFrameExpandOneSteps frame +
              affineExactlyOneFrameExpandRevSteps rest ≤
            9 * (encodeAffineExactlyOneCompactFrame frame).length +
              (9 * (encodeAffineExactlyOneCompactFamily rest).length + 2) :=
          Nat.add_le_add hone ih
        _ = 9 * ((encodeAffineExactlyOneCompactFrame frame).length +
              (encodeAffineExactlyOneCompactFamily rest).length) + 2 := by
          ring

/-- The compiled expander computes the reversed canonical family encoding. -/
noncomputable def affineExactlyOneFrameExpandRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneCompactFamily id
      (fun frames : List AffineExactlyOneFrame =>
        (encodeAffineExactlyOneFamily frames).reverse) where
  tm := compile affineExactlyOneFrameExpandRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 9 * Polynomial.X + 2
  outputsFun := fun frames => by
    have builderRun := affineExactlyOneFrameExpandRev_run frames
    have compiledRun := compile_evalsToInTime
      affineExactlyOneFrameExpandRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneFrameExpandRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneFrameExpandRevProgram)
          (encodeAffineExactlyOneCompactFamily frames))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneFrameExpandRevProgram)
          (encodeAffineExactlyOneFamily frames).reverse))
        (affineExactlyOneFrameExpandRevSteps frames) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : affineExactlyOneFrameExpandRevSteps frames ≤
        (9 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneCompactFamily frames).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineExactlyOneFrameExpandRev_steps_le frames
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneFrameExpandRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneFrameExpandRevProgram)
          (encodeAffineExactlyOneCompactFamily frames))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneFrameExpandRevProgram)
          (encodeAffineExactlyOneFamily frames).reverse))
        ((9 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneCompactFamily frames).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the prepend output yields the exact forward four-field family. -/
noncomputable def affineExactlyOneFrameExpand_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneCompactFamily id
      encodeAffineExactlyOneFamily := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineExactlyOneFrameExpandRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

/-! ## Reusable affine progression source -/

/-- Interpret every row of a runtime triple progression as the three
independent fields of one exactly-one frame. -/
def affineExactlyOneFramesOfTripleProgression
    (progression : AffineUnaryTripleProgression) :
    List AffineExactlyOneFrame :=
  (affineUnaryTripleProgressionRows progression).map fun row =>
    { start := row.1
      rowBase := row.2.1
      count := row.2.2 }

private theorem encodeAffineExactlyOneCompactFamily_eq_flatMap
    (frames : List AffineExactlyOneFrame) :
    encodeAffineExactlyOneCompactFamily frames =
      frames.flatMap encodeAffineExactlyOneCompactFrame := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [encodeAffineExactlyOneCompactFamily, ih]

/-- The existing triple-progression controller already emits exactly the
compact input expected by the redundant-field expander. -/
theorem affineUnaryTripleProgressionFrameStream_eq_compactFamily
    (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFrameStream progression =
      encodeAffineExactlyOneCompactFamily
        (affineExactlyOneFramesOfTripleProgression progression) := by
  rw [encodeAffineExactlyOneCompactFamily_eq_flatMap]
  simp [affineUnaryTripleProgressionFrameStream,
    affineExactlyOneFramesOfTripleProgression, List.flatMap_map,
    affineUnaryTripleRowValues,
    encodeAffineExactlyOneCompactFrame]

set_option maxHeartbeats 2000000 in
/-- One fixed polynomial-time TM2 expands seven runtime progression
parameters directly to the canonical four-field exactly-one frame family. -/
noncomputable def
    affineExactlyOneTripleProgressionFamily_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgression id
      (fun progression => encodeAffineExactlyOneFamily
        (affineExactlyOneFramesOfTripleProgression progression)) := by
  have compactSource : _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgression
      encodeAffineExactlyOneCompactFamily
      affineExactlyOneFramesOfTripleProgression := by
    let source :=
      affineUnaryTripleProgressionFrameStream_computableInPolyTime
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun progression => by
          simpa only [affineUnaryTripleProgressionFrameStream_eq_compactFamily,
            id_eq]
            using source.outputsFun progression }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      compactSource affineExactlyOneFrameExpand_computableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

/-! ## Row-boundary-preserving canonical expansion -/

/-- Compact exactly-one rows separated by an explicit `frameEnd`. -/
def encodeAffineExactlyOneCompactMarkedFamily :
    List (List AffineExactlyOneFrame) → List UnaryFrameSym
  | [] => []
  | row :: rest =>
      encodeAffineExactlyOneCompactFamily row ++ .frameEnd ::
        encodeAffineExactlyOneCompactMarkedFamily rest

/-- Canonical four-field rows with the marker expected by the validity-row
family controller: one leading `tick` and one trailing `frameEnd` per row. -/
def encodeAffineExactlyOneTickedMarkedFamily :
    List (List AffineExactlyOneFrame) → List UnaryFrameSym
  | [] => []
  | row :: rest =>
      .tick :: (encodeAffineExactlyOneFamily row ++ .frameEnd ::
        encodeAffineExactlyOneTickedMarkedFamily rest)

/-- The base expander's pre-halt configuration after it consumes a row
boundary while looking for the next compact frame. -/
def affineExactlyOneFrameExpandInvalidCfg
    (tail output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneFrameExpandRevProgram :=
  liftLoaderCfg (unaryTripleLoaderCfgFor .invalid (some .frameEnd)
    tail output [] [] [] [] [])

/-- Exact cost through the consumed row boundary, stopping before the base
expander executes its standalone invalid-input halt. -/
def affineExactlyOneFrameExpandToInvalidSteps :
    List AffineExactlyOneFrame → Nat
  | [] => 1
  | frame :: rest =>
      affineExactlyOneFrameExpandOneSteps frame +
        affineExactlyOneFrameExpandToInvalidSteps rest

/-- Exact base-expander execution through one consumed row boundary.  This
clean continuation theorem is public so payload-preserving outer controllers
can reuse the verified one-hot kernel without duplicating it. -/
def affineExactlyOneFrameExpand_runToInvalid
    (frames : List AffineExactlyOneFrame) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneFrameExpandRevProgram)
      (affineExactlyOneFrameExpandLoopCfg
        (encodeAffineExactlyOneCompactFamily frames ++ .frameEnd :: tail)
        output)
      (some (affineExactlyOneFrameExpandInvalidCfg tail
        ((encodeAffineExactlyOneFamily frames).reverse ++ output)))
      (affineExactlyOneFrameExpandToInvalidSteps frames) := by
  induction frames generalizing output with
  | nil =>
      refine ⟨⟨1, ?_⟩, le_rfl⟩
      rfl
  | cons frame rest ih =>
      let restInput := encodeAffineExactlyOneCompactFamily rest ++
        .frameEnd :: tail
      let frameOutput :=
        (encodeAffineExactlyOneFrame frame).reverse ++ output
      have hfirst := affineExactlyOneFrameExpand_one frame restInput output
      have hrest := ih frameOutput
      let full := EvalsToInTime.trans
        (step affineExactlyOneFrameExpandRevProgram)
        (affineExactlyOneFrameExpandOneSteps frame)
        (affineExactlyOneFrameExpandToInvalidSteps rest)
        _ (affineExactlyOneFrameExpandLoopCfg restInput frameOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineExactlyOneCompactFamily, restInput,
          List.append_assoc]
      · simp [encodeAffineExactlyOneFamily, frameOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneFrameExpandToInvalidSteps]
        omega

/-- Outer dispatch, one leading row marker, and the unchanged base expander. -/
inductive AffineExactlyOneMarkedExpandLabel
  | check
  | save (symbol : UnaryFrameSym)
  | restore
  | clearBuffer
  | markRow
  | body (label : AffineExactlyOneFrameExpandLabel)
  | clearEnd
  | finish
deriving DecidableEq, Fintype

private def affineExactlyOneMarkedExpandRelabelOp :
    Op UnaryFrameSym UnaryFrameSym AffineExactlyOneFrameExpandLabel →
      Op UnaryFrameSym UnaryFrameSym AffineExactlyOneMarkedExpandLabel
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

/-- A fixed family wrapper.  It probes for end-of-input before each row,
restores the first compact symbol, emits the leading tick, and redirects the
base expander's invalid label after the consumed row terminator. -/
def affineExactlyOneMarkedExpandRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneMarkedExpandLabel
  main := .check
  op
    | .check => .popInput .finish .save
    | .save symbol => .pushWork₁ symbol .restore
    | .restore => .moveWork₁Input .finish (fun _ => .clearBuffer)
    | .clearBuffer => .popWork₁ .markRow (fun _ => .finish)
    | .markRow =>
        .pushOutput .tick (.body affineExactlyOneFrameExpandRevProgram.main)
    | .body (.loader .invalid) => .pushOutput .frameEnd .clearEnd
    | .body label => affineExactlyOneMarkedExpandRelabelOp
        (affineExactlyOneFrameExpandRevProgram.op label)
    | .clearEnd => .popWork₁ .check (fun _ => .check)
    | .finish => .halt

private def affineExactlyOneMarkedExpandCfg
    (label : AffineExactlyOneMarkedExpandLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineExactlyOneMarkedExpandRevProgram where
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

/-- Clean family loop header. -/
def affineExactlyOneMarkedExpandLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneMarkedExpandRevProgram :=
  affineExactlyOneMarkedExpandCfg .check none none false input output
    [] [] [] [] []

private def liftAffineExactlyOneMarkedExpandBodyCfg
    (c : BuilderCfg affineExactlyOneFrameExpandRevProgram) :
    BuilderCfg affineExactlyOneMarkedExpandRevProgram where
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

private theorem affineExactlyOneMarkedExpandRelabel_stepOp
    (op : Op UnaryFrameSym UnaryFrameSym
      AffineExactlyOneFrameExpandLabel)
    (c : BuilderCfg affineExactlyOneFrameExpandRevProgram) :
    stepOp (affineExactlyOneMarkedExpandRelabelOp op)
        (liftAffineExactlyOneMarkedExpandBodyCfg c) =
      liftAffineExactlyOneMarkedExpandBodyCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [affineExactlyOneMarkedExpandRelabelOp,
      liftAffineExactlyOneMarkedExpandBodyCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneMarkedExpand_op_body
    (label : AffineExactlyOneFrameExpandLabel)
    (hexit : label ≠ .loader .invalid) :
    affineExactlyOneMarkedExpandRevProgram.op (.body label) =
      affineExactlyOneMarkedExpandRelabelOp
        (affineExactlyOneFrameExpandRevProgram.op label) := by
  cases label <;>
    simp_all [affineExactlyOneMarkedExpandRevProgram]

private theorem liftAffineExactlyOneMarkedExpandBody_step
    (c : BuilderCfg affineExactlyOneFrameExpandRevProgram)
    (hexit : c.label ≠ some (.loader .invalid)) :
    step affineExactlyOneMarkedExpandRevProgram
        (liftAffineExactlyOneMarkedExpandBodyCfg c) =
      Option.map liftAffineExactlyOneMarkedExpandBodyCfg
        (step affineExactlyOneFrameExpandRevProgram c) := by
  unfold step
  rw [show (liftAffineExactlyOneMarkedExpandBodyCfg c).label =
      c.label.map .body by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .loader .invalid := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneMarkedExpand_op_body label hlabelExit]
      exact congrArg some
        (affineExactlyOneMarkedExpandRelabel_stepOp
          (affineExactlyOneFrameExpandRevProgram.op label) c)

private theorem affineExactlyOneMarkedExpand_haltExit_no_return
    (a b : BuilderCfg affineExactlyOneFrameExpandRevProgram)
    (ha : a.label = some (.loader .invalid))
    (hb : b.label = some (.loader .invalid)) (n : Nat) :
    (flip Option.bind (step affineExactlyOneFrameExpandRevProgram))^[n]
        (step affineExactlyOneFrameExpandRevProgram a) ≠ some b := by
  rcases a with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at ha
  subst label
  let halted : BuilderCfg affineExactlyOneFrameExpandRevProgram :=
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
  have hstep : step affineExactlyOneFrameExpandRevProgram
      { label := some (.loader .invalid), buffer₁ := buffer₁,
        buffer₂ := buffer₂, test := test, input := input,
        output := output, work₁ := work₁, work₂ := work₂,
        counter₁ := counter₁, counter₂ := counter₂,
        counter₃ := counter₃ } = some halted := by
    simp [step, affineExactlyOneFrameExpandRevProgram,
      unaryTripleLoaderProgramFor, relabelLoaderOp, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind
        (step affineExactlyOneFrameExpandRevProgram))^[n]
          (step affineExactlyOneFrameExpandRevProgram halted) ≠ some b
      have hnone : step affineExactlyOneFrameExpandRevProgram halted = none :=
        rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem affineExactlyOneMarkedExpand_lift_iterations_to_invalid
    {a b : BuilderCfg affineExactlyOneFrameExpandRevProgram}
    (hb : b.label = some (.loader .invalid)) : ∀ n : Nat,
    (flip Option.bind (step affineExactlyOneFrameExpandRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind (step affineExactlyOneMarkedExpandRevProgram))^[n]
        (some (liftAffineExactlyOneMarkedExpandBodyCfg a)) =
          some (liftAffineExactlyOneMarkedExpandBodyCfg b) := by
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
        (step affineExactlyOneFrameExpandRevProgram))^[n]
          (step affineExactlyOneFrameExpandRevProgram a) = some b at h
      change (flip Option.bind
        (step affineExactlyOneMarkedExpandRevProgram))^[n]
          (step affineExactlyOneMarkedExpandRevProgram
            (liftAffineExactlyOneMarkedExpandBodyCfg a)) =
              some (liftAffineExactlyOneMarkedExpandBodyCfg b)
      have haexit : a.label ≠ some (.loader .invalid) := by
        intro ha
        exact affineExactlyOneMarkedExpand_haltExit_no_return
          a b ha hb n h
      cases hsource : step affineExactlyOneFrameExpandRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftAffineExactlyOneMarkedExpandBody_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineExactlyOneMarkedExpand_dispatch_run
    (input output : List UnaryFrameSym) (hinput : input ≠ []) :
    EvalsToInTime (step affineExactlyOneMarkedExpandRevProgram)
      (affineExactlyOneMarkedExpandLoopCfg input output)
      (some (liftAffineExactlyOneMarkedExpandBodyCfg
        (affineExactlyOneFrameExpandLoopCfg input (.tick :: output)))) 5 := by
  cases input with
  | nil => contradiction
  | cons symbol rest => exact ⟨⟨5, rfl⟩, le_rfl⟩

private def affineExactlyOneMarkedExpand_body_run
    (frames : List AffineExactlyOneFrame) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedExpandRevProgram)
      (liftAffineExactlyOneMarkedExpandBodyCfg
        (affineExactlyOneFrameExpandLoopCfg
          (encodeAffineExactlyOneCompactFamily frames ++ .frameEnd :: tail)
          output))
      (some (liftAffineExactlyOneMarkedExpandBodyCfg
        (affineExactlyOneFrameExpandInvalidCfg tail
          ((encodeAffineExactlyOneFamily frames).reverse ++ output))))
      (affineExactlyOneFrameExpandToInvalidSteps frames) := by
  have sourceRun := affineExactlyOneFrameExpand_runToInvalid
    frames tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineExactlyOneMarkedExpand_lift_iterations_to_invalid rfl
    sourceRun.steps sourceRun.evals_in_steps

/-- Exact family cost including the final empty dispatch and halt. -/
def affineExactlyOneMarkedExpandSteps :
    List (List AffineExactlyOneFrame) → Nat
  | [] => 2
  | row :: rest =>
      5 + affineExactlyOneFrameExpandToInvalidSteps row + 2 +
        affineExactlyOneMarkedExpandSteps rest

/-- Exact row-family execution with leading and trailing row markers. -/
def affineExactlyOneMarkedExpand_runFrom
    (rows : List (List AffineExactlyOneFrame))
    (output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedExpandRevProgram)
      (affineExactlyOneMarkedExpandLoopCfg
        (encodeAffineExactlyOneCompactMarkedFamily rows) output)
      (some (haltCfg affineExactlyOneMarkedExpandRevProgram
        ((encodeAffineExactlyOneTickedMarkedFamily rows).reverse ++ output)))
      (affineExactlyOneMarkedExpandSteps rows) := by
  induction rows generalizing output with
  | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | cons row rest ih =>
      let restInput := encodeAffineExactlyOneCompactMarkedFamily rest
      let markedOutput := .frameEnd ::
        (encodeAffineExactlyOneFamily row).reverse ++ .tick :: output
      let bodyStart := liftAffineExactlyOneMarkedExpandBodyCfg
        (affineExactlyOneFrameExpandLoopCfg
          (encodeAffineExactlyOneCompactFamily row ++
            .frameEnd :: restInput) (.tick :: output))
      let bodyDone := liftAffineExactlyOneMarkedExpandBodyCfg
        (affineExactlyOneFrameExpandInvalidCfg restInput
          ((encodeAffineExactlyOneFamily row).reverse ++ .tick :: output))
      let restStart := affineExactlyOneMarkedExpandLoopCfg
        restInput markedOutput
      have hinvocation :
          encodeAffineExactlyOneCompactFamily row ++
              .frameEnd :: restInput ≠ [] := by simp
      have hdispatch : EvalsToInTime
          (step affineExactlyOneMarkedExpandRevProgram)
          (affineExactlyOneMarkedExpandLoopCfg
            (encodeAffineExactlyOneCompactFamily row ++
              .frameEnd :: restInput) output)
          (some bodyStart) 5 := by
        simpa [bodyStart] using affineExactlyOneMarkedExpand_dispatch_run
          _ output hinvocation
      have hbody : EvalsToInTime
          (step affineExactlyOneMarkedExpandRevProgram)
          bodyStart (some bodyDone)
          (affineExactlyOneFrameExpandToInvalidSteps row) := by
        simpa [bodyStart, bodyDone] using
          affineExactlyOneMarkedExpand_body_run row restInput (.tick :: output)
      have hbridge : EvalsToInTime
          (step affineExactlyOneMarkedExpandRevProgram)
          bodyDone (some restStart) 2 := by
        refine ⟨⟨2, ?_⟩, le_rfl⟩
        rfl
      have hrest := ih markedOutput
      let h₁ := EvalsToInTime.trans
        (step affineExactlyOneMarkedExpandRevProgram)
        5 _ _ bodyStart _ hdispatch hbody
      let h₂ := EvalsToInTime.trans
        (step affineExactlyOneMarkedExpandRevProgram)
        _ 2 _ bodyDone _ h₁ hbridge
      let full := EvalsToInTime.trans
        (step affineExactlyOneMarkedExpandRevProgram)
        _ _ _ restStart _ h₂ hrest
      convert full using 1
      · simp [encodeAffineExactlyOneCompactMarkedFamily, restInput]
      · simp [encodeAffineExactlyOneTickedMarkedFamily, markedOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneMarkedExpandSteps]
        omega

/-- The one-row base cost is linear in its compact encoding through the
consumed boundary. -/
theorem affineExactlyOneFrameExpandToInvalidSteps_le
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneFrameExpandToInvalidSteps frames ≤
      9 * (encodeAffineExactlyOneCompactFamily frames).length + 1 := by
  induction frames with
  | nil => simp [affineExactlyOneFrameExpandToInvalidSteps,
      encodeAffineExactlyOneCompactFamily]
  | cons frame rest ih =>
      have hone : affineExactlyOneFrameExpandOneSteps frame ≤
          9 * (encodeAffineExactlyOneCompactFrame frame).length := by
        simp [affineExactlyOneFrameExpandOneSteps, unaryTripleLoaderSteps,
          encodeAffineExactlyOneCompactFrame_length]
        omega
      simp only [affineExactlyOneFrameExpandToInvalidSteps,
        encodeAffineExactlyOneCompactFamily, List.length_append]
      omega

/-- The wrapper remains linear in the complete marked compact stream. -/
theorem affineExactlyOneMarkedExpandSteps_le
    (rows : List (List AffineExactlyOneFrame)) :
    affineExactlyOneMarkedExpandSteps rows ≤
      9 * (encodeAffineExactlyOneCompactMarkedFamily rows).length + 2 := by
  induction rows with
  | nil => simp [affineExactlyOneMarkedExpandSteps,
      encodeAffineExactlyOneCompactMarkedFamily]
  | cons row rest ih =>
      have hrow := affineExactlyOneFrameExpandToInvalidSteps_le row
      simp only [affineExactlyOneMarkedExpandSteps,
        encodeAffineExactlyOneCompactMarkedFamily, List.length_append,
        List.length_cons]
      omega

/-- Compiled prepend-order marked expansion. -/
noncomputable def affineExactlyOneMarkedExpandRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneCompactMarkedFamily id
      (fun rows : List (List AffineExactlyOneFrame) =>
        (encodeAffineExactlyOneTickedMarkedFamily rows).reverse) where
  tm := compile affineExactlyOneMarkedExpandRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 9 * Polynomial.X + 2
  outputsFun := fun rows => by
    have builderRun := affineExactlyOneMarkedExpand_runFrom rows []
    have compiledRun := compile_evalsToInTime
      affineExactlyOneMarkedExpandRevProgram builderRun
    have hinitial : affineExactlyOneMarkedExpandLoopCfg
        (encodeAffineExactlyOneCompactMarkedFamily rows) [] =
          initialCfg affineExactlyOneMarkedExpandRevProgram
            (encodeAffineExactlyOneCompactMarkedFamily rows) := rfl
    rw [hinitial] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneMarkedExpandRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneMarkedExpandRevProgram)
          (encodeAffineExactlyOneCompactMarkedFamily rows))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneMarkedExpandRevProgram)
          (encodeAffineExactlyOneTickedMarkedFamily rows).reverse))
        (affineExactlyOneMarkedExpandSteps rows) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineExactlyOneMarkedExpandSteps rows ≤
        (9 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneCompactMarkedFamily rows).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineExactlyOneMarkedExpandSteps_le rows
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneMarkedExpandRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneMarkedExpandRevProgram)
          (encodeAffineExactlyOneCompactMarkedFamily rows))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneMarkedExpandRevProgram)
          (encodeAffineExactlyOneTickedMarkedFamily rows).reverse))
        ((9 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneCompactMarkedFamily rows).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward row-marked canonical expansion. -/
noncomputable def affineExactlyOneMarkedExpand_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneCompactMarkedFamily id
      encodeAffineExactlyOneTickedMarkedFamily := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineExactlyOneMarkedExpandRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
