import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOneFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import Mathlib.Tactic

/-!
# Compact source for exactly-one output wires

The final Cook--Levin validity conjunction needs only the last fresh wire of
each exactly-one frame.  This fixed controller loads `(start, count, 0)`,
computes `start + 3 * count + 3` in unary, and emits one delimiter-bearing
wire block.  The unused source base of the original exactly-one frame never
enters this compact invocation.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Compact runtime invocation for one exactly-one output wire. -/
def encodeAffineExactlyOneOutputSourceInvocation
    (frame : AffineExactlyOneFrame) : List UnaryFrameSym :=
  encodeUnaryFrame [frame.start, frame.count, 0]

/-- Loader, arithmetic, and unary-emission phases of the fixed source. -/
inductive AffineExactlyOneOutputSourceLabel
  | loader (label : UnaryTripleLoaderLabel)
  | addCount | addCount₁ | addCount₂ | addCount₃
  | addConst₁ | addConst₂ | addConst₃
  | emit | pushTick | pushSeparator
  | finish | invalid
deriving DecidableEq, Fintype

private def outputSourceRelabelOp {Delta : Type}
    (tag : UnaryTripleLoaderLabel → AffineExactlyOneOutputSourceLabel) :
    Op UnaryFrameSym Delta UnaryTripleLoaderLabel →
      Op UnaryFrameSym Delta AffineExactlyOneOutputSourceLabel
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

/-- One fixed program for every runtime exactly-one frame. -/
def affineExactlyOneOutputSourceRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneOutputSourceLabel
  main := .loader .load₁
  op
    | .loader .ready => .popWork₁ .addCount (fun _ => .invalid)
    | .loader label => outputSourceRelabelOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label)
    | .addCount => .dec₂ .addConst₁ .addCount₁
    | .addCount₁ => .inc₁ .addCount₂
    | .addCount₂ => .inc₁ .addCount₃
    | .addCount₃ => .inc₁ .addCount
    | .addConst₁ => .inc₁ .addConst₂
    | .addConst₂ => .inc₁ .addConst₃
    | .addConst₃ => .inc₁ .emit
    | .emit => .dec₁ .pushSeparator .pushTick
    | .pushTick => .pushOutput .tick .emit
    | .pushSeparator => .pushOutput .separator .finish
    | .finish => .halt
    | .invalid => .halt

private def affineExactlyOneOutputSourceCfg
    (label : AffineExactlyOneOutputSourceLabel)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (value count spare : List Unit) :
    BuilderCfg affineExactlyOneOutputSourceRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := value
  counter₂ := count
  counter₃ := spare

/-- Clean public entry, preserving an arbitrary following invocation. -/
def affineExactlyOneOutputSourceLoopCfg
    (frame : AffineExactlyOneFrame) (tail output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneOutputSourceRevProgram :=
  affineExactlyOneOutputSourceCfg (.loader .load₁) none false
    (encodeAffineExactlyOneOutputSourceInvocation frame ++ tail)
    output [] [] [] [] []

/-- Clean redirectable exit after one output-wire block. -/
def affineExactlyOneOutputSourceFinishCfg
    (tail output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneOutputSourceRevProgram :=
  affineExactlyOneOutputSourceCfg .finish none false tail output [] [] [] [] []

private def liftOutputSourceLoaderCfg
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    BuilderCfg affineExactlyOneOutputSourceRevProgram where
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

private theorem outputSourceRelabel_stepOp
    (op : Op UnaryFrameSym UnaryFrameSym UnaryTripleLoaderLabel)
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    stepOp (outputSourceRelabelOp .loader op)
        (liftOutputSourceLoaderCfg c) =
      liftOutputSourceLoaderCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [outputSourceRelabelOp, liftOutputSourceLoaderCfg,
      stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneOutputSource_op_loader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineExactlyOneOutputSourceRevProgram.op (.loader label) =
      outputSourceRelabelOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) := by
  cases label <;>
    simp_all [affineExactlyOneOutputSourceRevProgram]

private theorem liftOutputSourceLoader_step
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym))
    (hexit : c.label ≠ some .ready) :
    step affineExactlyOneOutputSourceRevProgram
        (liftOutputSourceLoaderCfg c) =
      Option.map liftOutputSourceLoaderCfg
        (step (unaryTripleLoaderProgramFor UnaryFrameSym) c) := by
  unfold step
  rw [show (liftOutputSourceLoaderCfg c).label = c.label.map .loader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneOutputSource_op_loader label hlabelExit]
      exact congrArg some
        (outputSourceRelabel_stepOp
          ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) c)

private theorem outputSource_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem outputSource_haltExit_no_return
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
      rw [hnone, outputSource_iterate_bind_none]
      simp

private theorem outputSource_lift_iterations_to_ready
    {a b : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)}
    (hb : b.label = some .ready) : ∀ n : Nat,
    (flip Option.bind
      (step (unaryTripleLoaderProgramFor UnaryFrameSym)))^[n]
        (some a) = some b →
      (flip Option.bind
        (step affineExactlyOneOutputSourceRevProgram))^[n]
          (some (liftOutputSourceLoaderCfg a)) =
            some (liftOutputSourceLoaderCfg b) := by
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
        (step (unaryTripleLoaderProgramFor UnaryFrameSym)))^[n]
          (step (unaryTripleLoaderProgramFor UnaryFrameSym) a) = some b at h
      change (flip Option.bind
        (step affineExactlyOneOutputSourceRevProgram))^[n]
          (step affineExactlyOneOutputSourceRevProgram
            (liftOutputSourceLoaderCfg a)) =
              some (liftOutputSourceLoaderCfg b)
      have haexit : a.label ≠ some .ready := by
        intro ha
        exact outputSource_haltExit_no_return
          UnaryTripleLoaderLabel.ready rfl a b ha hb n h
      cases hsource : step
          (unaryTripleLoaderProgramFor UnaryFrameSym) a with
      | none =>
          rw [hsource, outputSource_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftOutputSourceLoader_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineExactlyOneOutputSource_loader_run
    (frame : AffineExactlyOneFrame) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneOutputSourceRevProgram)
      (affineExactlyOneOutputSourceLoopCfg frame tail output)
      (some (liftOutputSourceLoaderCfg
        (unaryTripleLoaderReadyCfgFor frame.start frame.count 0 tail output
          [] [])))
      (unaryTripleLoaderSteps frame.start frame.count 0) := by
  have sourceRun := unaryTripleLoader_runFor (Δ := UnaryFrameSym)
    frame.start frame.count 0 tail output [] []
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have hstart : affineExactlyOneOutputSourceLoopCfg frame tail output =
      liftOutputSourceLoaderCfg
        (unaryTripleLoaderCfgFor UnaryTripleLoaderLabel.load₁ none
          (encodeUnaryFrame [frame.start, frame.count, 0] ++ tail)
          output [] [] [] [] []) := by
    rfl
  rw [hstart]
  exact outputSource_lift_iterations_to_ready rfl sourceRun.steps
    sourceRun.evals_in_steps

private theorem outputSource_addCount_eval (value count : Nat)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind
      (step affineExactlyOneOutputSourceRevProgram))^[4 * count + 4]
      (some (affineExactlyOneOutputSourceCfg .addCount none false
        tail output [] [] (List.replicate value ())
        (List.replicate count ()) [])) =
      some (affineExactlyOneOutputSourceCfg .emit none false
        tail output [] []
        (List.replicate (value + 3 * count + 3) ()) [] []) := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih =>
      rw [show 4 * (count + 1) + 4 = (4 * count + 4) + 1 + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneOutputSourceRevProgram))^[4 * count + 4]
          (some (affineExactlyOneOutputSourceCfg .addCount none false
            tail output [] [] (() :: (() :: (() :: List.replicate value ())))
            (List.replicate count ()) [])) = _
      have hvalue : (() :: (() :: (() :: List.replicate value ()))) =
          List.replicate (value + 3) () := by
        rw [show value + 3 = 3 + value by omega, List.replicate_add]
        rfl
      rw [hvalue]
      convert ih (value + 3) using 1
      congr 3
      omega

private theorem outputSource_replicate_append_cons {alpha : Type}
    (item : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count item ++ item :: tail =
      item :: (List.replicate count item ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons item) ih

private theorem outputSource_emit_eval (value : Nat) (test : Bool)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind
      (step affineExactlyOneOutputSourceRevProgram))^[2 * value + 2]
      (some (affineExactlyOneOutputSourceCfg .emit none test
        tail output [] [] (List.replicate value ()) [] [])) =
      some (affineExactlyOneOutputSourceFinishCfg tail
        ((encodeUnaryFrameBlock value).reverse ++ output)) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 = (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneOutputSourceRevProgram))^[2 * value + 2]
          (some (affineExactlyOneOutputSourceCfg .emit none true
            tail (.tick :: output) [] [] (List.replicate value ()) [] [])) = _
      convert ih true (.tick :: output) using 1
      simp [encodeUnaryFrameBlock, List.replicate_succ,
        outputSource_replicate_append_cons]

/-- Exact runtime of the compact one-frame output source. -/
def affineExactlyOneOutputSourceSteps
    (frame : AffineExactlyOneFrame) : Nat :=
  unaryTripleLoaderSteps frame.start frame.count 0 + 1 +
    (4 * frame.count + 4) +
      (2 * affineExactlyOneFrameOutputWire frame + 2)

/-- The fixed controller emits exactly the unary block of the frame's last
fresh wire and preserves the following invocation. -/
def affineExactlyOneOutputSource_runToFinish
    (frame : AffineExactlyOneFrame) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneOutputSourceRevProgram)
      (affineExactlyOneOutputSourceLoopCfg frame tail output)
      (some (affineExactlyOneOutputSourceFinishCfg tail
        ((encodeUnaryFrameBlock
          (affineExactlyOneFrameOutputWire frame)).reverse ++ output)))
      (affineExactlyOneOutputSourceSteps frame) := by
  have hloader := affineExactlyOneOutputSource_loader_run frame tail output
  let ready := liftOutputSourceLoaderCfg
    (unaryTripleLoaderReadyCfgFor frame.start frame.count 0 tail output [] [])
  let arithmeticStart := affineExactlyOneOutputSourceCfg .addCount none false
    tail output [] [] (List.replicate frame.start ())
    (List.replicate frame.count ()) []
  have hbridge : EvalsToInTime
      (step affineExactlyOneOutputSourceRevProgram)
      ready (some arithmeticStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have harithmetic := outputSource_addCount_eval
    frame.start frame.count tail output
  have harithmeticRun : EvalsToInTime
      (step affineExactlyOneOutputSourceRevProgram)
      arithmeticStart
      (some (affineExactlyOneOutputSourceCfg .emit none false tail output
        [] [] (List.replicate
          (affineExactlyOneFrameOutputWire frame) ()) [] []))
      (4 * frame.count + 4) := by
    refine ⟨⟨4 * frame.count + 4, ?_⟩, le_rfl⟩
    simpa [arithmeticStart, affineExactlyOneFrameOutputWire] using harithmetic
  have hemit := outputSource_emit_eval
    (affineExactlyOneFrameOutputWire frame) false tail output
  have hemitRun : EvalsToInTime
      (step affineExactlyOneOutputSourceRevProgram)
      (affineExactlyOneOutputSourceCfg .emit none false tail output [] []
        (List.replicate (affineExactlyOneFrameOutputWire frame) ()) [] [])
      (some (affineExactlyOneOutputSourceFinishCfg tail
        ((encodeUnaryFrameBlock
          (affineExactlyOneFrameOutputWire frame)).reverse ++ output)))
      (2 * affineExactlyOneFrameOutputWire frame + 2) :=
    ⟨⟨_, hemit⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneOutputSourceRevProgram) _ 1 _ ready _
      hloader hbridge
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneOutputSourceRevProgram) _ _ _ arithmeticStart _
      h₁ harithmeticRun
  let full := EvalsToInTime.trans
    (step affineExactlyOneOutputSourceRevProgram) _ _ _ _ _ h₂ hemitRun
  convert full using 1
  simp [affineExactlyOneOutputSourceSteps]
  omega

/-- The source is linear in its compact invocation and hence admits this
simple quadratic envelope. -/
theorem affineExactlyOneOutputSourceSteps_le
    (frame : AffineExactlyOneFrame) :
    affineExactlyOneOutputSourceSteps frame ≤
      20 * (encodeAffineExactlyOneOutputSourceInvocation frame).length ^ 2 := by
  rw [show (encodeAffineExactlyOneOutputSourceInvocation frame).length =
      frame.start + frame.count + 3 by
    simp [encodeAffineExactlyOneOutputSourceInvocation,
      encodeUnaryFrame_length]
    omega]
  simp [affineExactlyOneOutputSourceSteps, unaryTripleLoaderSteps,
    affineExactlyOneFrameOutputWire]
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
