import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource
import Mathlib.Tactic

/-!
# Re-encoding seed-preserving one-hot rows as projector carriers

The seed-preserving structured-row source emits packets

`seed ++ frameEnd ++ compactRow ++ frameEnd`.

This module turns each packet into one marked compact row whose first two
synthetic frames retain all three seed fields.  The ordinary marked-row
projector can therefore process the synthetic carriers and the genuine
one-hot frames in one pass, without duplicating or zipping two machines.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Two synthetic compact frames whose projected `(start,count,0)` operands
retain `(height,start,rowBase)` without using the ignored compact base field. -/
def affineExactlyOneStructuredRowSeedCarrierFrames
    (seed : AffineExactlyOneStructuredRowSeed) : List AffineExactlyOneFrame :=
  [ { start := seed.height, rowBase := 0, count := seed.start }
  , { start := seed.rowBase, rowBase := 0, count := 0 } ]

/-- Marked compact rows with the two seed carriers prepended to each genuine
structured one-hot row. -/
def encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowSeedCarrierFrames seed ++
            affineExactlyOneStructuredRowFrames labelWidth stateWidth
              cellCounts seed.height seed.start seed.rowBase) ++
        [.frameEnd] ++
        encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts rest

private theorem seedCarrier_encodeCompactFamily_append
    (left right : List AffineExactlyOneFrame) :
    encodeAffineExactlyOneCompactFamily (left ++ right) =
      encodeAffineExactlyOneCompactFamily left ++
        encodeAffineExactlyOneCompactFamily right := by
  induction left with
  | nil => rfl
  | cons frame rest ih =>
      simp [encodeAffineExactlyOneCompactFamily, ih, List.append_assoc]

/-- Finite control for the seed-packet to carrier-row transducer. -/
inductive AffineExactlyOneSeedCarrierLabel
  | loader (label : UnaryTripleLoaderLabel)
  | emitHeight | emitHeightTick | emitHeightSeparator
  | emitHeightZeroSeparator
  | emitStart | emitStartTick | emitStartSeparator
  | emitRowBase | emitRowBaseTick
  | emitRowBaseSeparator₁ | emitRowBaseSeparator₂
  | emitRowBaseSeparator₃
  | expectSeedEnd
  | copyRow | copyRowSymbol (symbol : UnaryFrameSym) | markRow
  | clearBuffer
  | finish | invalid
deriving DecidableEq, Fintype

private def seedCarrierRelabelLoaderOp {Delta : Type}
    (tag : UnaryTripleLoaderLabel → AffineExactlyOneSeedCarrierLabel) :
    Op UnaryFrameSym Delta UnaryTripleLoaderLabel →
      Op UnaryFrameSym Delta AffineExactlyOneSeedCarrierLabel
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

/-- Fixed transducer.  It emits each carrier encoding in forward instruction
order, copies the genuine compact row in forward input order, and relies on
prepend output to obtain the reverse of the complete marked carrier family. -/
abbrev affineExactlyOneSeedCarrierRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneSeedCarrierLabel
  main := .loader .load₁
  op
    | .loader .ready => .jump .emitHeight
    | .loader label =>
        seedCarrierRelabelLoaderOp .loader
          ((unaryTripleLoaderProgramFor UnaryFrameSym).op label)
    | .emitHeight => .dec₁ .emitHeightSeparator .emitHeightTick
    | .emitHeightTick => .pushOutput .tick .emitHeight
    | .emitHeightSeparator =>
        .pushOutput .separator .emitHeightZeroSeparator
    | .emitHeightZeroSeparator => .pushOutput .separator .emitStart
    | .emitStart => .dec₂ .emitStartSeparator .emitStartTick
    | .emitStartTick => .pushOutput .tick .emitStart
    | .emitStartSeparator => .pushOutput .separator .emitRowBase
    | .emitRowBase =>
        .dec₃ .emitRowBaseSeparator₁ .emitRowBaseTick
    | .emitRowBaseTick => .pushOutput .tick .emitRowBase
    | .emitRowBaseSeparator₁ =>
        .pushOutput .separator .emitRowBaseSeparator₂
    | .emitRowBaseSeparator₂ =>
        .pushOutput .separator .emitRowBaseSeparator₃
    | .emitRowBaseSeparator₃ =>
        .pushOutput .separator .expectSeedEnd
    | .expectSeedEnd => .popInput .invalid fun
        | .frameEnd => .copyRow
        | _ => .invalid
    | .copyRow => .popInput .finish fun
        | .frameEnd => .markRow
        | symbol => .copyRowSymbol symbol
    | .copyRowSymbol symbol => .pushOutput symbol .copyRow
    | .markRow => .pushOutput .frameEnd .clearBuffer
    | .clearBuffer => .popWork₁ (.loader .load₁) fun _ => .loader .load₁
    | .finish => .halt
    | .invalid => .halt

private def affineExactlyOneSeedCarrierCfg
    (label : AffineExactlyOneSeedCarrierLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg affineExactlyOneSeedCarrierRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := height
  counter₂ := start
  counter₃ := rowBase

private def affineExactlyOneSeedCarrierLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneSeedCarrierRevProgram :=
  affineExactlyOneSeedCarrierCfg (.loader .load₁) none none false
    input output [] [] [] [] []

private def liftSeedCarrierLoaderCfg
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    BuilderCfg affineExactlyOneSeedCarrierRevProgram where
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

private theorem seedCarrierRelabelLoader_stepOp
    (op : Op UnaryFrameSym UnaryFrameSym UnaryTripleLoaderLabel)
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    stepOp (P := affineExactlyOneSeedCarrierRevProgram)
        (seedCarrierRelabelLoaderOp .loader op) (liftSeedCarrierLoaderCfg c) =
      liftSeedCarrierLoaderCfg
        (stepOp (P := unaryTripleLoaderProgramFor UnaryFrameSym) op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [seedCarrierRelabelLoaderOp, liftSeedCarrierLoaderCfg,
      stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneSeedCarrier_op_loader
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    affineExactlyOneSeedCarrierRevProgram.op (.loader label) =
      seedCarrierRelabelLoaderOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) := by
  cases label <;>
    simp_all [affineExactlyOneSeedCarrierRevProgram]

private theorem liftSeedCarrierLoader_step
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym))
    (hexit : c.label ≠ some .ready) :
    step affineExactlyOneSeedCarrierRevProgram (liftSeedCarrierLoaderCfg c) =
      Option.map liftSeedCarrierLoaderCfg
        (step (unaryTripleLoaderProgramFor UnaryFrameSym) c) := by
  unfold step
  rw [show (liftSeedCarrierLoaderCfg c).label =
    c.label.map AffineExactlyOneSeedCarrierLabel.loader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      change some (stepOp
        (affineExactlyOneSeedCarrierRevProgram.op (.loader label))
        (liftSeedCarrierLoaderCfg c)) =
          some (liftSeedCarrierLoaderCfg
            (stepOp ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) c))
      rw [affineExactlyOneSeedCarrier_op_loader label hlabelExit]
      exact congrArg some (seedCarrierRelabelLoader_stepOp
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) c)

private theorem seedCarrier_iterate_bind_none
    {alpha : Type} (f : alpha → Option alpha) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem seedCarrier_haltExit_no_return
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
      rw [hnone, seedCarrier_iterate_bind_none]
      simp

private theorem seedCarrier_lift_iterations_to_ready
    {P Q : Program UnaryFrameSym UnaryFrameSym} (exit : P.Label)
    (hop : P.op exit = .halt) (tr : BuilderCfg P → BuilderCfg Q)
    (hstep : ∀ c, c.label ≠ some exit →
      step Q (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step Q))^[n] (some (tr a)) = some (tr b) := by
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
      change (flip Option.bind (step Q))^[n] (step Q (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact seedCarrier_haltExit_no_return exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, seedCarrier_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineExactlyOneSeedCarrier_loader_run
    (height start rowBase : Nat) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      (affineExactlyOneSeedCarrierLoopCfg
        (encodeUnaryFrame [height, start, rowBase] ++ tail) output)
      (some (affineExactlyOneSeedCarrierCfg (.loader .ready)
        (some .separator) none false tail output [] []
        (List.replicate height ()) (List.replicate start ())
        (List.replicate rowBase ())))
      (unaryTripleLoaderSteps height start rowBase) := by
  have sourceRun := unaryTripleLoader_runFor
    (Δ := UnaryFrameSym) height start rowBase tail output [] []
  have htarget :
      (unaryTripleLoaderReadyCfgFor height start rowBase tail output
        ([] : List UnaryFrameSym) []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have hstart : liftSeedCarrierLoaderCfg
      (unaryTripleLoaderCfgFor .load₁ none
        (encodeUnaryFrame [height, start, rowBase] ++ tail)
        output [] [] [] [] []) =
      affineExactlyOneSeedCarrierLoopCfg
        (encodeUnaryFrame [height, start, rowBase] ++ tail) output := rfl
  rw [← hstart]
  exact seedCarrier_lift_iterations_to_ready UnaryTripleLoaderLabel.ready rfl
    liftSeedCarrierLoaderCfg liftSeedCarrierLoader_step htarget
    sourceRun.steps sourceRun.evals_in_steps

private theorem seedCarrier_replicate_append_cons
    {alpha : Type} (item : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count item ++ item :: tail =
      item :: (List.replicate count item ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons item) ih

private theorem seedCarrier_emitHeight_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (start rowBase : List Unit) :
    (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * value + 1]
      (some (affineExactlyOneSeedCarrierCfg .emitHeight
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate value ()) start rowBase)) =
      some (affineExactlyOneSeedCarrierCfg .emitHeightSeparator
        buffer₁ buffer₂ false input
        (List.replicate value .tick ++ output) work₁ work₂
        [] start rowBase) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * value + 1]
          (some (affineExactlyOneSeedCarrierCfg .emitHeight
            buffer₁ buffer₂ true input (.tick :: output) work₁ work₂
            (List.replicate value ()) start rowBase)) = _
      simpa only [List.replicate_succ, List.cons_append,
        seedCarrier_replicate_append_cons] using
        ih true (.tick :: output)

private theorem seedCarrier_emitStart_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height rowBase : List Unit) :
    (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * value + 1]
      (some (affineExactlyOneSeedCarrierCfg .emitStart
        buffer₁ buffer₂ test input output work₁ work₂
        height (List.replicate value ()) rowBase)) =
      some (affineExactlyOneSeedCarrierCfg .emitStartSeparator
        buffer₁ buffer₂ false input
        (List.replicate value .tick ++ output) work₁ work₂
        height [] rowBase) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * value + 1]
          (some (affineExactlyOneSeedCarrierCfg .emitStart
            buffer₁ buffer₂ true input (.tick :: output) work₁ work₂
            height (List.replicate value ()) rowBase)) = _
      simpa only [List.replicate_succ, List.cons_append,
        seedCarrier_replicate_append_cons] using
        ih true (.tick :: output)

private theorem seedCarrier_emitRowBase_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start : List Unit) :
    (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * value + 1]
      (some (affineExactlyOneSeedCarrierCfg .emitRowBase
        buffer₁ buffer₂ test input output work₁ work₂
        height start (List.replicate value ()))) =
      some (affineExactlyOneSeedCarrierCfg .emitRowBaseSeparator₁
        buffer₁ buffer₂ false input
        (List.replicate value .tick ++ output) work₁ work₂
        height start []) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * value + 1]
          (some (affineExactlyOneSeedCarrierCfg .emitRowBase
            buffer₁ buffer₂ true input (.tick :: output) work₁ work₂
            height start (List.replicate value ()))) = _
      simpa only [List.replicate_succ, List.cons_append,
        seedCarrier_replicate_append_cons] using
        ih true (.tick :: output)

private theorem seedCarrier_replicate_tick_no_frameEnd (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).Forall
      (fun symbol => symbol ≠ .frameEnd) := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp [List.replicate_succ, List.forall_cons, ih]

private theorem seedCarrier_compact_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    (encodeAffineExactlyOneCompactFamily frames).Forall
      (fun symbol => symbol ≠ .frameEnd) := by
  induction frames with
  | nil => simp [encodeAffineExactlyOneCompactFamily]
  | cons frame rest ih =>
      simp [encodeAffineExactlyOneCompactFamily,
        encodeAffineExactlyOneCompactFrame, encodeUnaryFrame,
        encodeUnaryFrameBlock, List.forall_append,
        seedCarrier_replicate_tick_no_frameEnd, ih]

private theorem seedCarrier_copyRow_eval
    (row tail output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (height start rowBase : List Unit)
    (hrow : row.Forall (fun symbol => symbol ≠ .frameEnd)) :
    (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * row.length + 1]
      (some (affineExactlyOneSeedCarrierCfg .copyRow
        buffer₁ buffer₂ test (row ++ .frameEnd :: tail) output
        work₁ work₂ height start rowBase)) =
      some (affineExactlyOneSeedCarrierCfg .markRow
        (some .frameEnd) buffer₂ test tail (row.reverse ++ output)
        work₁ work₂ height start rowBase) := by
  induction row generalizing buffer₁ output with
  | nil => rfl
  | cons symbol row ih =>
      rw [List.forall_cons] at hrow
      have hs := hrow.1
      have hr := hrow.2
      rw [show 2 * (symbol :: row).length + 1 =
          (2 * row.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases symbol <;> simp at hs
      all_goals
        change
          (flip Option.bind (step affineExactlyOneSeedCarrierRevProgram))^[2 * row.length + 1]
            (some (affineExactlyOneSeedCarrierCfg .copyRow
              (some _) buffer₂ test (row ++ .frameEnd :: tail)
              (_ :: output) work₁ work₂ height start rowBase)) = _
        simpa [List.reverse_cons, List.append_assoc] using
          ih (_ :: output) (some _) hr

/-- Cost from the embedded loader's ready state to the beginning of the
genuine compact-row copy. -/
def affineExactlyOneSeedCarrierEmitSteps
    (height start rowBase : Nat) : Nat :=
  2 * (height + start + rowBase) + 11

private def affineExactlyOneSeedCarrier_emit_run
    (height start rowBase : Nat)
    (row tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      (affineExactlyOneSeedCarrierCfg (.loader .ready)
        (some .separator) none false
        (.frameEnd :: row ++ .frameEnd :: tail) output [] []
        (List.replicate height ()) (List.replicate start ())
        (List.replicate rowBase ()))
      (some (affineExactlyOneSeedCarrierCfg .copyRow
        (some .frameEnd) none false (row ++ .frameEnd :: tail)
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowSeedCarrierFrames
            { height := height, start := start, rowBase := rowBase })).reverse ++
          output) [] [] [] [] []))
      (affineExactlyOneSeedCarrierEmitSteps height start rowBase) := by
  let afterReady := affineExactlyOneSeedCarrierCfg .emitHeight
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    output [] [] (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())
  let afterHeight := affineExactlyOneSeedCarrierCfg .emitHeightSeparator
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (List.replicate height .tick ++ output) [] [] []
    (List.replicate start ()) (List.replicate rowBase ())
  let afterHeightSep := affineExactlyOneSeedCarrierCfg
    .emitHeightZeroSeparator (some .separator) none false
    (.frameEnd :: row ++ .frameEnd :: tail)
    (.separator :: List.replicate height .tick ++ output) [] [] []
    (List.replicate start ()) (List.replicate rowBase ())
  let beforeStart := affineExactlyOneSeedCarrierCfg .emitStart
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (.separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] (List.replicate start ()) (List.replicate rowBase ())
  let afterStart := affineExactlyOneSeedCarrierCfg .emitStartSeparator
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (List.replicate start .tick ++
      .separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] [] (List.replicate rowBase ())
  let beforeBase := affineExactlyOneSeedCarrierCfg .emitRowBase
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (.separator :: List.replicate start .tick ++
      .separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] [] (List.replicate rowBase ())
  let afterBase := affineExactlyOneSeedCarrierCfg .emitRowBaseSeparator₁
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (List.replicate rowBase .tick ++
      .separator :: List.replicate start .tick ++
      .separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] [] []
  let afterBaseSep₁ := affineExactlyOneSeedCarrierCfg .emitRowBaseSeparator₂
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (.separator :: List.replicate rowBase .tick ++
      .separator :: List.replicate start .tick ++
      .separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] [] []
  let afterBaseSep₂ := affineExactlyOneSeedCarrierCfg .emitRowBaseSeparator₃
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (.separator :: .separator :: List.replicate rowBase .tick ++
      .separator :: List.replicate start .tick ++
      .separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] [] []
  let beforeBoundary := affineExactlyOneSeedCarrierCfg .expectSeedEnd
    (some .separator) none false (.frameEnd :: row ++ .frameEnd :: tail)
    (.separator :: .separator :: .separator ::
      List.replicate rowBase .tick ++
      .separator :: List.replicate start .tick ++
      .separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] [] []
  let afterBoundary := affineExactlyOneSeedCarrierCfg .copyRow
    (some .frameEnd) none false (row ++ .frameEnd :: tail)
    (.separator :: .separator :: .separator ::
      List.replicate rowBase .tick ++
      .separator :: List.replicate start .tick ++
      .separator :: .separator :: List.replicate height .tick ++ output)
    [] [] [] [] []
  have hready : EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      (affineExactlyOneSeedCarrierCfg (.loader .ready)
        (some .separator) none false
        (.frameEnd :: row ++ .frameEnd :: tail) output [] []
        (List.replicate height ()) (List.replicate start ())
        (List.replicate rowBase ())) (some afterReady) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hheight : EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      afterReady (some afterHeight) (2 * height + 1) := by
    refine ⟨⟨2 * height + 1, ?_⟩, le_rfl⟩
    simpa [afterReady, afterHeight] using seedCarrier_emitHeight_eval
      height (some .separator) none false
      (.frameEnd :: row ++ .frameEnd :: tail) output [] []
      (List.replicate start ()) (List.replicate rowBase ())
  have hheightSep : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      afterHeight (some afterHeightSep) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hheightZero : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      afterHeightSep (some beforeStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hstart : EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      beforeStart (some afterStart) (2 * start + 1) := by
    refine ⟨⟨2 * start + 1, ?_⟩, le_rfl⟩
    convert
      seedCarrier_emitStart_eval start (some .separator) none false
        (.frameEnd :: row ++ .frameEnd :: tail)
        (.separator :: .separator :: List.replicate height .tick ++ output)
        [] [] [] (List.replicate rowBase ()) using 1 <;>
      simp [beforeStart, afterStart, List.cons_append, List.append_assoc]
  have hstartSep : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      afterStart (some beforeBase) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hbase : EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      beforeBase (some afterBase) (2 * rowBase + 1) := by
    refine ⟨⟨2 * rowBase + 1, ?_⟩, le_rfl⟩
    convert
      seedCarrier_emitRowBase_eval rowBase (some .separator) none false
        (.frameEnd :: row ++ .frameEnd :: tail)
        (.separator :: List.replicate start .tick ++
          .separator :: .separator :: List.replicate height .tick ++ output)
        [] [] [] [] using 1 <;>
      simp [beforeBase, afterBase, List.cons_append, List.append_assoc]
  have hbaseSep₁ : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      afterBase (some afterBaseSep₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hbaseSep₂ : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      afterBaseSep₁ (some afterBaseSep₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hbaseSep₃ : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      afterBaseSep₂ (some beforeBoundary) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hboundary : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      beforeBoundary (some afterBoundary) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    1 _ _ afterReady _ hready hheight
  let h₂ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 1 _ afterHeight _ h₁ hheightSep
  let h₃ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 1 _ afterHeightSep _ h₂ hheightZero
  let h₄ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ _ _ beforeStart _ h₃ hstart
  let h₅ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 1 _ afterStart _ h₄ hstartSep
  let h₆ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ _ _ beforeBase _ h₅ hbase
  let h₇ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 1 _ afterBase _ h₆ hbaseSep₁
  let h₈ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 1 _ afterBaseSep₁ _ h₇ hbaseSep₂
  let h₉ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 1 _ afterBaseSep₂ _ h₈ hbaseSep₃
  let full := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 1 _ beforeBoundary _ h₉ hboundary
  convert full using 1 <;>
    simp [afterBoundary, affineExactlyOneStructuredRowSeedCarrierFrames,
      encodeAffineExactlyOneCompactFamily,
      encodeAffineExactlyOneCompactFrame, encodeUnaryFrame,
      encodeUnaryFrameBlock, affineExactlyOneSeedCarrierEmitSteps,
      List.reverse_append, List.append_assoc] <;> omega

/-- Exact cost of one seed packet, including the compact-row copy and the
final row marker. -/
def affineExactlyOneSeedCarrierOneSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : Nat :=
  4 * (seed.height + seed.start + seed.rowBase) +
    2 * (encodeAffineExactlyOneCompactFamily
      (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
        seed.height seed.start seed.rowBase)).length + 17

private def affineExactlyOneSeedCarrier_one
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      (affineExactlyOneSeedCarrierLoopCfg
        (encodeAffineExactlyOneStructuredRowSeed seed ++ [.frameEnd] ++
          encodeAffineExactlyOneCompactFamily
            (affineExactlyOneStructuredRowFrames labelWidth stateWidth
              cellCounts seed.height seed.start seed.rowBase) ++
          UnaryFrameSym.frameEnd :: tail) output)
      (some (affineExactlyOneSeedCarrierLoopCfg tail
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowSeedCarrierFrames seed ++
            affineExactlyOneStructuredRowFrames labelWidth stateWidth
              cellCounts seed.height seed.start seed.rowBase) ++
          [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (affineExactlyOneSeedCarrierOneSteps
        labelWidth stateWidth cellCounts seed) := by
  let row := encodeAffineExactlyOneCompactFamily
    (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
      seed.height seed.start seed.rowBase)
  let carrier := encodeAffineExactlyOneCompactFamily
    (affineExactlyOneStructuredRowSeedCarrierFrames seed)
  let loaderReady := affineExactlyOneSeedCarrierCfg (.loader .ready)
    (some .separator) none false
    (.frameEnd :: row ++ .frameEnd :: tail) output [] []
    (List.replicate seed.height ()) (List.replicate seed.start ())
    (List.replicate seed.rowBase ())
  let copyStart := affineExactlyOneSeedCarrierCfg .copyRow
    (some .frameEnd) none false (row ++ .frameEnd :: tail)
    (carrier.reverse ++ output) [] [] [] [] []
  let beforeMark := affineExactlyOneSeedCarrierCfg .markRow
    (some .frameEnd) none false tail
    (row.reverse ++ carrier.reverse ++ output) [] [] [] [] []
  let rowOutput := .frameEnd :: row.reverse ++ carrier.reverse ++ output
  have hloader : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      (affineExactlyOneSeedCarrierLoopCfg
        (encodeAffineExactlyOneStructuredRowSeed seed ++ [.frameEnd] ++
          row ++ .frameEnd :: tail) output)
      (some loaderReady)
      (unaryTripleLoaderSteps seed.height seed.start seed.rowBase) := by
    simpa [encodeAffineExactlyOneStructuredRowSeed, loaderReady, row,
      List.append_assoc] using affineExactlyOneSeedCarrier_loader_run
        seed.height seed.start seed.rowBase
        (.frameEnd :: row ++ .frameEnd :: tail) output
  have hemit : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      loaderReady (some copyStart)
      (affineExactlyOneSeedCarrierEmitSteps
        seed.height seed.start seed.rowBase) := by
    simpa [loaderReady, copyStart, carrier] using
      affineExactlyOneSeedCarrier_emit_run seed.height seed.start seed.rowBase
        row tail output
  have hcopy : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      copyStart (some beforeMark) (2 * row.length + 1) :=
    ⟨⟨2 * row.length + 1, by
      simpa [copyStart, beforeMark, List.append_assoc] using
        seedCarrier_copyRow_eval row tail (carrier.reverse ++ output) [] []
          (some .frameEnd) none false [] [] []
          (by
            simpa [row] using
              (seedCarrier_compact_no_frameEnd
                (affineExactlyOneStructuredRowFrames labelWidth stateWidth
                  cellCounts seed.height seed.start seed.rowBase)))⟩,
      le_rfl⟩
  have hmark : EvalsToInTime
      (step affineExactlyOneSeedCarrierRevProgram)
      beforeMark
      (some (affineExactlyOneSeedCarrierLoopCfg tail rowOutput)) 2 :=
    ⟨⟨2, by rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ _ _ loaderReady _ hloader hemit
  let h₂ := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ _ _ copyStart _ h₁ hcopy
  let full := EvalsToInTime.trans (step affineExactlyOneSeedCarrierRevProgram)
    _ 2 _ beforeMark _ h₂ hmark
  convert full using 1 <;>
    simp [affineExactlyOneSeedCarrierOneSteps,
      affineExactlyOneSeedCarrierEmitSteps, unaryTripleLoaderSteps,
      rowOutput, row, carrier,
      seedCarrier_encodeCompactFamily_append,
      List.reverse_append, List.append_assoc]
  all_goals try omega

/-- Exact runtime for the complete packet family. -/
def affineExactlyOneSeedCarrierRevSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → Nat
  | [] => 2
  | seed :: rest =>
      affineExactlyOneSeedCarrierOneSteps
          labelWidth stateWidth cellCounts seed +
        affineExactlyOneSeedCarrierRevSteps
          labelWidth stateWidth cellCounts rest

private def affineExactlyOneSeedCarrier_runFrom
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      (affineExactlyOneSeedCarrierLoopCfg
        (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
          labelWidth stateWidth cellCounts seeds) output)
      (some (haltCfg affineExactlyOneSeedCarrierRevProgram
        ((encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse ++ output)))
      (affineExactlyOneSeedCarrierRevSteps
        labelWidth stateWidth cellCounts seeds) := by
  induction seeds generalizing output with
  | nil =>
      refine ⟨⟨2, ?_⟩, le_rfl⟩
      rfl
  | cons seed rest ih =>
      let rowFrames := affineExactlyOneStructuredRowFrames
        labelWidth stateWidth cellCounts seed.height seed.start seed.rowBase
      let rowOutput :=
        (encodeAffineExactlyOneCompactFamily
          (affineExactlyOneStructuredRowSeedCarrierFrames seed ++ rowFrames) ++
          [UnaryFrameSym.frameEnd]).reverse ++ output
      have hfirst := affineExactlyOneSeedCarrier_one
        labelWidth stateWidth cellCounts seed
        (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
          labelWidth stateWidth cellCounts rest) output
      have hrest := ih rowOutput
      let full := EvalsToInTime.trans
        (step affineExactlyOneSeedCarrierRevProgram)
        (affineExactlyOneSeedCarrierOneSteps
          labelWidth stateWidth cellCounts seed)
        (affineExactlyOneSeedCarrierRevSteps
          labelWidth stateWidth cellCounts rest)
        _ (affineExactlyOneSeedCarrierLoopCfg
          (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
            labelWidth stateWidth cellCounts rest) rowOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineExactlyOneStructuredRowSeedMarkedFamily,
          List.append_assoc]
      · simp [encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily,
          rowFrames, rowOutput, List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneSeedCarrierRevSteps]
        omega

/-- The fixed controller maps forward seed-preserving packets to the reverse
of the marked carrier-row family. -/
def affineExactlyOneSeedCarrierRev_run
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime (step affineExactlyOneSeedCarrierRevProgram)
      (initialCfg affineExactlyOneSeedCarrierRevProgram
        (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
          labelWidth stateWidth cellCounts seeds))
      (some (haltCfg affineExactlyOneSeedCarrierRevProgram
        (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse))
      (affineExactlyOneSeedCarrierRevSteps
        labelWidth stateWidth cellCounts seeds) := by
  have hinit : affineExactlyOneSeedCarrierLoopCfg
      (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
        labelWidth stateWidth cellCounts seeds) [] =
        initialCfg affineExactlyOneSeedCarrierRevProgram
          (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
            labelWidth stateWidth cellCounts seeds) := rfl
  rw [← hinit]
  simpa only [List.append_nil] using
    affineExactlyOneSeedCarrier_runFrom
      labelWidth stateWidth cellCounts seeds []

theorem affineExactlyOneSeedCarrierRev_steps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneSeedCarrierRevSteps
        labelWidth stateWidth cellCounts seeds ≤
      4 * (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
        labelWidth stateWidth cellCounts seeds).length + 2 := by
  induction seeds with
  | nil =>
      simp [affineExactlyOneSeedCarrierRevSteps,
        encodeAffineExactlyOneStructuredRowSeedMarkedFamily]
  | cons seed rest ih =>
      let rowLength := (encodeAffineExactlyOneCompactFamily
        (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
          seed.height seed.start seed.rowBase)).length
      let restLength :=
        (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
          labelWidth stateWidth cellCounts rest).length
      have hone : affineExactlyOneSeedCarrierOneSteps
          labelWidth stateWidth cellCounts seed ≤
          4 * (seed.height + seed.start + seed.rowBase + rowLength + 5) := by
        simp [affineExactlyOneSeedCarrierOneSteps, rowLength]
        omega
      calc
        affineExactlyOneSeedCarrierRevSteps
            labelWidth stateWidth cellCounts (seed :: rest) =
            affineExactlyOneSeedCarrierOneSteps
                labelWidth stateWidth cellCounts seed +
              affineExactlyOneSeedCarrierRevSteps
                labelWidth stateWidth cellCounts rest := by rfl
        _ ≤ 4 * (seed.height + seed.start + seed.rowBase + rowLength + 5) +
              (4 * restLength + 2) :=
          Nat.add_le_add hone (by simpa [restLength] using ih)
        _ = 4 * (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
              labelWidth stateWidth cellCounts (seed :: rest)).length + 2 := by
          simp [encodeAffineExactlyOneStructuredRowSeedMarkedFamily,
            encodeAffineExactlyOneStructuredRowSeed_length,
            rowLength, restLength]
          omega

/-- Concrete linear-time TM2 for the seed-carrier re-encoding. -/
noncomputable def affineExactlyOneSeedCarrierRev_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
        labelWidth stateWidth cellCounts)
      id
      (fun seeds : List AffineExactlyOneStructuredRowSeed =>
        (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse) := by
  exact
    { tm := compile affineExactlyOneSeedCarrierRevProgram
      inputAlphabet := Equiv.refl _
      outputAlphabet := Equiv.refl _
      time := Polynomial.C 4 * Polynomial.X + 2
      outputsFun := fun seeds => by
        have builderRun := affineExactlyOneSeedCarrierRev_run
          labelWidth stateWidth cellCounts seeds
        have compiledRun := compile_evalsToInTime
          affineExactlyOneSeedCarrierRevProgram builderRun
        have machineRun : _root_.StateTransition.EvalsToInTime
            (compile affineExactlyOneSeedCarrierRevProgram).step
            (_root_.Turing.initList
              (compile affineExactlyOneSeedCarrierRevProgram)
              (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
                labelWidth stateWidth cellCounts seeds))
            (some (_root_.Turing.haltList
              (compile affineExactlyOneSeedCarrierRevProgram)
              ((encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
                labelWidth stateWidth cellCounts seeds).reverse)))
            (affineExactlyOneSeedCarrierRevSteps
              labelWidth stateWidth cellCounts seeds) := by
          simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
        have htime : affineExactlyOneSeedCarrierRevSteps
            labelWidth stateWidth cellCounts seeds ≤
            (Polynomial.C 4 * Polynomial.X + 2).eval
              (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
                labelWidth stateWidth cellCounts seeds).length := by
          simpa only [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, Polynomial.eval_C,
            Polynomial.eval_ofNat] using
            affineExactlyOneSeedCarrierRev_steps_le
              labelWidth stateWidth cellCounts seeds
        have boundedRun : _root_.StateTransition.EvalsToInTime
            (compile affineExactlyOneSeedCarrierRevProgram).step
            (_root_.Turing.initList
              (compile affineExactlyOneSeedCarrierRevProgram)
              (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
                labelWidth stateWidth cellCounts seeds))
            (some (_root_.Turing.haltList
              (compile affineExactlyOneSeedCarrierRevProgram)
              ((encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
                labelWidth stateWidth cellCounts seeds).reverse)))
            ((Polynomial.C 4 * Polynomial.X + 2).eval
              (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
                labelWidth stateWidth cellCounts seeds).length) :=
          ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
        simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun }

end CLRS.Chapter34.Turing.PolyBuilder
