import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailSourceFamily
import Mathlib.Tactic

/-!
# Prefix-preserving family wrapper for compact validity tails

Every row has two already materialized, `frameEnd`-free prefix segments and
one compact invocation of the established continuous validity-tail source.
This fixed wrapper copies the prefix segments, runs the source in place, and
restarts at the next row without an intermediate halt.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private noncomputable instance prefixedTailSourceLabelDecidableEq
    (blankSteps : List Nat) :
    DecidableEq (affineValidityTailSourceRevProgram blankSteps).Label :=
  (affineValidityTailSourceRevProgram blankSteps).labelDecidableEq

private noncomputable instance prefixedTailSourceLabelFintype
    (blankSteps : List Nat) :
    Fintype (affineValidityTailSourceRevProgram blankSteps).Label :=
  (affineValidityTailSourceRevProgram blankSteps).labelFintype

/-- One compact row: two completed prefix segments followed by one tail
source invocation. -/
structure AffineValidityTailPrefixedSourceRow where
  first : List UnaryFrameSym
  second : List UnaryFrameSym
  tail : AffineValidityTailSourceFrame
deriving DecidableEq, Repr

/-- Well-formed row family for one fixed verifier machine. -/
structure AffineValidityTailPrefixedSourceFamily
    (blankSteps : List Nat) where
  rows : List AffineValidityTailPrefixedSourceRow
  first_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.first,
    symbol ≠ UnaryFrameSym.frameEnd
  second_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.second,
    symbol ≠ UnaryFrameSym.frameEnd
  stack_lengths : ∀ row ∈ rows,
    row.tail.stackSeeds.length = blankSteps.length

/-- Compact physical input, with the two prefix boundaries retained. -/
def encodeAffineValidityTailPrefixedSourceInput
    {blankSteps : List Nat}
    (family : AffineValidityTailPrefixedSourceFamily blankSteps) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row.first ++ [.frameEnd] ++ row.second ++ [.frameEnd] ++
      encodeAffineValidityTailSourceInvocation row.tail

/-- Fully expanded row stream. -/
def encodeAffineValidityTailPrefixedSourceOutput
    (blankSteps : List Nat)
    (family : AffineValidityTailPrefixedSourceFamily blankSteps) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row.first ++ [.frameEnd] ++ row.second ++ [.frameEnd] ++
      encodeAffineValidityTailFrame
        (affineValidityTailSourceFrame blankSteps row.tail)

/-- Copy phases around the relabeled one-row tail source. -/
inductive AffineValidityTailPrefixedSourceLabel (blankSteps : List Nat)
  | first
  | emitFirst (symbol : UnaryFrameSym)
  | emitFirstEnd
  | second
  | emitSecond (symbol : UnaryFrameSym)
  | emitSecondEnd
  | clearPrefixBuffer
  | body (label : (affineValidityTailSourceRevProgram blankSteps).Label)
  | finish
  | invalid
deriving DecidableEq, Fintype

private def prefixedTailSourceRelabelOp {blankSteps : List Nat} :
    Op UnaryFrameSym UnaryFrameSym
        (affineValidityTailSourceRevProgram blankSteps).Label →
      Op UnaryFrameSym UnaryFrameSym
        (AffineValidityTailPrefixedSourceLabel blankSteps)
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

/-- One continuous fixed controller for every prefixed compact row family. -/
def affineValidityTailPrefixedSourceRevProgram (blankSteps : List Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineValidityTailPrefixedSourceLabel blankSteps
  main := .first
  op
    | .first => .popInput .finish fun
        | .frameEnd => .emitFirstEnd
        | symbol => .emitFirst symbol
    | .emitFirst symbol => .pushOutput symbol .first
    | .emitFirstEnd => .pushOutput .frameEnd .second
    | .second => .popInput .invalid fun
        | .frameEnd => .emitSecondEnd
        | symbol => .emitSecond symbol
    | .emitSecond symbol => .pushOutput symbol .second
    | .emitSecondEnd => .pushOutput .frameEnd .clearPrefixBuffer
    | .clearPrefixBuffer => .popWork₁
        (.body (affineValidityTailSourceRevProgram blankSteps).main)
        (fun _ => .invalid)
    | .body (.inr .finish) => .popWork₁ .first (fun _ => .first)
    | .body label => prefixedTailSourceRelabelOp
        ((affineValidityTailSourceRevProgram blankSteps).op label)
    | .finish => .halt
    | .invalid => .halt

private def affineValidityTailPrefixedSourceCfg {blankSteps : List Nat}
    (label : AffineValidityTailPrefixedSourceLabel blankSteps)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineValidityTailPrefixedSourceRevProgram blankSteps) where
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

/-- Clean row-family entry. -/
def affineValidityTailPrefixedSourceLoopCfg (blankSteps : List Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineValidityTailPrefixedSourceRevProgram blankSteps) :=
  affineValidityTailPrefixedSourceCfg .first none none false
    input output [] [] [] [] []

/-- Clean family pre-halt state. -/
def affineValidityTailPrefixedSourceFinishCfg (blankSteps : List Nat)
    (output : List UnaryFrameSym) :
    BuilderCfg (affineValidityTailPrefixedSourceRevProgram blankSteps) :=
  affineValidityTailPrefixedSourceCfg .finish none none false
    [] output [] [] [] [] []

private def liftPrefixedTailSourceBodyCfg {blankSteps : List Nat}
    (c : BuilderCfg (affineValidityTailSourceRevProgram blankSteps)) :
    BuilderCfg (affineValidityTailPrefixedSourceRevProgram blankSteps) where
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

private theorem prefixedTailSourceRelabel_stepOp
    {blankSteps : List Nat}
    (op : Op UnaryFrameSym UnaryFrameSym
      (affineValidityTailSourceRevProgram blankSteps).Label)
    (c : BuilderCfg (affineValidityTailSourceRevProgram blankSteps)) :
    stepOp (prefixedTailSourceRelabelOp op)
        (liftPrefixedTailSourceBodyCfg c) =
      liftPrefixedTailSourceBodyCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [prefixedTailSourceRelabelOp,
      liftPrefixedTailSourceBodyCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private def prefixedTailSourceExitLabel (blankSteps : List Nat) :
    (affineValidityTailSourceRevProgram blankSteps).Label :=
  .inr (.finish : AffineValidityFinalConjunctionSourceLabel blankSteps.length)

private theorem affineValidityTailPrefixedSource_op_body
    (blankSteps : List Nat)
    (label : (affineValidityTailSourceRevProgram blankSteps).Label)
    (hexit : label ≠ prefixedTailSourceExitLabel blankSteps) :
    (affineValidityTailPrefixedSourceRevProgram blankSteps).op (.body label) =
      prefixedTailSourceRelabelOp
        ((affineValidityTailSourceRevProgram blankSteps).op label) := by
  rcases label with label | label
  · rfl
  · cases label <;>
      simp_all [affineValidityTailPrefixedSourceRevProgram,
        prefixedTailSourceExitLabel]

private theorem liftPrefixedTailSourceBody_step
    {blankSteps : List Nat}
    (c : BuilderCfg (affineValidityTailSourceRevProgram blankSteps))
    (hexit : c.label ≠ some (prefixedTailSourceExitLabel blankSteps)) :
    step (affineValidityTailPrefixedSourceRevProgram blankSteps)
        (liftPrefixedTailSourceBodyCfg c) =
      Option.map liftPrefixedTailSourceBodyCfg
        (step (affineValidityTailSourceRevProgram blankSteps) c) := by
  unfold step
  rw [show (liftPrefixedTailSourceBodyCfg c).label =
      c.label.map .body by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit :
          label ≠ prefixedTailSourceExitLabel blankSteps := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineValidityTailPrefixedSource_op_body
        blankSteps label hlabelExit]
      exact congrArg some
        (prefixedTailSourceRelabel_stepOp
          ((affineValidityTailSourceRevProgram blankSteps).op label) c)

private theorem prefixedTailSource_iterate_bind_none {sigma : Type}
    (f : sigma → Option sigma) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem prefixedTailSource_haltExit_no_return
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
      rw [hnone, prefixedTailSource_iterate_bind_none]
      simp

private theorem prefixedTailSource_lift_iterations_to_finish
    {blankSteps : List Nat}
    {a b : BuilderCfg (affineValidityTailSourceRevProgram blankSteps)}
    (hb : b.label = some (prefixedTailSourceExitLabel blankSteps)) :
    ∀ n : Nat,
    (flip Option.bind
      (step (affineValidityTailSourceRevProgram blankSteps)))^[n]
        (some a) = some b →
      (flip Option.bind
        (step (affineValidityTailPrefixedSourceRevProgram blankSteps)))^[n]
          (some (liftPrefixedTailSourceBodyCfg a)) =
            some (liftPrefixedTailSourceBodyCfg b) := by
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
        (step (affineValidityTailPrefixedSourceRevProgram blankSteps)))^[n]
          (step (affineValidityTailPrefixedSourceRevProgram blankSteps)
            (liftPrefixedTailSourceBodyCfg a)) =
              some (liftPrefixedTailSourceBodyCfg b)
      have haexit :
          a.label ≠ some (prefixedTailSourceExitLabel blankSteps) := by
        intro ha
        exact prefixedTailSource_haltExit_no_return
          (prefixedTailSourceExitLabel blankSteps) rfl a b ha hb n h
      cases hsource : step (affineValidityTailSourceRevProgram blankSteps) a with
      | none =>
          rw [hsource, prefixedTailSource_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := liftPrefixedTailSourceBody_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem prefixedTailSource_first_eval
    (blankSteps : List Nat) (first tail output : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ first,
      symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind
      (step (affineValidityTailPrefixedSourceRevProgram blankSteps)))
        ^[2 * (first.length + 1)]
      (some (affineValidityTailPrefixedSourceLoopCfg blankSteps
        (first ++ .frameEnd :: tail) output)) =
      some (affineValidityTailPrefixedSourceCfg .second
        (some .frameEnd) none false tail
        ((first ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        [] [] [] [] []) := by
  induction first generalizing output with
  | nil =>
      simp only [List.length_nil, zero_add, Nat.mul_one,
        Function.iterate_succ_apply, Function.iterate_zero_apply,
        List.nil_append, List.reverse_singleton, List.singleton_append]
      rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [show 2 * ((symbol :: rest).length + 1) =
          2 * (rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases symbol with
      | frameEnd => exact (hsymbol rfl).elim
      | tick =>
          change
            (flip Option.bind
              (step (affineValidityTailPrefixedSourceRevProgram
                blankSteps)))^[2 * (rest.length + 1)]
              (some (affineValidityTailPrefixedSourceLoopCfg blankSteps
                (rest ++ .frameEnd :: tail) (.tick :: output))) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih (.tick :: output) hrest
      | separator =>
          change
            (flip Option.bind
              (step (affineValidityTailPrefixedSourceRevProgram
                blankSteps)))^[2 * (rest.length + 1)]
              (some (affineValidityTailPrefixedSourceLoopCfg blankSteps
                (rest ++ .frameEnd :: tail) (.separator :: output))) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih (.separator :: output) hrest

private theorem prefixedTailSource_second_eval
    (blankSteps : List Nat) (second tail output : List UnaryFrameSym)
    (buffer₁ : Option UnaryFrameSym)
    (hfree : ∀ symbol ∈ second,
      symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind
      (step (affineValidityTailPrefixedSourceRevProgram blankSteps)))
        ^[2 * (second.length + 1) + 1]
      (some (affineValidityTailPrefixedSourceCfg .second
        buffer₁ none false
        (second ++ .frameEnd :: tail) output [] [] [] [] [])) =
      some (liftPrefixedTailSourceBodyCfg
        (affineValidityTailSourceLoopCfg blankSteps tail
          ((second ++ [UnaryFrameSym.frameEnd]).reverse ++ output))) := by
  induction second generalizing buffer₁ output with
  | nil =>
      simp only [List.length_nil, zero_add, Nat.mul_one,
        Function.iterate_succ_apply, Function.iterate_zero_apply,
        List.nil_append, List.reverse_singleton, List.singleton_append]
      rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [show 2 * ((symbol :: rest).length + 1) + 1 =
          (2 * (rest.length + 1) + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases symbol with
      | frameEnd => exact (hsymbol rfl).elim
      | tick =>
          change
            (flip Option.bind
              (step (affineValidityTailPrefixedSourceRevProgram
                blankSteps)))^[2 * (rest.length + 1) + 1]
              (some (affineValidityTailPrefixedSourceCfg .second
                (some .tick) none false
                (rest ++ .frameEnd :: tail) (.tick :: output)
                [] [] [] [] [])) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih (.tick :: output) (some .tick) hrest
      | separator =>
          change
            (flip Option.bind
              (step (affineValidityTailPrefixedSourceRevProgram
                blankSteps)))^[2 * (rest.length + 1) + 1]
              (some (affineValidityTailPrefixedSourceCfg .second
                (some .separator) none false
                (rest ++ .frameEnd :: tail) (.separator :: output)
                [] [] [] [] [])) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih (.separator :: output) (some .separator) hrest

private def prefixedTailSource_body_run
    (blankSteps : List Nat) (frame : AffineValidityTailSourceFrame)
    (tail output : List UnaryFrameSym)
    (hlength : frame.stackSeeds.length = blankSteps.length) :
    EvalsToInTime
      (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
      (liftPrefixedTailSourceBodyCfg
        (affineValidityTailSourceLoopCfg blankSteps
          (encodeAffineValidityTailSourceInvocation frame ++ tail) output))
      (some (liftPrefixedTailSourceBodyCfg
        (affineValidityTailSourceFinishCfg blankSteps tail
          ((encodeAffineValidityTailFrame
            (affineValidityTailSourceFrame blankSteps frame)).reverse ++
              output))))
      (affineValidityTailSourceSteps blankSteps frame) := by
  have sourceRun := affineValidityTailSource_runToFinish
    blankSteps frame tail output hlength
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact prefixedTailSource_lift_iterations_to_finish rfl
    sourceRun.steps sourceRun.evals_in_steps

private def prefixedTailSource_bridge_run
    (blankSteps : List Nat) (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
      (liftPrefixedTailSourceBodyCfg
        (affineValidityTailSourceFinishCfg blankSteps tail output))
      (some (affineValidityTailPrefixedSourceLoopCfg
        blankSteps tail output)) 1 := by
  exact ⟨⟨1, rfl⟩, le_rfl⟩

/-- Exact pre-halt runtime of a prefixed compact family. -/
def affineValidityTailPrefixedSourceStepsToFinish
    (blankSteps : List Nat) :
    List AffineValidityTailPrefixedSourceRow → Nat
  | [] => 1
  | row :: rest =>
      2 * (row.first.length + 1) +
        (2 * (row.second.length + 1) + 1) +
        affineValidityTailSourceSteps blankSteps row.tail + 1 +
        affineValidityTailPrefixedSourceStepsToFinish blankSteps rest

/-- Exact continuous family execution. -/
def affineValidityTailPrefixedSource_runToFinish
    (blankSteps : List Nat)
    (rows : List AffineValidityTailPrefixedSourceRow)
    (output : List UnaryFrameSym)
    (hfirst : ∀ row ∈ rows, ∀ symbol ∈ row.first,
      symbol ≠ UnaryFrameSym.frameEnd)
    (hsecond : ∀ row ∈ rows, ∀ symbol ∈ row.second,
      symbol ≠ UnaryFrameSym.frameEnd)
    (hlength : ∀ row ∈ rows,
      row.tail.stackSeeds.length = blankSteps.length) :
    EvalsToInTime
      (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
      (affineValidityTailPrefixedSourceLoopCfg blankSteps
        (rows.flatMap fun row =>
          row.first ++ [.frameEnd] ++ row.second ++ [.frameEnd] ++
            encodeAffineValidityTailSourceInvocation row.tail)
        output)
      (some (affineValidityTailPrefixedSourceFinishCfg blankSteps
        ((rows.flatMap fun row =>
          row.first ++ [.frameEnd] ++ row.second ++ [.frameEnd] ++
            encodeAffineValidityTailFrame
              (affineValidityTailSourceFrame blankSteps row.tail)).reverse ++
          output)))
      (affineValidityTailPrefixedSourceStepsToFinish blankSteps rows) := by
  induction rows generalizing output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons row rest ih =>
      let restInput := rest.flatMap fun item =>
        item.first ++ [.frameEnd] ++ item.second ++ [.frameEnd] ++
          encodeAffineValidityTailSourceInvocation item.tail
      let tailInput :=
        encodeAffineValidityTailSourceInvocation row.tail ++ restInput
      let afterFirstInput := row.second ++ .frameEnd :: tailInput
      let firstOutput :=
        (row.first ++ [UnaryFrameSym.frameEnd]).reverse ++ output
      let secondOutput :=
        (row.second ++ [UnaryFrameSym.frameEnd]).reverse ++ firstOutput
      let rowOutput :=
        (encodeAffineValidityTailFrame
          (affineValidityTailSourceFrame blankSteps row.tail)).reverse ++
            secondOutput
      have hfirstRun := prefixedTailSource_first_eval
        blankSteps row.first afterFirstInput output
        (hfirst row (by simp))
      have hsecondRun := prefixedTailSource_second_eval
        blankSteps row.second tailInput firstOutput (some .frameEnd)
        (hsecond row (by simp))
      have hbodyRun := prefixedTailSource_body_run
        blankSteps row.tail restInput secondOutput
        (hlength row (by simp))
      have hbridgeRun := prefixedTailSource_bridge_run
        blankSteps restInput rowOutput
      have hrestRun := ih rowOutput
        (fun item hitem => hfirst item (by simp [hitem]))
        (fun item hitem => hsecond item (by simp [hitem]))
        (fun item hitem => hlength item (by simp [hitem]))
      let h₁ := EvalsToInTime.trans
        (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
        _ _ _ _ _ ⟨⟨_, hfirstRun⟩, le_rfl⟩
          ⟨⟨_, hsecondRun⟩, le_rfl⟩
      let h₂ := EvalsToInTime.trans
        (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
        _ _ _ _ _ h₁ hbodyRun
      let h₃ := EvalsToInTime.trans
        (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
        _ _ _ _ _ h₂ hbridgeRun
      let full := EvalsToInTime.trans
        (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
        _ _ _ _ _ h₃ hrestRun
      convert full using 1
      · simp [restInput, afterFirstInput, tailInput, List.append_assoc]
      · simp [rowOutput, secondOutput, firstOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineValidityTailPrefixedSourceStepsToFinish]
        omega

/-- Fixed coefficient for the prefixed wrapper's quadratic bound. -/
def affineValidityTailPrefixedSourceStepCoeff
    (blankSteps : List Nat) : Nat :=
  affineValidityTailSourceStepCoeff blankSteps + 6

/-- The complete prefixed family run is quadratic in its compact physical
input. -/
theorem affineValidityTailPrefixedSourceStepsToFinish_le
    (blankSteps : List Nat)
    (rows : List AffineValidityTailPrefixedSourceRow)
    (hlength : ∀ row ∈ rows,
      row.tail.stackSeeds.length = blankSteps.length) :
    affineValidityTailPrefixedSourceStepsToFinish blankSteps rows ≤
      affineValidityTailPrefixedSourceStepCoeff blankSteps *
        (rows.flatMap fun row =>
          row.first ++ [.frameEnd] ++ row.second ++ [.frameEnd] ++
            encodeAffineValidityTailSourceInvocation row.tail).length ^ 2 +
          1 := by
  induction rows with
  | nil => simp [affineValidityTailPrefixedSourceStepsToFinish]
  | cons row rest ih =>
      let invocationLength :=
        (encodeAffineValidityTailSourceInvocation row.tail).length
      let headLength :=
        row.first.length + 1 + row.second.length + 1 + invocationLength
      let restLength :=
        (rest.flatMap fun item =>
          item.first ++ [.frameEnd] ++ item.second ++ [.frameEnd] ++
            encodeAffineValidityTailSourceInvocation item.tail).length
      let sourceCoeff := affineValidityTailSourceStepCoeff blankSteps
      let familyCoeff :=
        affineValidityTailPrefixedSourceStepCoeff blankSteps
      have hinvocationPos : 1 ≤ invocationLength := by
        have hpos := encodeAffineValidityTailSourceInvocation_length_pos
          row.tail
        simp only [invocationLength]
        omega
      have hinvocationHead : invocationLength + 1 ≤ headLength := by
        simp only [headLength]
        omega
      have hsource := affineValidityTailSource_steps_le
        blankSteps row.tail (hlength row (by simp))
      have hsourceBound :
          affineValidityTailSourceSteps blankSteps row.tail ≤
            sourceCoeff * headLength ^ 2 := by
        calc
          affineValidityTailSourceSteps blankSteps row.tail ≤
              sourceCoeff * (invocationLength + 1) ^ 2 := by
            simpa [sourceCoeff, invocationLength] using hsource
          _ ≤ sourceCoeff * headLength ^ 2 :=
            Nat.mul_le_mul_left sourceCoeff
              (Nat.pow_le_pow_left hinvocationHead 2)
      have hheadPos : 1 ≤ headLength := by
        simp only [headLength]
        omega
      have hoverhead :
          2 * (row.first.length + 1) +
              (2 * (row.second.length + 1) + 1) + 1 ≤
            6 * headLength ^ 2 := by
        simp only [headLength] at hheadPos ⊢
        nlinarith
      have hheadBound :
          2 * (row.first.length + 1) +
              (2 * (row.second.length + 1) + 1) +
              affineValidityTailSourceSteps blankSteps row.tail + 1 ≤
            familyCoeff * headLength ^ 2 := by
        simp only [familyCoeff,
          affineValidityTailPrefixedSourceStepCoeff]
        nlinarith
      have hrest := ih
        (fun item hitem => hlength item (by simp [hitem]))
      have hrestBound :
          affineValidityTailPrefixedSourceStepsToFinish blankSteps rest ≤
            familyCoeff * restLength ^ 2 + 1 := by
        simpa [familyCoeff, restLength] using hrest
      have hcross : headLength ^ 2 + restLength ^ 2 ≤
          (headLength + restLength) ^ 2 := by
        nlinarith [Nat.zero_le (2 * headLength * restLength)]
      have hencodedLength :
          ((row :: rest).flatMap fun item =>
            item.first ++ [.frameEnd] ++ item.second ++ [.frameEnd] ++
              encodeAffineValidityTailSourceInvocation item.tail).length =
            headLength + restLength := by
        simp [headLength, restLength, invocationLength,
          List.append_assoc]
        omega
      calc
        affineValidityTailPrefixedSourceStepsToFinish blankSteps
            (row :: rest) =
            2 * (row.first.length + 1) +
              (2 * (row.second.length + 1) + 1) +
              affineValidityTailSourceSteps blankSteps row.tail + 1 +
              affineValidityTailPrefixedSourceStepsToFinish
                blankSteps rest := rfl
        _ ≤ familyCoeff * headLength ^ 2 +
              (familyCoeff * restLength ^ 2 + 1) := by
            omega
        _ = familyCoeff * (headLength ^ 2 + restLength ^ 2) + 1 := by
            ring
        _ ≤ familyCoeff * (headLength + restLength) ^ 2 + 1 :=
            Nat.add_le_add_right
              (Nat.mul_le_mul_left familyCoeff hcross) 1
        _ = affineValidityTailPrefixedSourceStepCoeff blankSteps *
              ((row :: rest).flatMap fun item =>
                item.first ++ [.frameEnd] ++ item.second ++ [.frameEnd] ++
                  encodeAffineValidityTailSourceInvocation
                    item.tail).length ^ 2 + 1 := by
            rw [hencodedLength]

/-- Reverse-output polynomial-time interface. -/
noncomputable def
    affineValidityTailPrefixedSourceRev_computableInPolyTime
    (blankSteps : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineValidityTailPrefixedSourceInput id
      (fun family : AffineValidityTailPrefixedSourceFamily blankSteps =>
        (encodeAffineValidityTailPrefixedSourceOutput
          blankSteps family).reverse) where
  tm := compile (affineValidityTailPrefixedSourceRevProgram blankSteps)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C
      (affineValidityTailPrefixedSourceStepCoeff blankSteps) *
    Polynomial.X ^ 2 + 2
  outputsFun := fun family => by
    have finishRun := affineValidityTailPrefixedSource_runToFinish
      blankSteps family.rows [] family.first_frameEnd_free
        family.second_frameEnd_free family.stack_lengths
    have haltStep : EvalsToInTime
        (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
        (affineValidityTailPrefixedSourceFinishCfg blankSteps
          (encodeAffineValidityTailPrefixedSourceOutput
            blankSteps family).reverse)
        (some (haltCfg
          (affineValidityTailPrefixedSourceRevProgram blankSteps)
          (encodeAffineValidityTailPrefixedSourceOutput
            blankSteps family).reverse)) 1 :=
      ⟨⟨1, rfl⟩, le_rfl⟩
    have builderRun := EvalsToInTime.trans
      (step (affineValidityTailPrefixedSourceRevProgram blankSteps))
      _ 1 _ _ _ (by
        simpa [encodeAffineValidityTailPrefixedSourceInput,
          encodeAffineValidityTailPrefixedSourceOutput] using finishRun)
        haltStep
    have compiledRun := compile_evalsToInTime
      (affineValidityTailPrefixedSourceRevProgram blankSteps) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile
          (affineValidityTailPrefixedSourceRevProgram blankSteps)).step
        (_root_.Turing.initList
          (compile
            (affineValidityTailPrefixedSourceRevProgram blankSteps))
          (encodeAffineValidityTailPrefixedSourceInput family))
        (some (_root_.Turing.haltList
          (compile
            (affineValidityTailPrefixedSourceRevProgram blankSteps))
          (encodeAffineValidityTailPrefixedSourceOutput
            blankSteps family).reverse))
        (affineValidityTailPrefixedSourceStepsToFinish
          blankSteps family.rows + 1) := by
      have hinput :
          (family.rows.flatMap fun row =>
            row.first ++ .frameEnd ::
              (row.second ++ .frameEnd ::
                encodeAffineValidityTailSourceInvocation row.tail)) =
            encodeAffineValidityTailPrefixedSourceInput family := by
        simp [encodeAffineValidityTailPrefixedSourceInput,
          List.append_assoc]
      rw [hinput] at compiledRun
      have hinitial :
          affineValidityTailPrefixedSourceLoopCfg blankSteps
              (encodeAffineValidityTailPrefixedSourceInput family) [] =
            initialCfg
              (affineValidityTailPrefixedSourceRevProgram blankSteps)
              (encodeAffineValidityTailPrefixedSourceInput family) :=
        rfl
      rw [hinitial] at compiledRun
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        Nat.add_comm] using compiledRun
    have htime :
        affineValidityTailPrefixedSourceStepsToFinish
              blankSteps family.rows + 1 ≤
          (Polynomial.C
              (affineValidityTailPrefixedSourceStepCoeff blankSteps) *
            Polynomial.X ^ 2 + 2).eval
              (encodeAffineValidityTailPrefixedSourceInput family).length := by
      have hbound := affineValidityTailPrefixedSourceStepsToFinish_le
        blankSteps family.rows family.stack_lengths
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_ofNat]
      unfold encodeAffineValidityTailPrefixedSourceInput
      omega
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile
          (affineValidityTailPrefixedSourceRevProgram blankSteps)).step
        (_root_.Turing.initList
          (compile
            (affineValidityTailPrefixedSourceRevProgram blankSteps))
          (encodeAffineValidityTailPrefixedSourceInput family))
        (some (_root_.Turing.haltList
          (compile
            (affineValidityTailPrefixedSourceRevProgram blankSteps))
          (encodeAffineValidityTailPrefixedSourceOutput
            blankSteps family).reverse))
        ((Polynomial.C
              (affineValidityTailPrefixedSourceStepCoeff blankSteps) *
            Polynomial.X ^ 2 + 2).eval
              (encodeAffineValidityTailPrefixedSourceInput family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-output polynomial-time interface. -/
noncomputable def affineValidityTailPrefixedSource_computableInPolyTime
    (blankSteps : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineValidityTailPrefixedSourceInput id
      (fun family : AffineValidityTailPrefixedSourceFamily blankSteps =>
        encodeAffineValidityTailPrefixedSourceOutput blankSteps family) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineValidityTailPrefixedSourceRev_computableInPolyTime blankSteps)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
