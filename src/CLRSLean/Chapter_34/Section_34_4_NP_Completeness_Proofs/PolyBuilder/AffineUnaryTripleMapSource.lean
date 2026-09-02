import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLoader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Fixed affine maps over unary triples

Cook--Levin row sources repeatedly have to derive verifier-fixed affine wire
indices from the runtime triple `(height, gateStart, rowBase)`.  This module
provides that operation once as a concrete TM2 source.  Coefficients and
constants live in finite control; the three arguments remain unary tape data.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- One nonnegative affine form in three runtime variables. -/
structure AffineUnaryTripleForm where
  constant : Nat
  first : Nat
  second : Nat
  third : Nat
deriving DecidableEq, Repr

/-- Runtime triple consumed by the fixed affine-map source. -/
structure AffineUnaryTripleSeed where
  first : Nat
  second : Nat
  third : Nat
deriving DecidableEq, Repr

/-- Semantic value of one verifier-fixed affine form. -/
def affineUnaryTripleFormValue (form : AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) : Nat :=
  form.constant + form.first * seed.first + form.second * seed.second +
    form.third * seed.third

/-- Values emitted for one runtime triple. -/
def affineUnaryTripleMap (forms : List AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) : List Nat :=
  forms.map fun form => affineUnaryTripleFormValue form seed

/-- Canonical three-field seed encoding. -/
def encodeAffineUnaryTripleSeed (seed : AffineUnaryTripleSeed) :
    List UnaryFrameSym :=
  encodeUnaryFrame [seed.first, seed.second, seed.third]

/-- Concatenated seed family, with no oracle-side delimiter. -/
def encodeAffineUnaryTripleSeedFamily :
    List AffineUnaryTripleSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      encodeAffineUnaryTripleSeed seed ++
        encodeAffineUnaryTripleSeedFamily rest

/-- Row-major affine image of a seed family. -/
def affineUnaryTripleMapFamily (forms : List AffineUnaryTripleForm)
    (seeds : List AffineUnaryTripleSeed) : List Nat :=
  seeds.flatMap (affineUnaryTripleMap forms)

private inductive AffineUnaryTripleMapPhase
  | constant | first | second | third
deriving DecidableEq, Fintype

private def affineUnaryTripleMapCoefficient
    (phase : AffineUnaryTripleMapPhase) (form : AffineUnaryTripleForm) : Nat :=
  match phase with
  | .constant => form.constant
  | .first => form.first
  | .second => form.second
  | .third => form.third

private def AffineUnaryTripleMapCursor
    (forms : List AffineUnaryTripleForm)
    (phase : AffineUnaryTripleMapPhase) :=
  Σ index : Fin forms.length,
    Fin (affineUnaryTripleMapCoefficient phase (forms.get index) + 1)

private instance (forms : List AffineUnaryTripleForm)
    (phase : AffineUnaryTripleMapPhase) :
    Fintype (AffineUnaryTripleMapCursor forms phase) := by
  unfold AffineUnaryTripleMapCursor
  infer_instance

private inductive AffineUnaryTripleMapLabel
    (forms : List AffineUnaryTripleForm)
  | loader (label : UnaryTripleLoaderLabel)
  | repeat (phase : AffineUnaryTripleMapPhase)
      (cursor : AffineUnaryTripleMapCursor forms phase)
  | emit (phase : AffineUnaryTripleMapPhase)
      (cursor : AffineUnaryTripleMapCursor forms phase)
  | save (phase : AffineUnaryTripleMapPhase)
      (cursor : AffineUnaryTripleMapCursor forms phase)
  | pushTick (phase : AffineUnaryTripleMapPhase)
      (cursor : AffineUnaryTripleMapCursor forms phase)
  | restore (phase : AffineUnaryTripleMapPhase)
      (cursor : AffineUnaryTripleMapCursor forms phase)
  | restoreInc (phase : AffineUnaryTripleMapPhase)
      (cursor : AffineUnaryTripleMapCursor forms phase)
  | pushSeparator (index : Fin forms.length)
  | clearBuffer | clearFirst | clearSecond | clearThird
  | finish | invalid
deriving Fintype

private noncomputable instance (forms : List AffineUnaryTripleForm) :
    DecidableEq (AffineUnaryTripleMapLabel forms) := Classical.decEq _

private def affineUnaryTripleMapCursorStart
    (forms : List AffineUnaryTripleForm)
    (phase : AffineUnaryTripleMapPhase) (index : Fin forms.length) :
    AffineUnaryTripleMapCursor forms phase :=
  ⟨index, ⟨affineUnaryTripleMapCoefficient phase (forms.get index), by omega⟩⟩

private def affineUnaryTripleMapCursorPred
    {forms : List AffineUnaryTripleForm}
    {phase : AffineUnaryTripleMapPhase}
    (cursor : AffineUnaryTripleMapCursor forms phase)
    (hpositive : cursor.2.val ≠ 0) :
    AffineUnaryTripleMapCursor forms phase :=
  ⟨cursor.1, ⟨cursor.2.val - 1, by omega⟩⟩

private def affineUnaryTripleMapStartLabel
    (forms : List AffineUnaryTripleForm) :
    AffineUnaryTripleMapLabel forms :=
  if h : 0 < forms.length then
    .repeat .constant
      (affineUnaryTripleMapCursorStart forms .constant ⟨0, h⟩)
  else
    .clearBuffer

private def affineUnaryTripleMapAfterPhase
    (forms : List AffineUnaryTripleForm)
    (phase : AffineUnaryTripleMapPhase) (index : Fin forms.length) :
    AffineUnaryTripleMapLabel forms :=
  match phase with
  | .constant => .repeat .first
      (affineUnaryTripleMapCursorStart forms .first index)
  | .first => .repeat .second
      (affineUnaryTripleMapCursorStart forms .second index)
  | .second => .repeat .third
      (affineUnaryTripleMapCursorStart forms .third index)
  | .third => .pushSeparator index

private def affineUnaryTripleMapAfterField
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length) :
    AffineUnaryTripleMapLabel forms :=
  if h : index.val + 1 < forms.length then
    .repeat .constant
      (affineUnaryTripleMapCursorStart forms .constant
        ⟨index.val + 1, h⟩)
  else
    .clearBuffer

private def affineUnaryTripleMapRelabelOp {Γ Δ Λ Μ : Type}
    (tag : Λ → Μ) : Op Γ Δ Λ → Op Γ Δ Μ
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

/-- Fixed controller.  The list of forms is part of finite control. -/
def affineUnaryTripleMapFamilyRevProgram
    (forms : List AffineUnaryTripleForm) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineUnaryTripleMapLabel forms
  main := .loader .load₁
  op
    | .loader .ready => .popWork₁
        (affineUnaryTripleMapStartLabel forms) (fun _ => .invalid)
    | .loader label => affineUnaryTripleMapRelabelOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label)
    | .repeat phase cursor =>
        if hzero : cursor.2.val = 0 then
          .jump (affineUnaryTripleMapAfterPhase forms phase cursor.1)
        else match phase with
          | .constant => .pushOutput .tick
              (.repeat .constant
                (affineUnaryTripleMapCursorPred cursor hzero))
          | .first => .jump (.emit .first
              (affineUnaryTripleMapCursorPred cursor hzero))
          | .second => .jump (.emit .second
              (affineUnaryTripleMapCursorPred cursor hzero))
          | .third => .jump (.emit .third
              (affineUnaryTripleMapCursorPred cursor hzero))
    | .emit .constant _ => .jump .invalid
    | .emit .first cursor => .dec₁ (.restore .first cursor)
        (.save .first cursor)
    | .emit .second cursor => .dec₂ (.restore .second cursor)
        (.save .second cursor)
    | .emit .third cursor => .dec₃ (.restore .third cursor)
        (.save .third cursor)
    | .save phase cursor => .pushWork₁ .tick (.pushTick phase cursor)
    | .pushTick phase cursor => .pushOutput .tick (.emit phase cursor)
    | .restore phase cursor => .popWork₁
        (.repeat phase cursor)
        (fun _ => .restoreInc phase cursor)
    | .restoreInc .constant _ => .jump .invalid
    | .restoreInc .first cursor => .inc₁ (.restore .first cursor)
    | .restoreInc .second cursor => .inc₂ (.restore .second cursor)
    | .restoreInc .third cursor => .inc₃ (.restore .third cursor)
    | .pushSeparator index => .pushOutput .separator
        (affineUnaryTripleMapAfterField forms index)
    | .clearBuffer => .popWork₁ .clearFirst (fun _ => .invalid)
    | .clearFirst => .dec₁ .clearSecond .clearFirst
    | .clearSecond => .dec₂ .clearThird .clearSecond
    | .clearThird => .dec₃ (.loader .load₁) .clearThird
    | .finish => .halt
    | .invalid => .halt

private def affineUnaryTripleMapFamilyCfg
    {forms : List AffineUnaryTripleForm}
    (label : AffineUnaryTripleMapLabel forms)
    (buffer₁ : Option UnaryFrameSym) (input output work₁ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineUnaryTripleMapFamilyRevProgram forms) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := work₁
  work₂ := []
  counter₁ := first
  counter₂ := second
  counter₃ := third

/-- Clean entry before the next encoded unary triple. -/
def affineUnaryTripleMapFamilyLoopCfg
    (forms : List AffineUnaryTripleForm)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineUnaryTripleMapFamilyRevProgram forms) :=
  affineUnaryTripleMapFamilyCfg (.loader .load₁) none input output [] [] [] []

private def affineUnaryTripleMapRelabelCfg
    {Γ Δ : Type} {P Q : Program Γ Δ} (tag : P.Label → Q.Label)
    (c : BuilderCfg P) : BuilderCfg Q where
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

private def liftAffineUnaryTripleMapLoaderCfg
    {forms : List AffineUnaryTripleForm}
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym)) :
    BuilderCfg (affineUnaryTripleMapFamilyRevProgram forms) :=
  affineUnaryTripleMapRelabelCfg .loader c

private theorem affineUnaryTripleMapRelabel_stepOp
    {Γ Δ : Type} {P Q : Program Γ Δ} (tag : P.Label → Q.Label)
    (op : Op Γ Δ P.Label) (c : BuilderCfg P) :
    stepOp (affineUnaryTripleMapRelabelOp tag op)
        (affineUnaryTripleMapRelabelCfg tag c) =
      affineUnaryTripleMapRelabelCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [affineUnaryTripleMapRelabelOp,
      affineUnaryTripleMapRelabelCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineUnaryTripleMap_op_loader
    {forms : List AffineUnaryTripleForm}
    (label : UnaryTripleLoaderLabel) (hexit : label ≠ .ready) :
    (affineUnaryTripleMapFamilyRevProgram forms).op (.loader label) =
      affineUnaryTripleMapRelabelOp .loader
        ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) := by
  cases label <;>
    simp_all [affineUnaryTripleMapFamilyRevProgram] <;> rfl

private theorem liftAffineUnaryTripleMapLoader_step
    {forms : List AffineUnaryTripleForm}
    (c : BuilderCfg (unaryTripleLoaderProgramFor UnaryFrameSym))
    (hexit : c.label ≠ some .ready) :
    step (affineUnaryTripleMapFamilyRevProgram forms)
        (liftAffineUnaryTripleMapLoaderCfg c) =
      Option.map liftAffineUnaryTripleMapLoaderCfg
        (step (unaryTripleLoaderProgramFor UnaryFrameSym) c) := by
  unfold step
  rw [show (liftAffineUnaryTripleMapLoaderCfg c).label =
    c.label.map .loader by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .ready := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineUnaryTripleMap_op_loader label hlabelExit]
      exact congrArg some
        (affineUnaryTripleMapRelabel_stepOp
          (Q := affineUnaryTripleMapFamilyRevProgram forms) .loader
          ((unaryTripleLoaderProgramFor UnaryFrameSym).op label) c)

private theorem affineUnaryTripleMap_iterate_bind_none {σ : Type}
    (f : σ → Option σ) : ∀ n : Nat,
    (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem affineUnaryTripleMap_haltExit_no_return
    {Γ Δ : Type} {P : Program Γ Δ} (exit : P.Label)
    (hop : P.op exit = Op.halt) (a b : BuilderCfg P)
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
      rw [hnone, affineUnaryTripleMap_iterate_bind_none]
      simp

private theorem affineUnaryTripleMap_lift_iterations_to_haltExit
    {Γ Δ : Type} {P Q : Program Γ Δ} (exit : P.Label)
    (hop : P.op exit = Op.halt) (tr : BuilderCfg P → BuilderCfg Q)
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
        exact affineUnaryTripleMap_haltExit_no_return
          exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, affineUnaryTripleMap_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineUnaryTripleMap_loader_run
    {forms : List AffineUnaryTripleForm}
    (seed : AffineUnaryTripleSeed) (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyLoopCfg forms
        (encodeAffineUnaryTripleSeed seed ++ tail) output)
      (some (liftAffineUnaryTripleMapLoaderCfg
        (unaryTripleLoaderReadyCfgFor seed.first seed.second seed.third
          tail output [] [])))
      (unaryTripleLoaderSteps seed.first seed.second seed.third) := by
  have sourceRun := unaryTripleLoader_runFor
    (Δ := UnaryFrameSym) seed.first seed.second seed.third tail output [] []
  have htarget :
      (unaryTripleLoaderReadyCfgFor seed.first seed.second seed.third
        tail output ([] : List UnaryFrameSym) []).label = some .ready := rfl
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have hstart :
      liftAffineUnaryTripleMapLoaderCfg
          (unaryTripleLoaderCfgFor .load₁ none
            (encodeAffineUnaryTripleSeed seed ++ tail)
            output [] [] [] [] []) =
        affineUnaryTripleMapFamilyLoopCfg forms
          (encodeAffineUnaryTripleSeed seed ++ tail) output := rfl
  rw [← hstart]
  exact affineUnaryTripleMap_lift_iterations_to_haltExit
    UnaryTripleLoaderLabel.ready rfl liftAffineUnaryTripleMapLoaderCfg
    liftAffineUnaryTripleMapLoader_step htarget sourceRun.steps
    sourceRun.evals_in_steps

private theorem affineUnaryTripleMap_replicate_tick_append_cons
    (count : Nat) (tail : List UnaryFrameSym) :
    List.replicate count .tick ++ .tick :: tail =
      .tick :: (List.replicate count .tick ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons .tick) ih

private theorem affineUnaryTripleMap_constant_eval
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (index : Fin forms.length) (remaining : Nat)
    (hremaining : remaining ≤ (forms.get index).constant)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        remaining + 1]
      (some (affineUnaryTripleMapFamilyCfg
        (.repeat .constant
          ⟨index, ⟨remaining, by
            change remaining < (forms.get index).constant + 1
            omega⟩⟩)
        none tail output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))) =
      some (affineUnaryTripleMapFamilyCfg
        (affineUnaryTripleMapAfterPhase forms .constant index)
        none tail (List.replicate remaining .tick ++ output) []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())) := by
  induction remaining generalizing output with
  | zero => rfl
  | succ remaining ih =>
      rw [show remaining + 1 + 1 = (remaining + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
            remaining + 1]
          (some (affineUnaryTripleMapFamilyCfg
            (.repeat .constant
              ⟨index, ⟨remaining, by
                change remaining < (forms.get index).constant + 1
                omega⟩⟩)
            none tail (.tick :: output) []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))) = _
      simpa only [List.replicate_succ, List.cons_append,
        affineUnaryTripleMap_replicate_tick_append_cons] using
        ih (by omega) (.tick :: output)

private theorem affineUnaryTripleMap_replicate_unit_append_cons
    (count : Nat) (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ()) ih

private theorem affineUnaryTripleMap_first_drain_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .first)
    (remaining : Nat) (tail output work : List UnaryFrameSym)
    (second third : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        3 * remaining + 1]
      (some (affineUnaryTripleMapFamilyCfg (.emit .first cursor)
        none tail output work (List.replicate remaining ()) second third)) =
      some (affineUnaryTripleMapFamilyCfg (.restore .first cursor)
        none tail (List.replicate remaining .tick ++ output)
        (List.replicate remaining .tick ++ work) [] second third) := by
  induction remaining generalizing output work with
  | zero => rfl
  | succ remaining ih =>
      rw [show 3 * (remaining + 1) + 1 =
          (3 * remaining + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
            3 * remaining + 1]
          (some (affineUnaryTripleMapFamilyCfg (.emit .first cursor)
            none tail (.tick :: output) (.tick :: work)
            (List.replicate remaining ()) second third)) = _
      simpa only [List.replicate_succ, List.cons_append,
        affineUnaryTripleMap_replicate_tick_append_cons] using
        ih (.tick :: output) (.tick :: work)

private theorem affineUnaryTripleMap_first_restore_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .first)
    (remaining : Nat) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (first second third : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        2 * remaining + 1]
      (some (affineUnaryTripleMapFamilyCfg (.restore .first cursor)
        buffer tail output (List.replicate remaining .tick)
        first second third)) =
      some (affineUnaryTripleMapFamilyCfg (.repeat .first cursor)
        none tail output [] (List.replicate remaining () ++ first)
        second third) := by
  induction remaining generalizing buffer first with
  | zero => rfl
  | succ remaining ih =>
      rw [show 2 * (remaining + 1) + 1 =
          (2 * remaining + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
            2 * remaining + 1]
          (some (affineUnaryTripleMapFamilyCfg (.restore .first cursor)
            (some .tick) tail output (List.replicate remaining .tick)
            (() :: first) second third)) = _
      simpa only [List.replicate_succ, List.cons_append,
        affineUnaryTripleMap_replicate_unit_append_cons] using
        ih (some UnaryFrameSym.tick) (() :: first)

private theorem affineUnaryTripleMap_first_copy_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .first)
    (value : Nat) (tail output : List UnaryFrameSym)
    (second third : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        5 * value + 2]
      (some (affineUnaryTripleMapFamilyCfg (.emit .first cursor)
        none tail output [] (List.replicate value ()) second third)) =
      some (affineUnaryTripleMapFamilyCfg (.repeat .first cursor)
        none tail (List.replicate value .tick ++ output) []
        (List.replicate value ()) second third) := by
  have hdrain := affineUnaryTripleMap_first_drain_eval forms index cursor
    value tail output [] second third
  have hrestore := affineUnaryTripleMap_first_restore_eval forms index cursor
    value tail (List.replicate value .tick ++ output) none [] second third
  simp only [List.append_nil] at hdrain hrestore
  have hsteps : (2 * value + 1) + (3 * value + 1) =
      5 * value + 2 := by omega
  rw [← hsteps]
  exact (EvalsTo.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _
    (⟨3 * value + 1, hdrain⟩ : EvalsTo _ _ _)
    (⟨2 * value + 1, hrestore⟩ : EvalsTo _ _ _)).evals_in_steps

private theorem affineUnaryTripleMap_second_drain_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .second)
    (remaining : Nat) (tail output work : List UnaryFrameSym)
    (first third : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        3 * remaining + 1]
      (some (affineUnaryTripleMapFamilyCfg (.emit .second cursor)
        none tail output work first (List.replicate remaining ()) third)) =
      some (affineUnaryTripleMapFamilyCfg (.restore .second cursor)
        none tail (List.replicate remaining .tick ++ output)
        (List.replicate remaining .tick ++ work) first [] third) := by
  induction remaining generalizing output work with
  | zero => rfl
  | succ remaining ih =>
      rw [show 3 * (remaining + 1) + 1 =
          (3 * remaining + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
            3 * remaining + 1]
          (some (affineUnaryTripleMapFamilyCfg (.emit .second cursor)
            none tail (.tick :: output) (.tick :: work)
            first (List.replicate remaining ()) third)) = _
      simpa only [List.replicate_succ, List.cons_append,
        affineUnaryTripleMap_replicate_tick_append_cons] using
        ih (.tick :: output) (.tick :: work)

private theorem affineUnaryTripleMap_second_restore_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .second)
    (remaining : Nat) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (first second third : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        2 * remaining + 1]
      (some (affineUnaryTripleMapFamilyCfg (.restore .second cursor)
        buffer tail output (List.replicate remaining .tick)
        first second third)) =
      some (affineUnaryTripleMapFamilyCfg (.repeat .second cursor)
        none tail output [] first (List.replicate remaining () ++ second)
        third) := by
  induction remaining generalizing buffer second with
  | zero => rfl
  | succ remaining ih =>
      rw [show 2 * (remaining + 1) + 1 =
          (2 * remaining + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
            2 * remaining + 1]
          (some (affineUnaryTripleMapFamilyCfg (.restore .second cursor)
            (some .tick) tail output (List.replicate remaining .tick)
            first (() :: second) third)) = _
      simpa only [List.replicate_succ, List.cons_append,
        affineUnaryTripleMap_replicate_unit_append_cons] using
        ih (some UnaryFrameSym.tick) (() :: second)

private theorem affineUnaryTripleMap_second_copy_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .second)
    (value : Nat) (tail output : List UnaryFrameSym)
    (first third : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        5 * value + 2]
      (some (affineUnaryTripleMapFamilyCfg (.emit .second cursor)
        none tail output [] first (List.replicate value ()) third)) =
      some (affineUnaryTripleMapFamilyCfg (.repeat .second cursor)
        none tail (List.replicate value .tick ++ output) []
        first (List.replicate value ()) third) := by
  have hdrain := affineUnaryTripleMap_second_drain_eval forms index cursor
    value tail output [] first third
  have hrestore := affineUnaryTripleMap_second_restore_eval forms index cursor
    value tail (List.replicate value .tick ++ output) none first [] third
  simp only [List.append_nil] at hdrain hrestore
  have hsteps : (2 * value + 1) + (3 * value + 1) =
      5 * value + 2 := by omega
  rw [← hsteps]
  exact (EvalsTo.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _
    (⟨3 * value + 1, hdrain⟩ : EvalsTo _ _ _)
    (⟨2 * value + 1, hrestore⟩ : EvalsTo _ _ _)).evals_in_steps

private theorem affineUnaryTripleMap_third_drain_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .third)
    (remaining : Nat) (tail output work : List UnaryFrameSym)
    (first second : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        3 * remaining + 1]
      (some (affineUnaryTripleMapFamilyCfg (.emit .third cursor)
        none tail output work first second (List.replicate remaining ()))) =
      some (affineUnaryTripleMapFamilyCfg (.restore .third cursor)
        none tail (List.replicate remaining .tick ++ output)
        (List.replicate remaining .tick ++ work) first second []) := by
  induction remaining generalizing output work with
  | zero => rfl
  | succ remaining ih =>
      rw [show 3 * (remaining + 1) + 1 =
          (3 * remaining + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
            3 * remaining + 1]
          (some (affineUnaryTripleMapFamilyCfg (.emit .third cursor)
            none tail (.tick :: output) (.tick :: work)
            first second (List.replicate remaining ()))) = _
      simpa only [List.replicate_succ, List.cons_append,
        affineUnaryTripleMap_replicate_tick_append_cons] using
        ih (.tick :: output) (.tick :: work)

private theorem affineUnaryTripleMap_third_restore_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .third)
    (remaining : Nat) (tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (first second third : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        2 * remaining + 1]
      (some (affineUnaryTripleMapFamilyCfg (.restore .third cursor)
        buffer tail output (List.replicate remaining .tick)
        first second third)) =
      some (affineUnaryTripleMapFamilyCfg (.repeat .third cursor)
        none tail output [] first second
        (List.replicate remaining () ++ third)) := by
  induction remaining generalizing buffer third with
  | zero => rfl
  | succ remaining ih =>
      rw [show 2 * (remaining + 1) + 1 =
          (2 * remaining + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
            2 * remaining + 1]
          (some (affineUnaryTripleMapFamilyCfg (.restore .third cursor)
            (some .tick) tail output (List.replicate remaining .tick)
            first second (() :: third))) = _
      simpa only [List.replicate_succ, List.cons_append,
        affineUnaryTripleMap_replicate_unit_append_cons] using
        ih (some UnaryFrameSym.tick) (() :: third)

private theorem affineUnaryTripleMap_third_copy_eval
    (forms : List AffineUnaryTripleForm) (index : Fin forms.length)
    (cursor : AffineUnaryTripleMapCursor forms .third)
    (value : Nat) (tail output : List UnaryFrameSym)
    (first second : List Unit) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        5 * value + 2]
      (some (affineUnaryTripleMapFamilyCfg (.emit .third cursor)
        none tail output [] first second (List.replicate value ()))) =
      some (affineUnaryTripleMapFamilyCfg (.repeat .third cursor)
        none tail (List.replicate value .tick ++ output) []
        first second (List.replicate value ())) := by
  have hdrain := affineUnaryTripleMap_third_drain_eval forms index cursor
    value tail output [] first second
  have hrestore := affineUnaryTripleMap_third_restore_eval forms index cursor
    value tail (List.replicate value .tick ++ output) none first second []
  simp only [List.append_nil] at hdrain hrestore
  have hsteps : (2 * value + 1) + (3 * value + 1) =
      5 * value + 2 := by omega
  rw [← hsteps]
  exact (EvalsTo.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _
    (⟨3 * value + 1, hdrain⟩ : EvalsTo _ _ _)
    (⟨2 * value + 1, hrestore⟩ : EvalsTo _ _ _)).evals_in_steps

private theorem affineUnaryTripleMap_first_coefficient_eval
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (index : Fin forms.length) (remaining : Nat)
    (hremaining : remaining ≤ (forms.get index).first)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        remaining * (5 * seed.first + 3) + 1]
      (some (affineUnaryTripleMapFamilyCfg
        (.repeat .first
          ⟨index, ⟨remaining, by
            change remaining < (forms.get index).first + 1
            omega⟩⟩)
        none tail output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))) =
      some (affineUnaryTripleMapFamilyCfg
        (affineUnaryTripleMapAfterPhase forms .first index)
        none tail (List.replicate (remaining * seed.first) .tick ++ output) []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())) := by
  induction remaining generalizing output with
  | zero =>
      simp only [zero_mul, List.replicate_zero, List.nil_append]
      change step (affineUnaryTripleMapFamilyRevProgram forms)
        (affineUnaryTripleMapFamilyCfg
          (.repeat .first ⟨index, ⟨0, by
            change 0 < (forms.get index).first + 1
            omega⟩⟩)
          none tail output []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ())) =
        some (affineUnaryTripleMapFamilyCfg
          (affineUnaryTripleMapAfterPhase forms .first index)
          none tail output []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ()))
      rfl
  | succ remaining ih =>
      let cursor : AffineUnaryTripleMapCursor forms .first :=
        ⟨index, ⟨remaining, by
          change remaining < (forms.get index).first + 1
          omega⟩⟩
      let hone : EvalsTo
          (step (affineUnaryTripleMapFamilyRevProgram forms))
          (affineUnaryTripleMapFamilyCfg
            (.repeat .first
              ⟨index, ⟨remaining + 1, by
                change remaining + 1 < (forms.get index).first + 1
                omega⟩⟩)
            none tail output []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))
          (some (affineUnaryTripleMapFamilyCfg (.emit .first cursor)
            none tail output []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))) :=
        ⟨1, rfl⟩
      have hcopy := affineUnaryTripleMap_first_copy_eval forms index cursor
        seed.first tail output
        (List.replicate seed.second ()) (List.replicate seed.third ())
      have hrest := ih (by omega)
        (List.replicate seed.first .tick ++ output)
      let throughCopy := EvalsTo.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ hone
        (⟨5 * seed.first + 2, hcopy⟩ : EvalsTo _ _ _)
      let full := EvalsTo.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ throughCopy
        (⟨remaining * (5 * seed.first + 3) + 1, hrest⟩ : EvalsTo _ _ _)
      have hsteps : full.steps =
          (remaining + 1) * (5 * seed.first + 3) + 1 := by
        simp only [full, throughCopy, hone, EvalsTo.trans]
        ring
      rw [← hsteps]
      have hmul : (remaining + 1) * seed.first =
          remaining * seed.first + seed.first := by ring
      rw [hmul, List.replicate_add, List.append_assoc]
      exact full.evals_in_steps

private theorem affineUnaryTripleMap_second_coefficient_eval
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (index : Fin forms.length) (remaining : Nat)
    (hremaining : remaining ≤ (forms.get index).second)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        remaining * (5 * seed.second + 3) + 1]
      (some (affineUnaryTripleMapFamilyCfg
        (.repeat .second
          ⟨index, ⟨remaining, by
            change remaining < (forms.get index).second + 1
            omega⟩⟩)
        none tail output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))) =
      some (affineUnaryTripleMapFamilyCfg
        (affineUnaryTripleMapAfterPhase forms .second index)
        none tail
        (List.replicate (remaining * seed.second) .tick ++ output) []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())) := by
  induction remaining generalizing output with
  | zero =>
      simp only [zero_mul, List.replicate_zero, List.nil_append]
      change step (affineUnaryTripleMapFamilyRevProgram forms)
        (affineUnaryTripleMapFamilyCfg
          (.repeat .second ⟨index, ⟨0, by
            change 0 < (forms.get index).second + 1
            omega⟩⟩)
          none tail output []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ())) =
        some (affineUnaryTripleMapFamilyCfg
          (affineUnaryTripleMapAfterPhase forms .second index)
          none tail output []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ()))
      rfl
  | succ remaining ih =>
      let cursor : AffineUnaryTripleMapCursor forms .second :=
        ⟨index, ⟨remaining, by
          change remaining < (forms.get index).second + 1
          omega⟩⟩
      let hone : EvalsTo
          (step (affineUnaryTripleMapFamilyRevProgram forms))
          (affineUnaryTripleMapFamilyCfg
            (.repeat .second
              ⟨index, ⟨remaining + 1, by
                change remaining + 1 < (forms.get index).second + 1
                omega⟩⟩)
            none tail output []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))
          (some (affineUnaryTripleMapFamilyCfg (.emit .second cursor)
            none tail output []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))) :=
        ⟨1, rfl⟩
      have hcopy := affineUnaryTripleMap_second_copy_eval forms index cursor
        seed.second tail output
        (List.replicate seed.first ()) (List.replicate seed.third ())
      have hrest := ih (by omega)
        (List.replicate seed.second .tick ++ output)
      let throughCopy := EvalsTo.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ hone
        (⟨5 * seed.second + 2, hcopy⟩ : EvalsTo _ _ _)
      let full := EvalsTo.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ throughCopy
        (⟨remaining * (5 * seed.second + 3) + 1, hrest⟩ : EvalsTo _ _ _)
      have hsteps : full.steps =
          (remaining + 1) * (5 * seed.second + 3) + 1 := by
        simp only [full, throughCopy, hone, EvalsTo.trans]
        ring
      rw [← hsteps]
      have hmul : (remaining + 1) * seed.second =
          remaining * seed.second + seed.second := by ring
      rw [hmul, List.replicate_add, List.append_assoc]
      exact full.evals_in_steps

private theorem affineUnaryTripleMap_third_coefficient_eval
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (index : Fin forms.length) (remaining : Nat)
    (hremaining : remaining ≤ (forms.get index).third)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        remaining * (5 * seed.third + 3) + 1]
      (some (affineUnaryTripleMapFamilyCfg
        (.repeat .third
          ⟨index, ⟨remaining, by
            change remaining < (forms.get index).third + 1
            omega⟩⟩)
        none tail output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))) =
      some (affineUnaryTripleMapFamilyCfg
        (affineUnaryTripleMapAfterPhase forms .third index)
        none tail
        (List.replicate (remaining * seed.third) .tick ++ output) []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())) := by
  induction remaining generalizing output with
  | zero =>
      simp only [zero_mul, List.replicate_zero, List.nil_append]
      change step (affineUnaryTripleMapFamilyRevProgram forms)
        (affineUnaryTripleMapFamilyCfg
          (.repeat .third ⟨index, ⟨0, by
            change 0 < (forms.get index).third + 1
            omega⟩⟩)
          none tail output []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ())) =
        some (affineUnaryTripleMapFamilyCfg
          (affineUnaryTripleMapAfterPhase forms .third index)
          none tail output []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ()))
      rfl
  | succ remaining ih =>
      let cursor : AffineUnaryTripleMapCursor forms .third :=
        ⟨index, ⟨remaining, by
          change remaining < (forms.get index).third + 1
          omega⟩⟩
      let hone : EvalsTo
          (step (affineUnaryTripleMapFamilyRevProgram forms))
          (affineUnaryTripleMapFamilyCfg
            (.repeat .third
              ⟨index, ⟨remaining + 1, by
                change remaining + 1 < (forms.get index).third + 1
                omega⟩⟩)
            none tail output []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))
          (some (affineUnaryTripleMapFamilyCfg (.emit .third cursor)
            none tail output []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))) :=
        ⟨1, rfl⟩
      have hcopy := affineUnaryTripleMap_third_copy_eval forms index cursor
        seed.third tail output
        (List.replicate seed.first ()) (List.replicate seed.second ())
      have hrest := ih (by omega)
        (List.replicate seed.third .tick ++ output)
      let throughCopy := EvalsTo.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ hone
        (⟨5 * seed.third + 2, hcopy⟩ : EvalsTo _ _ _)
      let full := EvalsTo.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ throughCopy
        (⟨remaining * (5 * seed.third + 3) + 1, hrest⟩ : EvalsTo _ _ _)
      have hsteps : full.steps =
          (remaining + 1) * (5 * seed.third + 3) + 1 := by
        simp only [full, throughCopy, hone, EvalsTo.trans]
        ring
      rw [← hsteps]
      have hmul : (remaining + 1) * seed.third =
          remaining * seed.third + seed.third := by ring
      rw [hmul, List.replicate_add, List.append_assoc]
      exact full.evals_in_steps

/-- Exact cost of emitting one affine field from loaded counters. -/
def affineUnaryTripleFormSourceSteps (form : AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) : Nat :=
  form.constant + 1 +
    (form.first * (5 * seed.first + 3) + 1) +
    (form.second * (5 * seed.second + 3) + 1) +
    (form.third * (5 * seed.third + 3) + 1) + 1

private theorem affineUnaryTripleMap_oneForm_eval
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (index : Fin forms.length) (tail output : List UnaryFrameSym) :
    (flip Option.bind (step (affineUnaryTripleMapFamilyRevProgram forms)))^[
        affineUnaryTripleFormSourceSteps (forms.get index) seed]
      (some (affineUnaryTripleMapFamilyCfg
        (.repeat .constant
          (affineUnaryTripleMapCursorStart forms .constant index))
        none tail output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))) =
      some (affineUnaryTripleMapFamilyCfg
        (affineUnaryTripleMapAfterField forms index)
        none tail
        ((encodeUnaryFrameBlock
          (affineUnaryTripleFormValue (forms.get index) seed)).reverse ++
            output) []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())) := by
  let form := forms.get index
  have hconstant := affineUnaryTripleMap_constant_eval forms seed index
    form.constant (by simp [form]) tail output
  have hfirst := affineUnaryTripleMap_first_coefficient_eval forms seed index
    form.first (by simp [form]) tail
    (List.replicate form.constant .tick ++ output)
  have hsecond := affineUnaryTripleMap_second_coefficient_eval forms seed index
    form.second (by simp [form]) tail
    (List.replicate (form.first * seed.first) .tick ++
      (List.replicate form.constant .tick ++ output))
  have hthird := affineUnaryTripleMap_third_coefficient_eval forms seed index
    form.third (by simp [form]) tail
    (List.replicate (form.second * seed.second) .tick ++
      (List.replicate (form.first * seed.first) .tick ++
        (List.replicate form.constant .tick ++ output)))
  let hseparator : EvalsTo
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyCfg (.pushSeparator index)
        none tail
        (List.replicate (form.third * seed.third) .tick ++
          (List.replicate (form.second * seed.second) .tick ++
            (List.replicate (form.first * seed.first) .tick ++
              (List.replicate form.constant .tick ++ output)))) []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))
      (some (affineUnaryTripleMapFamilyCfg
        (affineUnaryTripleMapAfterField forms index)
        none tail
        (.separator ::
          (List.replicate (form.third * seed.third) .tick ++
            (List.replicate (form.second * seed.second) .tick ++
              (List.replicate (form.first * seed.first) .tick ++
                (List.replicate form.constant .tick ++ output))))) []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))) := ⟨1, rfl⟩
  let runConstant : EvalsTo
      (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ :=
    ⟨form.constant + 1, hconstant⟩
  let runFirst : EvalsTo
      (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ :=
    ⟨form.first * (5 * seed.first + 3) + 1, hfirst⟩
  let runSecond : EvalsTo
      (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ :=
    ⟨form.second * (5 * seed.second + 3) + 1, hsecond⟩
  let runThird : EvalsTo
      (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ :=
    ⟨form.third * (5 * seed.third + 3) + 1, hthird⟩
  let runSeparator : EvalsTo
      (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ := hseparator
  let throughFirst := EvalsTo.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _
    runConstant runFirst
  let throughSecond := EvalsTo.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _
    throughFirst runSecond
  let throughThird := EvalsTo.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _
    throughSecond runThird
  let full := EvalsTo.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _
    throughThird runSeparator
  have hsteps : full.steps =
      affineUnaryTripleFormSourceSteps (forms.get index) seed := by
    simp only [full, throughThird, throughSecond, throughFirst,
      runSeparator, runThird, runSecond, runFirst, runConstant,
      hseparator, EvalsTo.trans]
    simp [affineUnaryTripleFormSourceSteps, form]
    ring
  rw [← hsteps]
  have hticks : form.third * seed.third +
      (form.second * seed.second +
        (form.first * seed.first + form.constant)) =
      affineUnaryTripleFormValue form seed := by
    simp [affineUnaryTripleFormValue]
    ring
  convert full.evals_in_steps using 1
  · simp [form, affineUnaryTripleMapCursorStart,
      affineUnaryTripleMapCoefficient]
  · simp only [encodeUnaryFrameBlock, List.reverse_append,
      List.reverse_replicate, List.reverse_singleton,
      List.singleton_append]
    congr 2
    change .separator ::
        (List.replicate (affineUnaryTripleFormValue form seed) .tick ++
          output) = _
    rw [← hticks, List.replicate_add, List.replicate_add,
      List.replicate_add, List.append_assoc]
    simp only [List.cons.injEq, List.append_assoc]

/-- Exact cost of the still-unprocessed suffix of the fixed form table. -/
private def affineUnaryTripleMapFormsSourceStepsFrom
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (index : Nat) : Nat :=
  ((forms.drop index).map fun form =>
    affineUnaryTripleFormSourceSteps form seed).sum

private def affineUnaryTripleMap_formsFrom_eval
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (index : Nat) (hindex : index < forms.length)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyCfg
        (.repeat .constant
          (affineUnaryTripleMapCursorStart forms .constant
            ⟨index, hindex⟩))
        none tail output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))
      (some (affineUnaryTripleMapFamilyCfg .clearBuffer none tail
        ((encodeUnaryFrame
          (affineUnaryTripleMap (forms.drop index) seed)).reverse ++ output)
        []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())))
      (affineUnaryTripleMapFormsSourceStepsFrom forms seed index) := by
  let rec go (index : Nat) (hindex : index < forms.length)
      (output : List UnaryFrameSym) :
      EvalsToInTime
        (step (affineUnaryTripleMapFamilyRevProgram forms))
        (affineUnaryTripleMapFamilyCfg
          (.repeat .constant
            (affineUnaryTripleMapCursorStart forms .constant
              ⟨index, hindex⟩))
          none tail output []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ()))
        (some (affineUnaryTripleMapFamilyCfg .clearBuffer none tail
          ((encodeUnaryFrame
            (affineUnaryTripleMap (forms.drop index) seed)).reverse ++ output)
          []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ())))
        (affineUnaryTripleMapFormsSourceStepsFrom forms seed index) := by
    let current : Fin forms.length := ⟨index, hindex⟩
    have hdrop : forms.drop index =
        forms.get current :: forms.drop (index + 1) := by
      simpa [current] using List.drop_eq_getElem_cons hindex
    let blockOutput :=
      (encodeUnaryFrameBlock
        (affineUnaryTripleFormValue (forms.get current) seed)).reverse ++
        output
    have hfirstSource := affineUnaryTripleMap_oneForm_eval
      forms seed current tail output
    by_cases hnext : index + 1 < forms.length
    · let next : Fin forms.length := ⟨index + 1, hnext⟩
      have hafter : affineUnaryTripleMapAfterField forms current =
          .repeat .constant
            (affineUnaryTripleMapCursorStart forms .constant next) := by
        simp [affineUnaryTripleMapAfterField, current, next, hnext]
      have hfirst : EvalsToInTime
          (step (affineUnaryTripleMapFamilyRevProgram forms))
          (affineUnaryTripleMapFamilyCfg
            (.repeat .constant
              (affineUnaryTripleMapCursorStart forms .constant current))
            none tail output []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ()))
          (some (affineUnaryTripleMapFamilyCfg
            (.repeat .constant
              (affineUnaryTripleMapCursorStart forms .constant next))
            none tail blockOutput []
            (List.replicate seed.first ())
            (List.replicate seed.second ())
            (List.replicate seed.third ())))
          (affineUnaryTripleFormSourceSteps (forms.get current) seed) := by
        refine ⟨⟨_, ?_⟩, le_rfl⟩
        rw [hafter] at hfirstSource
        change _ = some (affineUnaryTripleMapFamilyCfg
          (.repeat .constant
            (affineUnaryTripleMapCursorStart forms .constant next))
          none tail blockOutput []
          (List.replicate seed.first ())
          (List.replicate seed.second ())
          (List.replicate seed.third ())) at hfirstSource
        exact hfirstSource
      have hrest := go (index + 1) hnext blockOutput
      let full := EvalsToInTime.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms))
        (affineUnaryTripleFormSourceSteps (forms.get current) seed)
        (affineUnaryTripleMapFormsSourceStepsFrom forms seed (index + 1))
        _ _ _ hfirst hrest
      convert full using 1
      · rw [hdrop]
        simp [affineUnaryTripleMap, blockOutput, encodeUnaryFrame,
          List.reverse_append, List.append_assoc]
      · simp [affineUnaryTripleMapFormsSourceStepsFrom, hdrop, Nat.add_comm]
    · have htail : forms.drop (index + 1) = [] := by
        apply List.drop_eq_nil_of_le
        omega
      have hafter : affineUnaryTripleMapAfterField forms current =
          .clearBuffer := by
        simp [affineUnaryTripleMapAfterField, current, hnext]
      refine ⟨⟨affineUnaryTripleFormSourceSteps (forms.get current) seed, ?_⟩,
        ?_⟩
      · simpa [hafter, hdrop, htail, affineUnaryTripleMap, blockOutput,
          encodeUnaryFrame, List.reverse_append] using hfirstSource
      · simp [affineUnaryTripleMapFormsSourceStepsFrom, hdrop, htail]
    termination_by forms.length - index
    decreasing_by omega
  exact go index hindex output

/-- Exact form-table cost for one loaded runtime triple. -/
def affineUnaryTripleMapFormsSourceSteps
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed) : Nat :=
  (forms.map fun form => affineUnaryTripleFormSourceSteps form seed).sum

private def affineUnaryTripleMap_forms_eval
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyCfg
        (affineUnaryTripleMapStartLabel forms) none tail output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))
      (some (affineUnaryTripleMapFamilyCfg .clearBuffer none tail
        ((encodeUnaryFrame (affineUnaryTripleMap forms seed)).reverse ++ output)
        []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())))
      (affineUnaryTripleMapFormsSourceSteps forms seed) := by
  cases forms with
  | nil =>
      exact ⟨⟨0, by simp [affineUnaryTripleMapStartLabel,
        affineUnaryTripleMapFormsSourceSteps, affineUnaryTripleMap,
        encodeUnaryFrame]⟩, le_rfl⟩
  | cons form rest =>
      have hpositive : 0 < (form :: rest).length := by simp
      simpa [affineUnaryTripleMapStartLabel, hpositive,
        affineUnaryTripleMapFormsSourceSteps,
        affineUnaryTripleMapFormsSourceStepsFrom] using
        affineUnaryTripleMap_formsFrom_eval
          (form :: rest) seed 0 hpositive tail output

private def affineUnaryTripleMapFamilyTestCfg
    {forms : List AffineUnaryTripleForm}
    (label : AffineUnaryTripleMapLabel forms) (test : Bool)
    (buffer₁ : Option UnaryFrameSym) (input output work₁ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineUnaryTripleMapFamilyRevProgram forms) where
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

private theorem affineUnaryTripleMap_clearFirst_eval
    {forms : List AffineUnaryTripleForm} (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym) (second third : List Unit) :
    (flip Option.bind
      (step (affineUnaryTripleMapFamilyRevProgram forms)))^[value + 1]
      (some (affineUnaryTripleMapFamilyTestCfg .clearFirst test buffer₁
        input output work₁ (List.replicate value ()) second third)) =
      some (affineUnaryTripleMapFamilyTestCfg .clearSecond false buffer₁
        input output work₁ [] second third) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[value + 1]
          (some (affineUnaryTripleMapFamilyTestCfg .clearFirst true buffer₁
            input output work₁ (List.replicate value ()) second third)) = _
      simpa using ih true

private theorem affineUnaryTripleMap_clearSecond_eval
    {forms : List AffineUnaryTripleForm} (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym) (first third : List Unit) :
    (flip Option.bind
      (step (affineUnaryTripleMapFamilyRevProgram forms)))^[value + 1]
      (some (affineUnaryTripleMapFamilyTestCfg .clearSecond test buffer₁
        input output work₁ first (List.replicate value ()) third)) =
      some (affineUnaryTripleMapFamilyTestCfg .clearThird false buffer₁
        input output work₁ first [] third) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[value + 1]
          (some (affineUnaryTripleMapFamilyTestCfg .clearSecond true buffer₁
            input output work₁ first (List.replicate value ()) third)) = _
      simpa using ih true

private theorem affineUnaryTripleMap_clearThird_eval
    {forms : List AffineUnaryTripleForm} (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym) (first second : List Unit) :
    (flip Option.bind
      (step (affineUnaryTripleMapFamilyRevProgram forms)))^[value + 1]
      (some (affineUnaryTripleMapFamilyTestCfg .clearThird test buffer₁
        input output work₁ first second (List.replicate value ()))) =
      some (affineUnaryTripleMapFamilyTestCfg (.loader .load₁) false buffer₁
        input output work₁ first second []) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineUnaryTripleMapFamilyRevProgram forms)))^[value + 1]
          (some (affineUnaryTripleMapFamilyTestCfg .clearThird true buffer₁
            input output work₁ first second (List.replicate value ()))) = _
      simpa using ih true

private def affineUnaryTripleMap_clear_run
    {forms : List AffineUnaryTripleForm} (seed : AffineUnaryTripleSeed)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyCfg .clearFirst none input output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))
      (some (affineUnaryTripleMapFamilyLoopCfg forms input output))
      ((seed.first + 1) + (seed.second + 1) + (seed.third + 1)) := by
  let afterFirst := affineUnaryTripleMapFamilyTestCfg
    (forms := forms) .clearSecond false none input output [] []
    (List.replicate seed.second ()) (List.replicate seed.third ())
  let afterSecond := affineUnaryTripleMapFamilyTestCfg
    (forms := forms) .clearThird false none input output [] [] []
    (List.replicate seed.third ())
  have hfirst : EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyCfg .clearFirst none input output []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))
      (some afterFirst) (seed.first + 1) :=
    ⟨⟨seed.first + 1, by
      simpa [affineUnaryTripleMapFamilyCfg,
        affineUnaryTripleMapFamilyTestCfg, afterFirst] using
        affineUnaryTripleMap_clearFirst_eval (forms := forms) seed.first
          none false input output [] (List.replicate seed.second ())
          (List.replicate seed.third ())⟩, le_rfl⟩
  have hsecond : EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms)) afterFirst
      (some afterSecond) (seed.second + 1) :=
    ⟨⟨seed.second + 1, by
      simpa [afterFirst, afterSecond] using
        affineUnaryTripleMap_clearSecond_eval (forms := forms) seed.second
          none false input output [] [] (List.replicate seed.third ())⟩,
      le_rfl⟩
  have hthird : EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms)) afterSecond
      (some (affineUnaryTripleMapFamilyLoopCfg forms input output))
      (seed.third + 1) :=
    ⟨⟨seed.third + 1, by
      simpa [afterSecond, affineUnaryTripleMapFamilyLoopCfg,
        affineUnaryTripleMapFamilyCfg,
        affineUnaryTripleMapFamilyTestCfg] using
        affineUnaryTripleMap_clearThird_eval (forms := forms) seed.third
          none false input output [] [] []⟩, le_rfl⟩
  let throughSecond := EvalsToInTime.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms))
    (seed.first + 1) (seed.second + 1) _ afterFirst _ hfirst hsecond
  let full := EvalsToInTime.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms))
    ((seed.second + 1) + (seed.first + 1)) (seed.third + 1)
    _ afterSecond _ throughSecond hthird
  convert full using 1 <;> omega

/-- Exact cost of one seed iteration, including loader and scratch clearing. -/
def affineUnaryTripleMapFamilyOneSteps
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed) : Nat :=
  unaryTripleLoaderSteps seed.first seed.second seed.third + 1 +
    affineUnaryTripleMapFormsSourceSteps forms seed + 1 +
    (seed.first + 1) + (seed.second + 1) + (seed.third + 1)

private def affineUnaryTripleMapFamily_one
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyLoopCfg forms
        (encodeAffineUnaryTripleSeed seed ++ tail) output)
      (some (affineUnaryTripleMapFamilyLoopCfg forms tail
        ((encodeUnaryFrame (affineUnaryTripleMap forms seed)).reverse ++
          output)))
      (affineUnaryTripleMapFamilyOneSteps forms seed) := by
  let loaderReady := liftAffineUnaryTripleMapLoaderCfg (forms := forms)
    (unaryTripleLoaderReadyCfgFor seed.first seed.second seed.third
      tail output [] [])
  let formStart := affineUnaryTripleMapFamilyCfg
    (affineUnaryTripleMapStartLabel forms) none tail output []
    (List.replicate seed.first ())
    (List.replicate seed.second ())
    (List.replicate seed.third ())
  let rowOutput :=
    (encodeUnaryFrame (affineUnaryTripleMap forms seed)).reverse ++ output
  let clearStart := affineUnaryTripleMapFamilyCfg (forms := forms)
    .clearFirst none tail rowOutput []
    (List.replicate seed.first ())
    (List.replicate seed.second ())
    (List.replicate seed.third ())
  have hloader := affineUnaryTripleMap_loader_run
    (forms := forms) seed tail output
  have hbridge : EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms)) loaderReady
      (some formStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hforms : EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms)) formStart
      (some (affineUnaryTripleMapFamilyCfg .clearBuffer none tail
        rowOutput []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ())))
      (affineUnaryTripleMapFormsSourceSteps forms seed) := by
    simpa [formStart, rowOutput] using
      affineUnaryTripleMap_forms_eval forms seed tail output
  have hbuffer : EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyCfg .clearBuffer none tail rowOutput []
        (List.replicate seed.first ())
        (List.replicate seed.second ())
        (List.replicate seed.third ()))
      (some clearStart) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms)) clearStart
      (some (affineUnaryTripleMapFamilyLoopCfg forms tail rowOutput))
      ((seed.first + 1) + (seed.second + 1) + (seed.third + 1)) := by
    simpa [clearStart] using
      affineUnaryTripleMap_clear_run (forms := forms) seed tail rowOutput
  let h₁ := EvalsToInTime.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ 1 _ loaderReady _
    hloader hbridge
  let h₂ := EvalsToInTime.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ formStart _
    h₁ hforms
  let h₃ := EvalsToInTime.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ 1 _ _ _
    h₂ hbuffer
  let full := EvalsToInTime.trans
    (step (affineUnaryTripleMapFamilyRevProgram forms)) _ _ _ clearStart _
    h₃ hclear
  convert full using 1 <;>
    simp [affineUnaryTripleMapFamilyOneSteps] <;> omega

/-- Exact runtime for the complete seed family, including the two final
empty-input halt steps. -/
def affineUnaryTripleMapFamilySteps
    (forms : List AffineUnaryTripleForm) :
    List AffineUnaryTripleSeed → Nat
  | [] => 2
  | seed :: rest =>
      affineUnaryTripleMapFamilyOneSteps forms seed +
        affineUnaryTripleMapFamilySteps forms rest

private def affineUnaryTripleMapFamily_runFrom
    (forms : List AffineUnaryTripleForm)
    (seeds : List AffineUnaryTripleSeed) (output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (affineUnaryTripleMapFamilyLoopCfg forms
        (encodeAffineUnaryTripleSeedFamily seeds) output)
      (some (haltCfg (affineUnaryTripleMapFamilyRevProgram forms)
        ((encodeUnaryFrame
          (affineUnaryTripleMapFamily forms seeds)).reverse ++ output)))
      (affineUnaryTripleMapFamilySteps forms seeds) := by
  induction seeds generalizing output with
  | nil =>
      exact ⟨⟨2, rfl⟩, le_rfl⟩
  | cons seed rest ih =>
      let rowOutput :=
        (encodeUnaryFrame (affineUnaryTripleMap forms seed)).reverse ++ output
      have hfirst := affineUnaryTripleMapFamily_one
        forms seed (encodeAffineUnaryTripleSeedFamily rest) output
      have hrest := ih rowOutput
      let full := EvalsToInTime.trans
        (step (affineUnaryTripleMapFamilyRevProgram forms))
        (affineUnaryTripleMapFamilyOneSteps forms seed)
        (affineUnaryTripleMapFamilySteps forms rest)
        _ (affineUnaryTripleMapFamilyLoopCfg forms
          (encodeAffineUnaryTripleSeedFamily rest) rowOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineUnaryTripleSeedFamily,
          encodeAffineUnaryTripleSeed]
      · simp [affineUnaryTripleMapFamily, rowOutput, encodeUnaryFrame,
          List.reverse_append, List.append_assoc]
      · simp [affineUnaryTripleMapFamilySteps]
        omega

/-- One fixed builder controller maps every unary runtime triple through its
fixed affine form table, emits the reversed canonical result frame, and
halts with all scratch state cleared. -/
def affineUnaryTripleMapFamily_run
    (forms : List AffineUnaryTripleForm)
    (seeds : List AffineUnaryTripleSeed) :
    EvalsToInTime
      (step (affineUnaryTripleMapFamilyRevProgram forms))
      (initialCfg (affineUnaryTripleMapFamilyRevProgram forms)
        (encodeAffineUnaryTripleSeedFamily seeds))
      (some (haltCfg (affineUnaryTripleMapFamilyRevProgram forms)
        ((encodeUnaryFrame
          (affineUnaryTripleMapFamily forms seeds)).reverse)))
      (affineUnaryTripleMapFamilySteps forms seeds) := by
  have hinit : affineUnaryTripleMapFamilyLoopCfg forms
      (encodeAffineUnaryTripleSeedFamily seeds) [] =
        initialCfg (affineUnaryTripleMapFamilyRevProgram forms)
          (encodeAffineUnaryTripleSeedFamily seeds) := rfl
  rw [← hinit]
  simpa only [List.append_nil] using
    affineUnaryTripleMapFamily_runFrom forms seeds []

/-- Fixed contribution of one affine form to the source's quadratic bound. -/
def affineUnaryTripleFormStepCoeff (form : AffineUnaryTripleForm) : Nat :=
  form.constant + 8 * (form.first + form.second + form.third) + 5

/-- Fixed coefficient for the complete affine-map family source. -/
def affineUnaryTripleMapFamilyStepCoeff
    (forms : List AffineUnaryTripleForm) : Nat :=
  11 + (forms.map affineUnaryTripleFormStepCoeff).sum

private theorem affineUnaryTripleFormSourceSteps_le
    (form : AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleFormSourceSteps form seed ≤
      affineUnaryTripleFormStepCoeff form *
        (seed.first + seed.second + seed.third + 1) ^ 2 := by
  let payload := seed.first + seed.second + seed.third + 1
  have hpayload : 1 ≤ payload := by simp [payload]
  have hpayloadSquare : payload ≤ payload ^ 2 := by nlinarith
  have hone : 1 ≤ payload ^ 2 := hpayload.trans hpayloadSquare
  have hfirstPayload : seed.first ≤ payload := by
    dsimp only [payload]
    omega
  have hsecondPayload : seed.second ≤ payload := by
    dsimp only [payload]
    omega
  have hthirdPayload : seed.third ≤ payload := by
    dsimp only [payload]
    omega
  have hfirst : seed.first ≤ payload ^ 2 :=
    hfirstPayload.trans hpayloadSquare
  have hsecond : seed.second ≤ payload ^ 2 :=
    hsecondPayload.trans hpayloadSquare
  have hthird : seed.third ≤ payload ^ 2 :=
    hthirdPayload.trans hpayloadSquare
  have hc := Nat.mul_le_mul_left form.constant hone
  have hfa := Nat.mul_le_mul_left (5 * form.first) hfirst
  have hfc := Nat.mul_le_mul_left (3 * form.first) hone
  have hsa := Nat.mul_le_mul_left (5 * form.second) hsecond
  have hsc := Nat.mul_le_mul_left (3 * form.second) hone
  have hta := Nat.mul_le_mul_left (5 * form.third) hthird
  have htc := Nat.mul_le_mul_left (3 * form.third) hone
  have hfive := Nat.mul_le_mul_left 5 hone
  calc
    affineUnaryTripleFormSourceSteps form seed =
        form.constant + 5 * form.first * seed.first + 3 * form.first +
          5 * form.second * seed.second + 3 * form.second +
          5 * form.third * seed.third + 3 * form.third + 5 := by
      simp [affineUnaryTripleFormSourceSteps]
      ring
    _ ≤ form.constant * payload ^ 2 +
          5 * form.first * payload ^ 2 + 3 * form.first * payload ^ 2 +
          5 * form.second * payload ^ 2 + 3 * form.second * payload ^ 2 +
          5 * form.third * payload ^ 2 + 3 * form.third * payload ^ 2 +
          5 * payload ^ 2 := by omega
    _ = affineUnaryTripleFormStepCoeff form * payload ^ 2 := by
      simp [affineUnaryTripleFormStepCoeff]
      ring

private theorem affineUnaryTripleMapFormsSourceSteps_le
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMapFormsSourceSteps forms seed ≤
      (forms.map affineUnaryTripleFormStepCoeff).sum *
        (seed.first + seed.second + seed.third + 1) ^ 2 := by
  induction forms with
  | nil => simp [affineUnaryTripleMapFormsSourceSteps]
  | cons form rest ih =>
      simp only [affineUnaryTripleMapFormsSourceSteps, List.map_cons,
        List.sum_cons]
      have hform := affineUnaryTripleFormSourceSteps_le form seed
      calc
        affineUnaryTripleFormSourceSteps form seed +
            (rest.map fun form =>
              affineUnaryTripleFormSourceSteps form seed).sum ≤
            affineUnaryTripleFormStepCoeff form *
                (seed.first + seed.second + seed.third + 1) ^ 2 +
              (rest.map affineUnaryTripleFormStepCoeff).sum *
                (seed.first + seed.second + seed.third + 1) ^ 2 :=
          Nat.add_le_add hform (by
            simpa [affineUnaryTripleMapFormsSourceSteps] using ih)
        _ = (affineUnaryTripleFormStepCoeff form +
              (rest.map affineUnaryTripleFormStepCoeff).sum) *
            (seed.first + seed.second + seed.third + 1) ^ 2 := by ring

/-- One complete loaded-seed iteration is quadratic in its three explicit
unary fields; the form table occurs only in the fixed coefficient. -/
theorem affineUnaryTripleMapFamilyOneSteps_le
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMapFamilyOneSteps forms seed ≤
      affineUnaryTripleMapFamilyStepCoeff forms *
        (seed.first + seed.second + seed.third + 1) ^ 2 := by
  let payload := seed.first + seed.second + seed.third + 1
  have hpayload : 1 ≤ payload := by simp [payload]
  have hpayloadSquare : payload ≤ payload ^ 2 := by nlinarith
  have hone : 1 ≤ payload ^ 2 := hpayload.trans hpayloadSquare
  have hbase :
      unaryTripleLoaderSteps seed.first seed.second seed.third + 1 + 1 +
          (seed.first + 1) + (seed.second + 1) + (seed.third + 1) ≤
        11 * payload ^ 2 := by
    simp only [unaryTripleLoaderSteps]
    dsimp only [payload]
    nlinarith
  have hforms := affineUnaryTripleMapFormsSourceSteps_le forms seed
  calc
    affineUnaryTripleMapFamilyOneSteps forms seed =
        (unaryTripleLoaderSteps seed.first seed.second seed.third + 1 + 1 +
          (seed.first + 1) + (seed.second + 1) + (seed.third + 1)) +
          affineUnaryTripleMapFormsSourceSteps forms seed := by
      simp [affineUnaryTripleMapFamilyOneSteps]
      omega
    _ ≤ 11 * payload ^ 2 +
          (forms.map affineUnaryTripleFormStepCoeff).sum * payload ^ 2 :=
      Nat.add_le_add hbase (by simpa [payload] using hforms)
    _ = affineUnaryTripleMapFamilyStepCoeff forms * payload ^ 2 := by
      simp [affineUnaryTripleMapFamilyStepCoeff]
      ring

@[simp] theorem encodeAffineUnaryTripleSeed_length
    (seed : AffineUnaryTripleSeed) :
    (encodeAffineUnaryTripleSeed seed).length =
      seed.first + seed.second + seed.third + 3 := by
  simp [encodeAffineUnaryTripleSeed, encodeUnaryFrame_length]
  omega

/-- The complete source run is quadratic in the concatenated explicit seed
stream. -/
theorem affineUnaryTripleMapFamilySteps_le
    (forms : List AffineUnaryTripleForm)
    (seeds : List AffineUnaryTripleSeed) :
    affineUnaryTripleMapFamilySteps forms seeds ≤
      affineUnaryTripleMapFamilyStepCoeff forms *
        (encodeAffineUnaryTripleSeedFamily seeds).length ^ 2 + 2 := by
  induction seeds with
  | nil => simp [affineUnaryTripleMapFamilySteps,
      encodeAffineUnaryTripleSeedFamily]
  | cons seed rest ih =>
      let headLength := (encodeAffineUnaryTripleSeed seed).length
      let restLength := (encodeAffineUnaryTripleSeedFamily rest).length
      let coeff := affineUnaryTripleMapFamilyStepCoeff forms
      have honeSource := affineUnaryTripleMapFamilyOneSteps_le forms seed
      have hpayload : seed.first + seed.second + seed.third + 1 ≤
          headLength := by simp [headLength]
      have hsquare : (seed.first + seed.second + seed.third + 1) ^ 2 ≤
          headLength ^ 2 := by nlinarith
      have hone : affineUnaryTripleMapFamilyOneSteps forms seed ≤
          coeff * headLength ^ 2 :=
        honeSource.trans (Nat.mul_le_mul_left coeff hsquare)
      calc
        affineUnaryTripleMapFamilySteps forms (seed :: rest) =
            affineUnaryTripleMapFamilyOneSteps forms seed +
              affineUnaryTripleMapFamilySteps forms rest := by rfl
        _ ≤ coeff * headLength ^ 2 + (coeff * restLength ^ 2 + 2) :=
          Nat.add_le_add hone (by simpa [coeff, restLength] using ih)
        _ = coeff * (headLength ^ 2 + restLength ^ 2) + 2 := by ring
        _ ≤ coeff * (headLength + restLength) ^ 2 + 2 := by
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left
          nlinarith [Nat.zero_le (2 * headLength * restLength)]
        _ = affineUnaryTripleMapFamilyStepCoeff forms *
            (encodeAffineUnaryTripleSeedFamily (seed :: rest)).length ^ 2 +
              2 := by
          simp [coeff, headLength, restLength,
            encodeAffineUnaryTripleSeedFamily]

/-- The compiled fixed affine-map source computes its prepend-order output
in quadratic time. -/
noncomputable def affineUnaryTripleMapFamilyRev_computableInPolyTime
    (forms : List AffineUnaryTripleForm) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleSeedFamily id
      (fun seeds : List AffineUnaryTripleSeed =>
        (encodeUnaryFrame
          (affineUnaryTripleMapFamily forms seeds)).reverse) where
  tm := compile (affineUnaryTripleMapFamilyRevProgram forms)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C (affineUnaryTripleMapFamilyStepCoeff forms) *
    Polynomial.X ^ 2 + 2
  outputsFun := fun seeds => by
    have builderRun := affineUnaryTripleMapFamily_run forms seeds
    have compiledRun := compile_evalsToInTime
      (affineUnaryTripleMapFamilyRevProgram forms) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile (affineUnaryTripleMapFamilyRevProgram forms)).step
        (_root_.Turing.initList
          (compile (affineUnaryTripleMapFamilyRevProgram forms))
          (encodeAffineUnaryTripleSeedFamily seeds))
        (some (_root_.Turing.haltList
          (compile (affineUnaryTripleMapFamilyRevProgram forms))
          ((encodeUnaryFrame
            (affineUnaryTripleMapFamily forms seeds)).reverse)))
        (affineUnaryTripleMapFamilySteps forms seeds) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : affineUnaryTripleMapFamilySteps forms seeds ≤
        (Polynomial.C (affineUnaryTripleMapFamilyStepCoeff forms) *
          Polynomial.X ^ 2 + 2).eval
            (encodeAffineUnaryTripleSeedFamily seeds).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_ofNat] using
        affineUnaryTripleMapFamilySteps_le forms seeds
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile (affineUnaryTripleMapFamilyRevProgram forms)).step
        (_root_.Turing.initList
          (compile (affineUnaryTripleMapFamilyRevProgram forms))
          (encodeAffineUnaryTripleSeedFamily seeds))
        (some (_root_.Turing.haltList
          (compile (affineUnaryTripleMapFamilyRevProgram forms))
          ((encodeUnaryFrame
            (affineUnaryTripleMapFamily forms seeds)).reverse)))
        ((Polynomial.C (affineUnaryTripleMapFamilyStepCoeff forms) *
          Polynomial.X ^ 2 + 2).eval
            (encodeAffineUnaryTripleSeedFamily seeds).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the prepend-order stream yields the forward canonical affine
frame.  Hence the raw runtime triple family is concretely TM2-computable in
polynomial time. -/
noncomputable def affineUnaryTripleMapFamily_computableInPolyTime
    (forms : List AffineUnaryTripleForm) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleSeedFamily id
      (fun seeds : List AffineUnaryTripleSeed =>
        encodeUnaryFrame (affineUnaryTripleMapFamily forms seeds)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineUnaryTripleMapFamilyRev_computableInPolyTime forms)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

/-! ## Payload-preserving row specialization -/

/-- One affine runtime triple together with a row-local byte payload.  The
payload is protected by an internal `frameEnd`; on the intended inputs it
contains no `frameEnd` of its own. -/
structure AffineUnaryTriplePayloadRow where
  seed : AffineUnaryTripleSeed
  payload : List UnaryFrameSym
deriving DecidableEq, Repr

/-- Seed-first input row consumed by the payload-preserving affine source. -/
def encodeAffineUnaryTriplePayloadRow
    (row : AffineUnaryTriplePayloadRow) : List UnaryFrameSym :=
  encodeAffineUnaryTripleSeed row.seed ++ [.frameEnd] ++
    row.payload ++ [.frameEnd]

/-- Concatenated seed-first row family. -/
def encodeAffineUnaryTriplePayloadRowFamily :
    List AffineUnaryTriplePayloadRow → List UnaryFrameSym
  | [] => []
  | row :: rest =>
      encodeAffineUnaryTriplePayloadRow row ++
        encodeAffineUnaryTriplePayloadRowFamily rest

/-- Intended output row: the affine image first, then the internal boundary,
the untouched payload, and the outer row boundary. -/
def affineUnaryTriplePayloadRowOutput
    (forms : List AffineUnaryTripleForm)
    (row : AffineUnaryTriplePayloadRow) : List UnaryFrameSym :=
  encodeUnaryFrame (affineUnaryTripleMap forms row.seed) ++ [.frameEnd] ++
    row.payload ++ [.frameEnd]

/-- Row-major output family of the payload-preserving affine source. -/
def affineUnaryTriplePayloadRowOutputFamily
    (forms : List AffineUnaryTripleForm) :
    List AffineUnaryTriplePayloadRow → List UnaryFrameSym
  | [] => []
  | row :: rest =>
      affineUnaryTriplePayloadRowOutput forms row ++
        affineUnaryTriplePayloadRowOutputFamily forms rest

/-- The affine-map core is reused verbatim.  `boundary` replaces only the
core's otherwise-halting malformed-loader target: on well-formed rows that
target is reached precisely after the internal `frameEnd`. -/
private inductive AffineUnaryTriplePayloadLabel
    (forms : List AffineUnaryTripleForm)
  | core (label : AffineUnaryTripleMapLabel forms)
  | boundary
  | emitBoundary (symbol : UnaryFrameSym)
  | payload
  | emitPayload (symbol : UnaryFrameSym)
  | clearPayloadBuffer
  | finish
deriving Fintype

private noncomputable instance (forms : List AffineUnaryTripleForm) :
    DecidableEq (AffineUnaryTriplePayloadLabel forms) := Classical.decEq _

/-- Relabel the complete existing affine core, redirecting only its loader's
invalid label to the new row-boundary continuation. -/
private def affineUnaryTriplePayloadTag
    (forms : List AffineUnaryTripleForm) :
    AffineUnaryTripleMapLabel forms → AffineUnaryTriplePayloadLabel forms
  | .loader .invalid => .boundary
  | label => .core label

/-- Fixed payload-preserving affine-map controller. -/
def affineUnaryTriplePayloadFamilyRevProgram
    (forms : List AffineUnaryTripleForm) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineUnaryTriplePayloadLabel forms
  main := .core (.loader .load₁)
  op
    | .core label => affineUnaryTripleMapRelabelOp
        (affineUnaryTriplePayloadTag forms)
        ((affineUnaryTripleMapFamilyRevProgram forms).op label)
    | .boundary => .popInput .finish (.emitBoundary)
    | .emitBoundary symbol => .pushOutput .frameEnd (.emitPayload symbol)
    | .payload => .popInput .finish (.emitPayload)
    | .emitPayload symbol => .pushOutput symbol
        (if symbol = .frameEnd then .clearPayloadBuffer else .payload)
    | .clearPayloadBuffer => .popWork₁
        (.core (.loader .load₁)) (fun _ => .finish)
    | .finish => .halt

private def affineUnaryTriplePayloadCfg
    {forms : List AffineUnaryTripleForm}
    (label : AffineUnaryTriplePayloadLabel forms)
    (buffer₁ : Option UnaryFrameSym) (input output work₁ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg (affineUnaryTriplePayloadFamilyRevProgram forms) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := work₁
  work₂ := []
  counter₁ := first
  counter₂ := second
  counter₃ := third

/-- Clean row entry of the payload-preserving source. -/
def affineUnaryTriplePayloadFamilyLoopCfg
    (forms : List AffineUnaryTripleForm)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineUnaryTriplePayloadFamilyRevProgram forms) :=
  affineUnaryTriplePayloadCfg (.core (.loader .load₁)) none input output
    [] [] [] []

private def liftAffineUnaryTriplePayloadCfg
    {forms : List AffineUnaryTripleForm}
    (c : BuilderCfg (affineUnaryTripleMapFamilyRevProgram forms)) :
    BuilderCfg (affineUnaryTriplePayloadFamilyRevProgram forms) :=
  affineUnaryTripleMapRelabelCfg
    (affineUnaryTriplePayloadTag forms) c

private theorem affineUnaryTriplePayload_op_core
    {forms : List AffineUnaryTripleForm}
    (label : AffineUnaryTripleMapLabel forms)
    (hexit : label ≠ .loader .invalid) :
    (affineUnaryTriplePayloadFamilyRevProgram forms).op
        (affineUnaryTriplePayloadTag forms label) =
      affineUnaryTripleMapRelabelOp (affineUnaryTriplePayloadTag forms)
        ((affineUnaryTripleMapFamilyRevProgram forms).op label) := by
  cases label <;>
    simp_all [affineUnaryTriplePayloadTag,
      affineUnaryTriplePayloadFamilyRevProgram]

private theorem liftAffineUnaryTriplePayload_step
    {forms : List AffineUnaryTripleForm}
    (c : BuilderCfg (affineUnaryTripleMapFamilyRevProgram forms))
    (hexit : c.label ≠ some (.loader .invalid)) :
    step (affineUnaryTriplePayloadFamilyRevProgram forms)
        (liftAffineUnaryTriplePayloadCfg c) =
      Option.map liftAffineUnaryTriplePayloadCfg
        (step (affineUnaryTripleMapFamilyRevProgram forms) c) := by
  unfold step
  rw [show (liftAffineUnaryTriplePayloadCfg c).label =
    c.label.map (affineUnaryTriplePayloadTag forms) by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠
          (AffineUnaryTripleMapLabel.loader .invalid :
            AffineUnaryTripleMapLabel forms) := by
        intro h
        subst label
        exact hexit hlabel
      change some (stepOp
          ((affineUnaryTriplePayloadFamilyRevProgram forms).op
            (affineUnaryTriplePayloadTag forms label))
          (liftAffineUnaryTriplePayloadCfg c)) =
        some (liftAffineUnaryTriplePayloadCfg
          (stepOp ((affineUnaryTripleMapFamilyRevProgram forms).op label) c))
      rw [affineUnaryTriplePayload_op_core label hlabelExit]
      exact congrArg some
        (affineUnaryTripleMapRelabel_stepOp
          (Q := affineUnaryTriplePayloadFamilyRevProgram forms)
          (affineUnaryTriplePayloadTag forms)
          ((affineUnaryTripleMapFamilyRevProgram forms).op label) c)

private theorem affineUnaryTriplePayload_haltExit_no_return
    {Gamma Delta : Type} {P : Program Gamma Delta} (exit : P.Label)
    (hop : P.op exit = Op.halt) (a b : BuilderCfg P)
    (ha : a.label = some exit) (hb : b.label ≠ none) : ∀ n : Nat,
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
      apply hb
      simpa [halted] using hlabel.symm
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step P))^[n] (step P halted) ≠ some b
      have hnone : step P halted = none := rfl
      rw [hnone, affineUnaryTripleMap_iterate_bind_none]
      simp

private theorem affineUnaryTriplePayload_lift_iterations
    {Gamma Delta : Type} {P Q : Program Gamma Delta} (exit : P.Label)
    (hop : P.op exit = Op.halt) (tr : BuilderCfg P → BuilderCfg Q)
    (hstep : ∀ c, c.label ≠ some exit →
      step Q (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label ≠ none) : ∀ n : Nat,
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
        exact affineUnaryTriplePayload_haltExit_no_return
          exit hop a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, affineUnaryTripleMap_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineUnaryTriplePayload_core_one
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTriplePayloadFamilyRevProgram forms))
      (affineUnaryTriplePayloadFamilyLoopCfg forms
        (encodeAffineUnaryTripleSeed seed ++ tail) output)
      (some (affineUnaryTriplePayloadFamilyLoopCfg forms tail
        ((encodeUnaryFrame (affineUnaryTripleMap forms seed)).reverse ++
          output)))
      (affineUnaryTripleMapFamilyOneSteps forms seed) := by
  have sourceRun := affineUnaryTripleMapFamily_one forms seed tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  have hlift := affineUnaryTriplePayload_lift_iterations
    (P := affineUnaryTripleMapFamilyRevProgram forms)
    (Q := affineUnaryTriplePayloadFamilyRevProgram forms)
    (.loader .invalid) rfl liftAffineUnaryTriplePayloadCfg
    liftAffineUnaryTriplePayload_step (a :=
      affineUnaryTripleMapFamilyLoopCfg forms
        (encodeAffineUnaryTripleSeed seed ++ tail) output)
    (b := affineUnaryTripleMapFamilyLoopCfg forms tail
      ((encodeUnaryFrame (affineUnaryTripleMap forms seed)).reverse ++
        output)) (by
          change some (AffineUnaryTripleMapLabel.loader
            UnaryTripleLoaderLabel.load₁) ≠ none
          simp)
    sourceRun.steps sourceRun.evals_in_steps
  simpa [affineUnaryTriplePayloadFamilyLoopCfg,
    affineUnaryTriplePayloadCfg, liftAffineUnaryTriplePayloadCfg,
    affineUnaryTripleMapFamilyLoopCfg, affineUnaryTripleMapFamilyCfg,
    affineUnaryTripleMapRelabelCfg,
    affineUnaryTriplePayloadTag] using hlift

private theorem affineUnaryTriplePayload_payload_eval
    {forms : List AffineUnaryTripleForm}
    (payload tail output : List UnaryFrameSym)
    (buffer₁ : Option UnaryFrameSym)
    (hpayload : ∀ symbol ∈ payload, symbol ≠ .frameEnd) :
    (flip Option.bind
      (step (affineUnaryTriplePayloadFamilyRevProgram forms)))^[
        2 * payload.length + 3]
      (some (affineUnaryTriplePayloadCfg .payload buffer₁
        (payload ++ .frameEnd :: tail) output [] [] [] [])) =
      some (affineUnaryTriplePayloadFamilyLoopCfg forms tail
        (.frameEnd :: payload.reverse ++ output)) := by
  induction payload generalizing buffer₁ output with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ .frameEnd := hpayload symbol (by simp)
      have hrest : ∀ item ∈ rest, item ≠ .frameEnd := by
        intro item hitem
        exact hpayload item (by simp [hitem])
      rw [show 2 * (symbol :: rest).length + 3 =
          (2 * rest.length + 3) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      have htwo :
          flip Option.bind
              (step (affineUnaryTriplePayloadFamilyRevProgram forms))
            (flip Option.bind
              (step (affineUnaryTriplePayloadFamilyRevProgram forms))
              (some (affineUnaryTriplePayloadCfg .payload buffer₁
                ((symbol :: rest) ++ .frameEnd :: tail)
                output [] [] [] []))) =
            some (affineUnaryTriplePayloadCfg .payload (some symbol)
              (rest ++ .frameEnd :: tail) (symbol :: output) [] [] [] []) := by
        have hpop :
            step (affineUnaryTriplePayloadFamilyRevProgram forms)
                (affineUnaryTriplePayloadCfg .payload buffer₁
                  ((symbol :: rest) ++ .frameEnd :: tail)
                  output [] [] [] []) =
              some (affineUnaryTriplePayloadCfg (.emitPayload symbol)
                (some symbol) (rest ++ .frameEnd :: tail)
                output [] [] [] []) := by
          rfl
        have hemit :
            step (affineUnaryTriplePayloadFamilyRevProgram forms)
                (affineUnaryTriplePayloadCfg (.emitPayload symbol)
                  (some symbol) (rest ++ .frameEnd :: tail)
                  output [] [] [] []) =
              some (affineUnaryTriplePayloadCfg .payload (some symbol)
                (rest ++ .frameEnd :: tail) (symbol :: output)
                [] [] [] []) := by
          change some (affineUnaryTriplePayloadCfg
            (if symbol = .frameEnd then .clearPayloadBuffer else .payload)
            (some symbol) (rest ++ .frameEnd :: tail)
            (symbol :: output) [] [] [] []) = _
          rw [if_neg hsymbol]
        have hinner :
            flip Option.bind
                (step (affineUnaryTriplePayloadFamilyRevProgram forms))
                (some (affineUnaryTriplePayloadCfg .payload buffer₁
                  ((symbol :: rest) ++ .frameEnd :: tail)
                  output [] [] [] [])) =
              some (affineUnaryTriplePayloadCfg (.emitPayload symbol)
                (some symbol) (rest ++ .frameEnd :: tail)
                output [] [] [] []) := by
          change step (affineUnaryTriplePayloadFamilyRevProgram forms)
            (affineUnaryTriplePayloadCfg .payload buffer₁
              ((symbol :: rest) ++ .frameEnd :: tail)
              output [] [] [] []) = _
          exact hpop
        rw [hinner]
        change step (affineUnaryTriplePayloadFamilyRevProgram forms)
          (affineUnaryTriplePayloadCfg (.emitPayload symbol)
            (some symbol) (rest ++ .frameEnd :: tail)
            output [] [] [] []) = _
        exact hemit
      rw [htwo]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (symbol :: output) (some symbol) hrest

private theorem affineUnaryTriplePayload_boundary_eval
    {forms : List AffineUnaryTripleForm}
    (payload tail output : List UnaryFrameSym)
    (hpayload : ∀ symbol ∈ payload, symbol ≠ .frameEnd) :
    (flip Option.bind
      (step (affineUnaryTriplePayloadFamilyRevProgram forms)))^[
        2 * payload.length + 5]
      (some (affineUnaryTriplePayloadFamilyLoopCfg forms
        (.frameEnd :: (payload ++ .frameEnd :: tail)) output)) =
      some (affineUnaryTriplePayloadFamilyLoopCfg forms tail
        (.frameEnd :: payload.reverse ++ .frameEnd :: output)) := by
  cases payload with
  | nil => rfl
  | cons symbol rest =>
      have hsymbol : symbol ≠ .frameEnd := hpayload symbol (by simp)
      have hrest : ∀ item ∈ rest, item ≠ .frameEnd := by
        intro item hitem
        exact hpayload item (by simp [hitem])
      rw [show 2 * (symbol :: rest).length + 5 =
          (2 * rest.length + 3) + 1 + 1 + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hfour :
          flip Option.bind
              (step (affineUnaryTriplePayloadFamilyRevProgram forms))
            (flip Option.bind
              (step (affineUnaryTriplePayloadFamilyRevProgram forms))
              (flip Option.bind
                (step (affineUnaryTriplePayloadFamilyRevProgram forms))
                (flip Option.bind
                  (step (affineUnaryTriplePayloadFamilyRevProgram forms))
                  (some (affineUnaryTriplePayloadFamilyLoopCfg forms
                    (.frameEnd ::
                      (symbol :: rest ++ .frameEnd :: tail)) output))))) =
            some (affineUnaryTriplePayloadCfg .payload (some symbol)
              (rest ++ .frameEnd :: tail)
              (symbol :: .frameEnd :: output) [] [] [] []) := by
        let c₁ := affineUnaryTriplePayloadCfg (forms := forms) .boundary
          (some .frameEnd) (symbol :: (rest ++ .frameEnd :: tail))
          output [] [] [] []
        let c₂ := affineUnaryTriplePayloadCfg (forms := forms)
          (.emitBoundary symbol) (some symbol)
          (rest ++ .frameEnd :: tail) output [] [] [] []
        let c₃ := affineUnaryTriplePayloadCfg (forms := forms)
          (.emitPayload symbol) (some symbol)
          (rest ++ .frameEnd :: tail) (.frameEnd :: output) [] [] [] []
        let c₄ := affineUnaryTriplePayloadCfg (forms := forms) .payload
          (some symbol) (rest ++ .frameEnd :: tail)
          (symbol :: .frameEnd :: output) [] [] [] []
        have hs₁ : step (affineUnaryTriplePayloadFamilyRevProgram forms)
            (affineUnaryTriplePayloadFamilyLoopCfg forms
              (.frameEnd :: (symbol :: rest ++ .frameEnd :: tail)) output) =
            some c₁ := by
          rfl
        have hs₂ : step (affineUnaryTriplePayloadFamilyRevProgram forms) c₁ =
            some c₂ := by
          rfl
        have hs₃ : step (affineUnaryTriplePayloadFamilyRevProgram forms) c₂ =
            some c₃ := by
          rfl
        have hs₄ : step (affineUnaryTriplePayloadFamilyRevProgram forms) c₃ =
            some c₄ := by
          change some (affineUnaryTriplePayloadCfg
            (if symbol = .frameEnd then .clearPayloadBuffer else .payload)
            (some symbol) (rest ++ .frameEnd :: tail)
            (symbol :: .frameEnd :: output) [] [] [] []) = some c₄
          rw [if_neg hsymbol]
        have hi₁ : flip Option.bind
              (step (affineUnaryTriplePayloadFamilyRevProgram forms))
              (some (affineUnaryTriplePayloadFamilyLoopCfg forms
                (.frameEnd :: (symbol :: rest ++ .frameEnd :: tail)) output)) =
            some c₁ := by
          change step (affineUnaryTriplePayloadFamilyRevProgram forms)
            (affineUnaryTriplePayloadFamilyLoopCfg forms
              (.frameEnd :: (symbol :: rest ++ .frameEnd :: tail)) output) = _
          exact hs₁
        have hi₂ : flip Option.bind
              (step (affineUnaryTriplePayloadFamilyRevProgram forms))
              (some c₁) = some c₂ := by
          change step (affineUnaryTriplePayloadFamilyRevProgram forms) c₁ = _
          exact hs₂
        have hi₃ : flip Option.bind
              (step (affineUnaryTriplePayloadFamilyRevProgram forms))
              (some c₂) = some c₃ := by
          change step (affineUnaryTriplePayloadFamilyRevProgram forms) c₂ = _
          exact hs₃
        rw [hi₁, hi₂, hi₃]
        change step (affineUnaryTriplePayloadFamilyRevProgram forms) c₃ = _
        simpa [c₄] using hs₄
      rw [hfour]
      simpa [List.reverse_cons, List.append_assoc] using
        affineUnaryTriplePayload_payload_eval
          rest tail (symbol :: .frameEnd :: output) (some symbol) hrest

/-- Exact cost of one seed-plus-payload row. -/
def affineUnaryTriplePayloadFamilyOneSteps
    (forms : List AffineUnaryTripleForm)
    (row : AffineUnaryTriplePayloadRow) : Nat :=
  affineUnaryTripleMapFamilyOneSteps forms row.seed +
    (2 * row.payload.length + 5)

private def affineUnaryTriplePayloadFamily_one
    (forms : List AffineUnaryTripleForm)
    (row : AffineUnaryTriplePayloadRow) (tail output : List UnaryFrameSym)
    (hpayload : ∀ symbol ∈ row.payload, symbol ≠ .frameEnd) :
    EvalsToInTime
      (step (affineUnaryTriplePayloadFamilyRevProgram forms))
      (affineUnaryTriplePayloadFamilyLoopCfg forms
        (encodeAffineUnaryTriplePayloadRow row ++ tail) output)
      (some (affineUnaryTriplePayloadFamilyLoopCfg forms tail
        ((affineUnaryTriplePayloadRowOutput forms row).reverse ++ output)))
      (affineUnaryTriplePayloadFamilyOneSteps forms row) := by
  let rowTail :=
    .frameEnd :: (row.payload ++ .frameEnd :: tail)
  let prefixOutput :=
    (encodeUnaryFrame (affineUnaryTripleMap forms row.seed)).reverse ++ output
  have hcore := affineUnaryTriplePayload_core_one
    forms row.seed rowTail output
  have hboundary := affineUnaryTriplePayload_boundary_eval
    (forms := forms) row.payload tail prefixOutput hpayload
  have hboundaryRun : EvalsToInTime
      (step (affineUnaryTriplePayloadFamilyRevProgram forms))
      (affineUnaryTriplePayloadFamilyLoopCfg forms rowTail prefixOutput)
      (some (affineUnaryTriplePayloadFamilyLoopCfg forms tail
        (.frameEnd :: row.payload.reverse ++ .frameEnd :: prefixOutput)))
      (2 * row.payload.length + 5) := by
    exact ⟨⟨2 * row.payload.length + 5, by
      simpa [rowTail] using hboundary⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step (affineUnaryTriplePayloadFamilyRevProgram forms))
    (affineUnaryTripleMapFamilyOneSteps forms row.seed)
    (2 * row.payload.length + 5) _
    (affineUnaryTriplePayloadFamilyLoopCfg forms rowTail prefixOutput) _
    (by simpa [rowTail, prefixOutput,
      encodeAffineUnaryTriplePayloadRow, List.append_assoc] using hcore)
    hboundaryRun
  convert full using 1
  · simp [rowTail, encodeAffineUnaryTriplePayloadRow, List.append_assoc]
  · simp [prefixOutput, affineUnaryTriplePayloadRowOutput,
      List.reverse_append, List.append_assoc]
  · simp [affineUnaryTriplePayloadFamilyOneSteps]
    omega

/-- Exact complete-family cost, including the three-step empty-input halt. -/
def affineUnaryTriplePayloadFamilySteps
    (forms : List AffineUnaryTripleForm) :
    List AffineUnaryTriplePayloadRow → Nat
  | [] => 3
  | row :: rest =>
      affineUnaryTriplePayloadFamilyOneSteps forms row +
        affineUnaryTriplePayloadFamilySteps forms rest

private def affineUnaryTriplePayloadFamily_runFrom
    (forms : List AffineUnaryTripleForm)
    (rows : List AffineUnaryTriplePayloadRow)
    (output : List UnaryFrameSym)
    (hpayload : ∀ row ∈ rows, ∀ symbol ∈ row.payload,
      symbol ≠ .frameEnd) :
    EvalsToInTime
      (step (affineUnaryTriplePayloadFamilyRevProgram forms))
      (affineUnaryTriplePayloadFamilyLoopCfg forms
        (encodeAffineUnaryTriplePayloadRowFamily rows) output)
      (some (haltCfg (affineUnaryTriplePayloadFamilyRevProgram forms)
        ((affineUnaryTriplePayloadRowOutputFamily forms rows).reverse ++
          output)))
      (affineUnaryTriplePayloadFamilySteps forms rows) := by
  induction rows generalizing output with
  | nil =>
      exact ⟨⟨3, rfl⟩, le_rfl⟩
  | cons row rest ih =>
      let rowOutput :=
        (affineUnaryTriplePayloadRowOutput forms row).reverse ++ output
      have hrow : ∀ symbol ∈ row.payload, symbol ≠ .frameEnd := by
        intro symbol hsymbol
        exact hpayload row (by simp) symbol hsymbol
      have hrest : ∀ item ∈ rest, ∀ symbol ∈ item.payload,
          symbol ≠ .frameEnd := by
        intro item hitem symbol hsymbol
        exact hpayload item (by simp [hitem]) symbol hsymbol
      have hfirst := affineUnaryTriplePayloadFamily_one
        forms row (encodeAffineUnaryTriplePayloadRowFamily rest) output hrow
      have htail := ih rowOutput hrest
      let full := EvalsToInTime.trans
        (step (affineUnaryTriplePayloadFamilyRevProgram forms))
        (affineUnaryTriplePayloadFamilyOneSteps forms row)
        (affineUnaryTriplePayloadFamilySteps forms rest) _
        (affineUnaryTriplePayloadFamilyLoopCfg forms
          (encodeAffineUnaryTriplePayloadRowFamily rest) rowOutput) _
        hfirst htail
      convert full using 1
      · simp [encodeAffineUnaryTriplePayloadRowFamily]
      · simp [affineUnaryTriplePayloadRowOutputFamily, rowOutput,
          List.reverse_append, List.append_assoc]
      · simp [affineUnaryTriplePayloadFamilySteps]
        omega

/-- One fixed machine maps every well-formed seed-first row family to its
affine-prefix-plus-payload stream and halts with clean scratch state. -/
def affineUnaryTriplePayloadFamily_run
    (forms : List AffineUnaryTripleForm)
    (rows : List AffineUnaryTriplePayloadRow)
    (hpayload : ∀ row ∈ rows, ∀ symbol ∈ row.payload,
      symbol ≠ .frameEnd) :
    EvalsToInTime
      (step (affineUnaryTriplePayloadFamilyRevProgram forms))
      (initialCfg (affineUnaryTriplePayloadFamilyRevProgram forms)
        (encodeAffineUnaryTriplePayloadRowFamily rows))
      (some (haltCfg (affineUnaryTriplePayloadFamilyRevProgram forms)
        (affineUnaryTriplePayloadRowOutputFamily forms rows).reverse))
      (affineUnaryTriplePayloadFamilySteps forms rows) := by
  have hinit : affineUnaryTriplePayloadFamilyLoopCfg forms
      (encodeAffineUnaryTriplePayloadRowFamily rows) [] =
        initialCfg (affineUnaryTriplePayloadFamilyRevProgram forms)
          (encodeAffineUnaryTriplePayloadRowFamily rows) := rfl
  rw [← hinit]
  simpa only [List.append_nil] using
    affineUnaryTriplePayloadFamily_runFrom forms rows [] hpayload

/-- Fixed coefficient for the payload-preserving quadratic bound. -/
def affineUnaryTriplePayloadFamilyStepCoeff
    (forms : List AffineUnaryTripleForm) : Nat :=
  affineUnaryTripleMapFamilyStepCoeff forms + 6

@[simp] theorem encodeAffineUnaryTriplePayloadRow_length
    (row : AffineUnaryTriplePayloadRow) :
    (encodeAffineUnaryTriplePayloadRow row).length =
      row.seed.first + row.seed.second + row.seed.third +
        row.payload.length + 5 := by
  simp [encodeAffineUnaryTriplePayloadRow]
  omega

/-- One row remains quadratic in its complete explicit byte encoding. -/
theorem affineUnaryTriplePayloadFamilyOneSteps_le
    (forms : List AffineUnaryTripleForm)
    (row : AffineUnaryTriplePayloadRow) :
    affineUnaryTriplePayloadFamilyOneSteps forms row ≤
      affineUnaryTriplePayloadFamilyStepCoeff forms *
        (encodeAffineUnaryTriplePayloadRow row).length ^ 2 := by
  let rowLength := (encodeAffineUnaryTriplePayloadRow row).length
  let seedLength := row.seed.first + row.seed.second + row.seed.third + 1
  let coeff := affineUnaryTripleMapFamilyStepCoeff forms
  have hrow : 1 ≤ rowLength := by
    simp [rowLength]
  have hrowSquare : rowLength ≤ rowLength ^ 2 := by
    nlinarith
  have hseedLength : seedLength ≤ rowLength := by
    simp [seedLength, rowLength]
    omega
  have hseedSquare : seedLength ^ 2 ≤ rowLength ^ 2 := by
    nlinarith
  have hcoreSource := affineUnaryTripleMapFamilyOneSteps_le forms row.seed
  have hcore : affineUnaryTripleMapFamilyOneSteps forms row.seed ≤
      coeff * rowLength ^ 2 :=
    hcoreSource.trans (Nat.mul_le_mul_left coeff (by
      simpa [seedLength] using hseedSquare))
  have hpayload : row.payload.length ≤ rowLength := by
    simp [rowLength]
    omega
  have hrowFive : 5 ≤ rowLength := by
    simp [rowLength]
  have hcopy : 2 * row.payload.length + 5 ≤ 6 * rowLength ^ 2 := by
    calc
      2 * row.payload.length + 5 ≤ 2 * rowLength + 5 := by omega
      _ ≤ 3 * rowLength := by omega
      _ ≤ 6 * rowLength ^ 2 := by nlinarith
  calc
    affineUnaryTriplePayloadFamilyOneSteps forms row =
        affineUnaryTripleMapFamilyOneSteps forms row.seed +
          (2 * row.payload.length + 5) := by rfl
    _ ≤ coeff * rowLength ^ 2 + 6 * rowLength ^ 2 :=
      Nat.add_le_add hcore hcopy
    _ = affineUnaryTriplePayloadFamilyStepCoeff forms *
        (encodeAffineUnaryTriplePayloadRow row).length ^ 2 := by
      simp [affineUnaryTriplePayloadFamilyStepCoeff, coeff, rowLength]
      ring

/-- Complete-family cost is quadratic in the concatenated seed-and-payload
stream. -/
theorem affineUnaryTriplePayloadFamilySteps_le
    (forms : List AffineUnaryTripleForm)
    (rows : List AffineUnaryTriplePayloadRow) :
    affineUnaryTriplePayloadFamilySteps forms rows ≤
      affineUnaryTriplePayloadFamilyStepCoeff forms *
        (encodeAffineUnaryTriplePayloadRowFamily rows).length ^ 2 + 3 := by
  induction rows with
  | nil => simp [affineUnaryTriplePayloadFamilySteps,
      encodeAffineUnaryTriplePayloadRowFamily]
  | cons row rest ih =>
      let headLength := (encodeAffineUnaryTriplePayloadRow row).length
      let restLength :=
        (encodeAffineUnaryTriplePayloadRowFamily rest).length
      let coeff := affineUnaryTriplePayloadFamilyStepCoeff forms
      have hhead := affineUnaryTriplePayloadFamilyOneSteps_le forms row
      calc
        affineUnaryTriplePayloadFamilySteps forms (row :: rest) =
            affineUnaryTriplePayloadFamilyOneSteps forms row +
              affineUnaryTriplePayloadFamilySteps forms rest := by rfl
        _ ≤ coeff * headLength ^ 2 + (coeff * restLength ^ 2 + 3) :=
          Nat.add_le_add (by simpa [coeff, headLength] using hhead)
            (by simpa [coeff, restLength] using ih)
        _ = coeff * (headLength ^ 2 + restLength ^ 2) + 3 := by ring
        _ ≤ coeff * (headLength + restLength) ^ 2 + 3 := by
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left
          nlinarith [Nat.zero_le (2 * headLength * restLength)]
        _ = affineUnaryTriplePayloadFamilyStepCoeff forms *
            (encodeAffineUnaryTriplePayloadRowFamily (row :: rest)).length ^ 2 +
              3 := by
          simp [coeff, headLength, restLength,
            encodeAffineUnaryTriplePayloadRowFamily]

/-- Typed domain used by the compiled total machine: every row payload is
free of the outer boundary marker. -/
structure AffineUnaryTriplePayloadFamily where
  rows : List AffineUnaryTriplePayloadRow
  payload_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.payload,
    symbol ≠ UnaryFrameSym.frameEnd

/-- Concrete input encoding of a well-formed payload family. -/
def encodeAffineUnaryTriplePayloadFamily
    (family : AffineUnaryTriplePayloadFamily) : List UnaryFrameSym :=
  encodeAffineUnaryTriplePayloadRowFamily family.rows

/-- The compiled fixed controller computes the reversed affine-prefix and
payload family in quadratic time. -/
noncomputable def
    affineUnaryTriplePayloadFamilyRev_computableInPolyTime
    (forms : List AffineUnaryTripleForm) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTriplePayloadFamily id
      (fun family : AffineUnaryTriplePayloadFamily =>
        (affineUnaryTriplePayloadRowOutputFamily forms family.rows).reverse) where
  tm := compile (affineUnaryTriplePayloadFamilyRevProgram forms)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C (affineUnaryTriplePayloadFamilyStepCoeff forms) *
    Polynomial.X ^ 2 + 3
  outputsFun := fun family => by
    have builderRun := affineUnaryTriplePayloadFamily_run forms family.rows
      family.payload_frameEnd_free
    have compiledRun := compile_evalsToInTime
      (affineUnaryTriplePayloadFamilyRevProgram forms) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile (affineUnaryTriplePayloadFamilyRevProgram forms)).step
        (_root_.Turing.initList
          (compile (affineUnaryTriplePayloadFamilyRevProgram forms))
          (encodeAffineUnaryTriplePayloadRowFamily family.rows))
        (some (_root_.Turing.haltList
          (compile (affineUnaryTriplePayloadFamilyRevProgram forms))
          (affineUnaryTriplePayloadRowOutputFamily forms family.rows).reverse))
        (affineUnaryTriplePayloadFamilySteps forms family.rows) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : affineUnaryTriplePayloadFamilySteps forms family.rows ≤
        (Polynomial.C (affineUnaryTriplePayloadFamilyStepCoeff forms) *
          Polynomial.X ^ 2 + 3).eval
            (encodeAffineUnaryTriplePayloadRowFamily family.rows).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_ofNat] using
        affineUnaryTriplePayloadFamilySteps_le forms family.rows
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile (affineUnaryTriplePayloadFamilyRevProgram forms)).step
        (_root_.Turing.initList
          (compile (affineUnaryTriplePayloadFamilyRevProgram forms))
          (encodeAffineUnaryTriplePayloadRowFamily family.rows))
        (some (_root_.Turing.haltList
          (compile (affineUnaryTriplePayloadFamilyRevProgram forms))
          (affineUnaryTriplePayloadRowOutputFamily forms family.rows).reverse))
        ((Polynomial.C (affineUnaryTriplePayloadFamilyStepCoeff forms) *
          Polynomial.X ^ 2 + 3).eval
            (encodeAffineUnaryTriplePayloadRowFamily family.rows).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [encodeAffineUnaryTriplePayloadFamily,
      _root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward payload-preserving affine source. -/
noncomputable def affineUnaryTriplePayloadFamily_computableInPolyTime
    (forms : List AffineUnaryTripleForm) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTriplePayloadFamily id
      (fun family : AffineUnaryTriplePayloadFamily =>
        affineUnaryTriplePayloadRowOutputFamily forms family.rows) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineUnaryTriplePayloadFamilyRev_computableInPolyTime forms)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
