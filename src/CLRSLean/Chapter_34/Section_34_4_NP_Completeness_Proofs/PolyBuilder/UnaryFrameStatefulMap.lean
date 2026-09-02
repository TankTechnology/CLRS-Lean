import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Reusable stateful unary-frame maps

Many concrete Cook--Levin sources only need a fixed finite-state streaming
pass which emits either zero or one symbol for each input symbol.  This module
packages that pattern once as an explicit TM2, together with exact semantics
and a linear running-time bound.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite-control specification of a streaming filter-map. -/
structure UnaryFrameStatefulMapSpec (Mode : Type) where
  initial : Mode
  action : Mode → UnaryFrameSym → Option UnaryFrameSym × Mode

/-- Pure semantics from an arbitrary current finite-control mode. -/
def rewriteUnaryFrameStatefulFrom {Mode : Type}
    (spec : UnaryFrameStatefulMapSpec Mode) :
    Mode → List UnaryFrameSym → List UnaryFrameSym
  | _, [] => []
  | mode, symbol :: rest =>
      let result := spec.action mode symbol
      match result.1 with
      | none => rewriteUnaryFrameStatefulFrom spec result.2 rest
      | some emitted => emitted ::
          rewriteUnaryFrameStatefulFrom spec result.2 rest

/-- Pure semantics from the specified initial mode. -/
def rewriteUnaryFrameStateful {Mode : Type}
    (spec : UnaryFrameStatefulMapSpec Mode)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStatefulFrom spec spec.initial input

/-- Fixed controller labels.  `emit` and `skip` make every input symbol cost
exactly two transitions, independent of the chosen action. -/
inductive UnaryFrameStatefulMapLabel (Mode : Type)
  | scan (mode : Mode)
  | emit (mode : Mode) (symbol : UnaryFrameSym)
  | skip (mode : Mode)
  | finish
deriving DecidableEq, Fintype

def unaryFrameStatefulMapTarget {Mode : Type}
    (spec : UnaryFrameStatefulMapSpec Mode)
    (mode : Mode) (symbol : UnaryFrameSym) :
    UnaryFrameStatefulMapLabel Mode :=
  match spec.action mode symbol with
  | (none, nextMode) => .skip nextMode
  | (some emitted, nextMode) => .emit nextMode emitted

/-- Reverse-output program implementing an arbitrary fixed specification. -/
def unaryFrameStatefulMapRevProgram {Mode : Type}
    [DecidableEq Mode] [Fintype Mode]
    (spec : UnaryFrameStatefulMapSpec Mode) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameStatefulMapLabel Mode
  main := .scan spec.initial
  op
    | .scan mode => .popInput .finish fun symbol =>
        unaryFrameStatefulMapTarget spec mode symbol
    | .emit mode symbol => .pushOutput symbol (.scan mode)
    | .skip mode => .jump (.scan mode)
    | .finish => .halt

private def unaryFrameStatefulMapCfg {Mode : Type}
    [DecidableEq Mode] [Fintype Mode]
    (spec : UnaryFrameStatefulMapSpec Mode)
    (label : UnaryFrameStatefulMapLabel Mode)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameStatefulMapRevProgram spec) :=
  { label := some label
    buffer₁ := buffer
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := []
    work₂ := []
    counter₁ := []
    counter₂ := []
    counter₃ := [] }

private def unaryFrameStatefulMapLoopCfg {Mode : Type}
    [DecidableEq Mode] [Fintype Mode]
    (spec : UnaryFrameStatefulMapSpec Mode)
    (mode : Mode) (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameStatefulMapRevProgram spec) :=
  unaryFrameStatefulMapCfg spec (.scan mode) buffer input output

private theorem unaryFrameStatefulMap_phase_eval {Mode : Type}
    [DecidableEq Mode] [Fintype Mode]
    (spec : UnaryFrameStatefulMapSpec Mode)
    (mode : Mode) (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    (flip Option.bind
      (step (unaryFrameStatefulMapRevProgram spec)))^[
        2 * input.length + 1]
      (some (unaryFrameStatefulMapLoopCfg
        spec mode buffer input output)) =
      some (unaryFrameStatefulMapCfg spec .finish none []
        ((rewriteUnaryFrameStatefulFrom spec mode input).reverse ++
          output)) := by
  induction input generalizing mode buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      rcases haction : spec.action mode symbol with
        ⟨emitted, nextMode⟩
      cases emitted with
      | none =>
          have htarget : unaryFrameStatefulMapTarget spec mode symbol =
              .skip nextMode := by
            simp [unaryFrameStatefulMapTarget, haction]
          have hfirst :
              step (unaryFrameStatefulMapRevProgram spec)
                  (unaryFrameStatefulMapLoopCfg spec mode buffer
                    (symbol :: rest) output) =
                some (unaryFrameStatefulMapCfg spec
                  (.skip nextMode) (some symbol) rest output) := by
            change some (unaryFrameStatefulMapCfg spec
              (unaryFrameStatefulMapTarget spec mode symbol)
              (some symbol) rest output) = _
            rw [htarget]
          have hsecond :
              step (unaryFrameStatefulMapRevProgram spec)
                  (unaryFrameStatefulMapCfg spec
                    (.skip nextMode) (some symbol) rest output) =
                some (unaryFrameStatefulMapLoopCfg spec nextMode
                  (some symbol) rest output) := by
            rfl
          have hinner :
              flip Option.bind
                  (step (unaryFrameStatefulMapRevProgram spec))
                  (some (unaryFrameStatefulMapLoopCfg spec mode buffer
                    (symbol :: rest) output)) =
                some (unaryFrameStatefulMapCfg spec
                  (.skip nextMode) (some symbol) rest output) := by
            change step (unaryFrameStatefulMapRevProgram spec)
              (unaryFrameStatefulMapLoopCfg spec mode buffer
                (symbol :: rest) output) = _
            exact hfirst
          have htwo :
              flip Option.bind
                  (step (unaryFrameStatefulMapRevProgram spec))
                (flip Option.bind
                  (step (unaryFrameStatefulMapRevProgram spec))
                  (some (unaryFrameStatefulMapLoopCfg spec mode buffer
                    (symbol :: rest) output))) =
                some (unaryFrameStatefulMapLoopCfg spec nextMode
                  (some symbol) rest output) := by
            rw [hinner]
            change step (unaryFrameStatefulMapRevProgram spec)
              (unaryFrameStatefulMapCfg spec (.skip nextMode)
                (some symbol) rest output) = _
            exact hsecond
          rw [htwo]
          simpa [rewriteUnaryFrameStatefulFrom, haction] using
            ih nextMode (some symbol) output
      | some emitted =>
          have htarget : unaryFrameStatefulMapTarget spec mode symbol =
              .emit nextMode emitted := by
            simp [unaryFrameStatefulMapTarget, haction]
          have hfirst :
              step (unaryFrameStatefulMapRevProgram spec)
                  (unaryFrameStatefulMapLoopCfg spec mode buffer
                    (symbol :: rest) output) =
                some (unaryFrameStatefulMapCfg spec
                  (.emit nextMode emitted) (some symbol) rest output) := by
            change some (unaryFrameStatefulMapCfg spec
              (unaryFrameStatefulMapTarget spec mode symbol)
              (some symbol) rest output) = _
            rw [htarget]
          have hsecond :
              step (unaryFrameStatefulMapRevProgram spec)
                  (unaryFrameStatefulMapCfg spec
                    (.emit nextMode emitted) (some symbol) rest output) =
                some (unaryFrameStatefulMapLoopCfg spec nextMode
                  (some symbol) rest (emitted :: output)) := by
            rfl
          have hinner :
              flip Option.bind
                  (step (unaryFrameStatefulMapRevProgram spec))
                  (some (unaryFrameStatefulMapLoopCfg spec mode buffer
                    (symbol :: rest) output)) =
                some (unaryFrameStatefulMapCfg spec
                  (.emit nextMode emitted) (some symbol) rest output) := by
            change step (unaryFrameStatefulMapRevProgram spec)
              (unaryFrameStatefulMapLoopCfg spec mode buffer
                (symbol :: rest) output) = _
            exact hfirst
          have htwo :
              flip Option.bind
                  (step (unaryFrameStatefulMapRevProgram spec))
                (flip Option.bind
                  (step (unaryFrameStatefulMapRevProgram spec))
                  (some (unaryFrameStatefulMapLoopCfg spec mode buffer
                    (symbol :: rest) output))) =
                some (unaryFrameStatefulMapLoopCfg spec nextMode
                  (some symbol) rest (emitted :: output)) := by
            rw [hinner]
            change step (unaryFrameStatefulMapRevProgram spec)
              (unaryFrameStatefulMapCfg spec
                (.emit nextMode emitted) (some symbol) rest output) = _
            exact hsecond
          rw [htwo]
          simpa [rewriteUnaryFrameStatefulFrom, haction,
            List.reverse_cons, List.append_assoc] using
            ih nextMode (some symbol) (emitted :: output)

/-- Exact linear transition count, including the final halt. -/
def unaryFrameStatefulMapSteps (input : List UnaryFrameSym) : Nat :=
  2 * input.length + 2

/-- The reverse-output controller implements the pure stateful rewrite. -/
def unaryFrameStatefulMapRev_run {Mode : Type}
    [DecidableEq Mode] [Fintype Mode]
    (spec : UnaryFrameStatefulMapSpec Mode)
    (input : List UnaryFrameSym) :
    EvalsToInTime
      (step (unaryFrameStatefulMapRevProgram spec))
      (initialCfg (unaryFrameStatefulMapRevProgram spec) input)
      (some (haltCfg (unaryFrameStatefulMapRevProgram spec)
        (rewriteUnaryFrameStateful spec input).reverse))
      (unaryFrameStatefulMapSteps input) := by
  let beforeHalt := unaryFrameStatefulMapCfg spec .finish none []
    (rewriteUnaryFrameStateful spec input).reverse
  have hphase := unaryFrameStatefulMap_phase_eval spec spec.initial none
    input []
  have hphaseRun : EvalsToInTime
      (step (unaryFrameStatefulMapRevProgram spec))
      (initialCfg (unaryFrameStatefulMapRevProgram spec) input)
      (some beforeHalt) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [beforeHalt, initialCfg, unaryFrameStatefulMapLoopCfg,
      unaryFrameStatefulMapCfg, rewriteUnaryFrameStateful,
      unaryFrameStatefulMapRevProgram] using hphase
  have hhalt : EvalsToInTime
      (step (unaryFrameStatefulMapRevProgram spec))
      beforeHalt
      (some (haltCfg (unaryFrameStatefulMapRevProgram spec)
        (rewriteUnaryFrameStateful spec input).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step (unaryFrameStatefulMapRevProgram spec))
    (2 * input.length + 1) 1 _ beforeHalt _ hphaseRun hhalt
  convert full using 1
  simp [unaryFrameStatefulMapSteps]
  omega

/-- Reversed stateful rewrite in linear polynomial time. -/
noncomputable def unaryFrameStatefulMapRev_computableInPolyTime
    {Mode : Type} [DecidableEq Mode] [Fintype Mode]
    (spec : UnaryFrameStatefulMapSpec Mode) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (rewriteUnaryFrameStateful spec input).reverse) where
  tm := compile (unaryFrameStatefulMapRevProgram spec)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun := fun input => by
    have builderRun := unaryFrameStatefulMapRev_run spec input
    have compiledRun := compile_evalsToInTime
      (unaryFrameStatefulMapRevProgram spec) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile (unaryFrameStatefulMapRevProgram spec)).step
        (_root_.Turing.initList
          (compile (unaryFrameStatefulMapRevProgram spec)) input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameStatefulMapRevProgram spec))
          (rewriteUnaryFrameStateful spec input).reverse))
        (unaryFrameStatefulMapSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameStatefulMapSteps input ≤
        (2 * Polynomial.X + 2).eval input.length := by
      simp [unaryFrameStatefulMapSteps]
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile (unaryFrameStatefulMapRevProgram spec)).step
        (_root_.Turing.initList
          (compile (unaryFrameStatefulMapRevProgram spec)) input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameStatefulMapRevProgram spec))
          (rewriteUnaryFrameStateful spec input).reverse))
        ((2 * Polynomial.X + 2).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward stateful rewrite in linear polynomial time. -/
noncomputable def unaryFrameStatefulMap_computableInPolyTime
    {Mode : Type} [DecidableEq Mode] [Fintype Mode]
    (spec : UnaryFrameStatefulMapSpec Mode) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameStateful spec) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameStatefulMapRev_computableInPolyTime spec)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
