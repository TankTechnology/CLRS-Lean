import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Reusable finite-state flat maps

This module verifies a fixed streaming transducer whose finite control carries
a mode and whose transition may emit a finite chunk.  A final chunk depending
on the terminal mode supports bounded look-ahead parsers: delayed symbols are
flushed when the input ends.

The direct prepend-output controller returns the reverse of the semantic
stream.  Composing it with the verified reversal controller gives the forward
map.  Both constructions are genuine fixed TM2 machines.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- A finite-state streaming transducer with a terminal flush action. -/
structure StatefulFlatMapSpec (Mode Γ Δ : Type) where
  initial : Mode
  action : Mode → Γ → List Δ × Mode
  finish : Mode → List Δ

/-- Pure semantics from an arbitrary current mode. -/
def rewriteStatefulFlatMapFrom {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    Mode → List Γ → List Δ
  | mode, [] => spec.finish mode
  | mode, symbol :: rest =>
      let result := spec.action mode symbol
      result.1 ++ rewriteStatefulFlatMapFrom spec result.2 rest

/-- Pure semantics from the specified initial mode. -/
def rewriteStatefulFlatMap {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) (input : List Γ) : List Δ :=
  rewriteStatefulFlatMapFrom spec spec.initial input

/-- A finite cursor in one action chunk. -/
def StatefulFlatMapActionCursor {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) :=
  Σ mode : Mode, Σ symbol : Γ, Fin (spec.action mode symbol).1.length

/-- A finite cursor in one terminal flush chunk. -/
def StatefulFlatMapFinishCursor {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) :=
  Σ mode : Mode, Fin (spec.finish mode).length

instance {Mode Γ Δ : Type} [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    Fintype (StatefulFlatMapActionCursor spec) := by
  unfold StatefulFlatMapActionCursor
  infer_instance

instance {Mode Γ Δ : Type} [Fintype Mode]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    Fintype (StatefulFlatMapFinishCursor spec) := by
  unfold StatefulFlatMapFinishCursor
  infer_instance

/-- Fixed controller labels. -/
inductive StatefulFlatMapLabel {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ)
  | scan (mode : Mode)
  | action (cursor : StatefulFlatMapActionCursor spec)
  | finish (cursor : StatefulFlatMapFinishCursor spec)
  | halt

private def statefulFlatMapLabelEquiv {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    (Mode ⊕ (StatefulFlatMapActionCursor spec ⊕
      (StatefulFlatMapFinishCursor spec ⊕ Unit))) ≃
        StatefulFlatMapLabel spec where
  toFun
    | .inl mode => .scan mode
    | .inr (.inl cursor) => .action cursor
    | .inr (.inr (.inl cursor)) => .finish cursor
    | .inr (.inr (.inr _)) => .halt
  invFun
    | .scan mode => .inl mode
    | .action cursor => .inr (.inl cursor)
    | .finish cursor => .inr (.inr (.inl cursor))
    | .halt => .inr (.inr (.inr ()))
  left_inv encoded := by rcases encoded with (_ | (_ | (_ | _))) <;> rfl
  right_inv label := by cases label <;> rfl

instance {Mode Γ Δ : Type} [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    Fintype (StatefulFlatMapLabel spec) :=
  Fintype.ofEquiv _ (statefulFlatMapLabelEquiv spec)

noncomputable instance {Mode Γ Δ : Type} [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    DecidableEq (StatefulFlatMapLabel spec) := Classical.decEq _

private def statefulFlatMapStartAction {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) (mode : Mode) (symbol : Γ) :
    StatefulFlatMapLabel spec :=
  if hempty : (spec.action mode symbol).1.length = 0 then
    .scan (spec.action mode symbol).2
  else
    .action ⟨mode, symbol, ⟨0, Nat.pos_of_ne_zero hempty⟩⟩

private def statefulFlatMapNextAction {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (cursor : StatefulFlatMapActionCursor spec) :
    StatefulFlatMapLabel spec :=
  if hlast : cursor.2.2.val + 1 =
      (spec.action cursor.1 cursor.2.1).1.length then
    .scan (spec.action cursor.1 cursor.2.1).2
  else
    .action ⟨cursor.1, cursor.2.1,
      ⟨cursor.2.2.val + 1, by omega⟩⟩

private def statefulFlatMapStartFinish {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) (mode : Mode) :
    StatefulFlatMapLabel spec :=
  if hempty : (spec.finish mode).length = 0 then .halt
  else .finish ⟨mode, ⟨0, Nat.pos_of_ne_zero hempty⟩⟩

private def statefulFlatMapNextFinish {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (cursor : StatefulFlatMapFinishCursor spec) :
    StatefulFlatMapLabel spec :=
  if hlast : cursor.2.val + 1 = (spec.finish cursor.1).length then .halt
  else .finish ⟨cursor.1, ⟨cursor.2.val + 1, by omega⟩⟩

/-- Reverse-output controller for a fixed finite-state flat map. -/
def statefulFlatMapRevProgram {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) : Program Γ Δ where
  Label := StatefulFlatMapLabel spec
  main := .scan spec.initial
  op
    | .scan mode => .popInput (statefulFlatMapStartFinish spec mode)
        (statefulFlatMapStartAction spec mode)
    | .action cursor =>
        .pushOutput
          ((spec.action cursor.1 cursor.2.1).1.get cursor.2.2)
          (statefulFlatMapNextAction spec cursor)
    | .finish cursor =>
        .pushOutput ((spec.finish cursor.1).get cursor.2)
          (statefulFlatMapNextFinish spec cursor)
    | .halt => .halt

private def statefulFlatMapCfg {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (label : StatefulFlatMapLabel spec) (buffer : Option Γ)
    (input : List Γ) (output : List Δ) :
    BuilderCfg (statefulFlatMapRevProgram spec) :=
  { initialCfg (statefulFlatMapRevProgram spec) input with
      label := some label
      buffer₁ := buffer
      output := output }

private def statefulFlatMapScanCfg {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) (mode : Mode)
    (buffer : Option Γ) (input : List Γ) (output : List Δ) :
    BuilderCfg (statefulFlatMapRevProgram spec) :=
  statefulFlatMapCfg spec (.scan mode) buffer input output

private def statefulFlatMapActionCfg {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (cursor : StatefulFlatMapActionCursor spec) (buffer : Option Γ)
    (input : List Γ) (output : List Δ) :
    BuilderCfg (statefulFlatMapRevProgram spec) :=
  statefulFlatMapCfg spec (.action cursor) buffer input output

private def statefulFlatMapFinishCfg {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (cursor : StatefulFlatMapFinishCursor spec) (buffer : Option Γ)
    (output : List Δ) : BuilderCfg (statefulFlatMapRevProgram spec) :=
  statefulFlatMapCfg spec (.finish cursor) buffer [] output

private theorem statefulFlatMap_actionCursor_eval {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (mode : Mode) (symbol : Γ) (buffer : Option Γ)
    (input : List Γ) (output : List Δ) (i : Nat)
    (hi : i < (spec.action mode symbol).1.length) :
    (flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
        (spec.action mode symbol).1.length - i]
      (some (statefulFlatMapActionCfg spec
        ⟨mode, symbol, ⟨i, hi⟩⟩ buffer input output)) =
      some (statefulFlatMapScanCfg spec
        (spec.action mode symbol).2 buffer input
        (((spec.action mode symbol).1.drop i).reverse ++ output)) := by
  classical
  let chunk := (spec.action mode symbol).1
  by_cases hlast : i + 1 = chunk.length
  · have hsteps : chunk.length - i = 1 := by omega
    rw [show (spec.action mode symbol).1.length - i = 1 by
      simpa [chunk] using hsteps, Function.iterate_succ_apply]
    simp only [Function.iterate_zero_apply, flip, Option.bind_some]
    have hstep :
        step (statefulFlatMapRevProgram spec)
            (statefulFlatMapActionCfg spec
              ⟨mode, symbol, ⟨i, hi⟩⟩ buffer input output) =
          some (statefulFlatMapScanCfg spec
            (spec.action mode symbol).2 buffer input
            ((spec.action mode symbol).1[i] :: output)) := by
      simp [step, statefulFlatMapRevProgram, statefulFlatMapActionCfg,
        statefulFlatMapScanCfg, statefulFlatMapCfg,
        statefulFlatMapNextAction, hlast, chunk]
      rfl
    rw [hstep]
    congr 2
    rw [List.drop_eq_getElem_cons hi,
      List.drop_eq_nil_of_le (show chunk.length ≤ i + 1 by omega)]
    simp
  · have hiChunk : i < chunk.length := by simpa [chunk] using hi
    have hnext : i + 1 < chunk.length := by omega
    have hsteps : chunk.length - i = (chunk.length - (i + 1)) + 1 := by
      omega
    rw [show (spec.action mode symbol).1.length - i =
        ((spec.action mode symbol).1.length - (i + 1)) + 1 by
      simpa [chunk] using hsteps,
      Function.iterate_succ_apply]
    simp only [flip, Option.bind_some]
    have hi' : i + 1 < (spec.action mode symbol).1.length := by
      simpa [chunk] using hnext
    have hstep :
        step (statefulFlatMapRevProgram spec)
            (statefulFlatMapActionCfg spec
              ⟨mode, symbol, ⟨i, hi⟩⟩ buffer input output) =
          some (statefulFlatMapActionCfg spec
            ⟨mode, symbol, ⟨i + 1, hi'⟩⟩ buffer input
            ((spec.action mode symbol).1[i] :: output)) := by
      simp [step, statefulFlatMapRevProgram, statefulFlatMapActionCfg,
        statefulFlatMapCfg, statefulFlatMapNextAction, hlast, chunk]
      rfl
    rw [hstep, statefulFlatMap_actionCursor_eval spec mode symbol buffer
      input ((spec.action mode symbol).1[i] :: output) (i + 1) hi']
    congr 2
    conv_rhs => rw [List.drop_eq_getElem_cons hi]
    rw [List.reverse_cons]
    simp [List.append_assoc]
termination_by (spec.action mode symbol).1.length - i
decreasing_by omega

private theorem statefulFlatMap_finishCursor_eval {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (mode : Mode) (buffer : Option Γ) (output : List Δ) (i : Nat)
    (hi : i < (spec.finish mode).length) :
    (flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
        (spec.finish mode).length - i]
      (some (statefulFlatMapFinishCfg spec
        ⟨mode, ⟨i, hi⟩⟩ buffer output)) =
      some (statefulFlatMapCfg spec .halt buffer []
        (((spec.finish mode).drop i).reverse ++ output)) := by
  classical
  let chunk := spec.finish mode
  by_cases hlast : i + 1 = chunk.length
  · have hsteps : chunk.length - i = 1 := by omega
    rw [show (spec.finish mode).length - i = 1 by
      simpa [chunk] using hsteps, Function.iterate_succ_apply]
    simp only [Function.iterate_zero_apply, flip, Option.bind_some]
    have hstep :
        step (statefulFlatMapRevProgram spec)
            (statefulFlatMapFinishCfg spec
              ⟨mode, ⟨i, hi⟩⟩ buffer output) =
          some (statefulFlatMapCfg spec .halt buffer []
            ((spec.finish mode)[i] :: output)) := by
      simp [step, statefulFlatMapRevProgram, statefulFlatMapFinishCfg,
        statefulFlatMapCfg, statefulFlatMapNextFinish, hlast, chunk]
      rfl
    rw [hstep]
    congr 2
    rw [List.drop_eq_getElem_cons hi,
      List.drop_eq_nil_of_le (show chunk.length ≤ i + 1 by omega)]
    simp
  · have hiChunk : i < chunk.length := by simpa [chunk] using hi
    have hnext : i + 1 < chunk.length := by omega
    have hsteps : chunk.length - i = (chunk.length - (i + 1)) + 1 := by
      omega
    rw [show (spec.finish mode).length - i =
        ((spec.finish mode).length - (i + 1)) + 1 by
      simpa [chunk] using hsteps,
      Function.iterate_succ_apply]
    simp only [flip, Option.bind_some]
    have hi' : i + 1 < (spec.finish mode).length := by
      simpa [chunk] using hnext
    have hstep :
        step (statefulFlatMapRevProgram spec)
            (statefulFlatMapFinishCfg spec
              ⟨mode, ⟨i, hi⟩⟩ buffer output) =
          some (statefulFlatMapFinishCfg spec
            ⟨mode, ⟨i + 1, hi'⟩⟩ buffer
            ((spec.finish mode)[i] :: output)) := by
      simp [step, statefulFlatMapRevProgram, statefulFlatMapFinishCfg,
        statefulFlatMapCfg, statefulFlatMapNextFinish, hlast, chunk]
      rfl
    rw [hstep, statefulFlatMap_finishCursor_eval spec mode buffer
      ((spec.finish mode)[i] :: output) (i + 1) hi']
    congr 2
    conv_rhs => rw [List.drop_eq_getElem_cons hi]
    rw [List.reverse_cons]
    simp [List.append_assoc]
termination_by (spec.finish mode).length - i
decreasing_by omega

private theorem statefulFlatMap_actionPhase_eval {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (mode : Mode) (symbol : Γ) (buffer : Option Γ)
    (input : List Γ) (output : List Δ) :
    (flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
        (spec.action mode symbol).1.length]
      (some (statefulFlatMapCfg spec
        (statefulFlatMapStartAction spec mode symbol) buffer input output)) =
      some (statefulFlatMapScanCfg spec
        (spec.action mode symbol).2 buffer input
        ((spec.action mode symbol).1.reverse ++ output)) := by
  classical
  by_cases hempty : (spec.action mode symbol).1.length = 0
  · have hchunk : (spec.action mode symbol).1 = [] :=
      List.length_eq_zero_iff.mp hempty
    simp [hchunk, statefulFlatMapStartAction,
      statefulFlatMapCfg, statefulFlatMapScanCfg]
  · let first : StatefulFlatMapActionCursor spec :=
      ⟨mode, symbol, ⟨0, Nat.pos_of_ne_zero hempty⟩⟩
    have hstart : statefulFlatMapStartAction spec mode symbol = .action first := by
      simp [statefulFlatMapStartAction, hempty, first]
    rw [hstart]
    simpa [first, statefulFlatMapActionCfg] using
      statefulFlatMap_actionCursor_eval spec mode symbol buffer input output
        0 (Nat.pos_of_ne_zero hempty)

private theorem statefulFlatMap_finishPhase_eval {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (mode : Mode) (buffer : Option Γ) (output : List Δ) :
    (flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
        (spec.finish mode).length]
      (some (statefulFlatMapCfg spec
        (statefulFlatMapStartFinish spec mode) buffer [] output)) =
      some (statefulFlatMapCfg spec .halt buffer []
        ((spec.finish mode).reverse ++ output)) := by
  classical
  by_cases hempty : (spec.finish mode).length = 0
  · have hchunk : spec.finish mode = [] := List.length_eq_zero_iff.mp hempty
    simp [hchunk, statefulFlatMapStartFinish, statefulFlatMapCfg]
  · let first : StatefulFlatMapFinishCursor spec :=
      ⟨mode, ⟨0, Nat.pos_of_ne_zero hempty⟩⟩
    have hstart : statefulFlatMapStartFinish spec mode = .finish first := by
      simp [statefulFlatMapStartFinish, hempty, first]
    rw [hstart]
    simpa [first, statefulFlatMapFinishCfg] using
      statefulFlatMap_finishCursor_eval spec mode buffer output 0
        (Nat.pos_of_ne_zero hempty)

private theorem statefulFlatMap_scanPhase_eval {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ)
    (mode : Mode) (buffer : Option Γ) (input : List Γ)
    (output : List Δ) :
    (flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
        input.length + (rewriteStatefulFlatMapFrom spec mode input).length + 1]
      (some (statefulFlatMapScanCfg spec mode buffer input output)) =
      some (statefulFlatMapCfg spec .halt none []
        ((rewriteStatefulFlatMapFrom spec mode input).reverse ++ output)) := by
  induction input generalizing mode buffer output with
  | nil =>
      rw [show [].length +
          (rewriteStatefulFlatMapFrom spec mode []).length + 1 =
          (spec.finish mode).length + 1 by
            simp [rewriteStatefulFlatMapFrom],
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
            (spec.finish mode).length]
          (some (statefulFlatMapCfg spec
            (statefulFlatMapStartFinish spec mode) none [] output)) = _
      simpa [rewriteStatefulFlatMapFrom] using
        statefulFlatMap_finishPhase_eval spec mode none output
  | cons symbol rest ih =>
      rcases haction : spec.action mode symbol with ⟨chunk, nextMode⟩
      have hsteps :
          (symbol :: rest).length +
              (rewriteStatefulFlatMapFrom spec mode (symbol :: rest)).length + 1 =
            (rest.length +
                (rewriteStatefulFlatMapFrom spec nextMode rest).length + 1) +
              (chunk.length + 1) := by
        simp [rewriteStatefulFlatMapFrom, haction]
        omega
      rw [hsteps, Function.iterate_add_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
            rest.length +
              (rewriteStatefulFlatMapFrom spec nextMode rest).length + 1]
          ((flip Option.bind (step (statefulFlatMapRevProgram spec)))^[
              chunk.length]
            (some (statefulFlatMapCfg spec
              (statefulFlatMapStartAction spec mode symbol)
              (some symbol) rest output))) = _
      have hchunk := statefulFlatMap_actionPhase_eval spec mode symbol
        (some symbol) rest output
      rw [show (spec.action mode symbol).1.length = chunk.length by
        rw [haction]] at hchunk
      rw [hchunk]
      have htailRaw := ih nextMode (some symbol) (chunk.reverse ++ output)
      rw [show (spec.action mode symbol).2 = nextMode by rw [haction],
        show (spec.action mode symbol).1 = chunk by rw [haction],
        htailRaw]
      congr 2
      simp [rewriteStatefulFlatMapFrom, haction, List.reverse_append,
        List.append_assoc]

/-- Exact transition count of the reverse-output controller. -/
def statefulFlatMapRevSteps {Mode Γ Δ : Type}
    (spec : StatefulFlatMapSpec Mode Γ Δ) (input : List Γ) : Nat :=
  input.length + (rewriteStatefulFlatMap spec input).length + 2

/-- Exact independent-semantics execution of the reverse-output controller. -/
def statefulFlatMapRev_run {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) (input : List Γ) :
    EvalsToInTime (step (statefulFlatMapRevProgram spec))
      (initialCfg (statefulFlatMapRevProgram spec) input)
      (some (haltCfg (statefulFlatMapRevProgram spec)
        (rewriteStatefulFlatMap spec input).reverse))
      (statefulFlatMapRevSteps spec input) := by
  have hscan := statefulFlatMap_scanPhase_eval spec spec.initial none input []
  have hscanRun : EvalsToInTime (step (statefulFlatMapRevProgram spec))
      (initialCfg (statefulFlatMapRevProgram spec) input)
      (some (statefulFlatMapCfg spec .halt none []
        (rewriteStatefulFlatMap spec input).reverse))
      (input.length + (rewriteStatefulFlatMap spec input).length + 1) := by
    refine ⟨⟨_, ?_⟩, le_rfl⟩
    have hinit :
        initialCfg (statefulFlatMapRevProgram spec) input =
          statefulFlatMapScanCfg spec spec.initial none input [] := by
      rfl
    rw [hinit]
    simpa [rewriteStatefulFlatMap] using hscan
  have hhalt : EvalsToInTime (step (statefulFlatMapRevProgram spec))
      (statefulFlatMapCfg spec .halt none []
        (rewriteStatefulFlatMap spec input).reverse)
      (some (haltCfg (statefulFlatMapRevProgram spec)
        (rewriteStatefulFlatMap spec input).reverse)) 1 :=
    ⟨⟨1, by rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step (statefulFlatMapRevProgram spec))
    (input.length + (rewriteStatefulFlatMap spec input).length + 1) 1
    _ _ _ hscanRun hhalt
  convert full using 1
  simp [statefulFlatMapRevSteps]
  omega

/-- Builder output contract for the reversed semantic stream. -/
theorem statefulFlatMapRev_builderOutputs {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    BuilderOutputs (statefulFlatMapRevProgram spec)
      (fun input => (rewriteStatefulFlatMap spec input).reverse)
      (statefulFlatMapRevSteps spec) := by
  intro input
  exact ⟨statefulFlatMapRev_run spec input⟩

/-- Compiled output contract for the reversed semantic stream. -/
theorem statefulFlatMapRev_outputs {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    Outputs (statefulFlatMapRevProgram spec)
      (fun input => (rewriteStatefulFlatMap spec input).reverse)
      (statefulFlatMapRevSteps spec) :=
  Outputs.of_builder_run (statefulFlatMapRev_builderOutputs spec)

private def statefulFlatMapActionTotal {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) : Nat :=
  ∑ mode : Mode, ∑ symbol : Γ, (spec.action mode symbol).1.length

private def statefulFlatMapFinishTotal {Mode Γ Δ : Type}
    [Fintype Mode] (spec : StatefulFlatMapSpec Mode Γ Δ) : Nat :=
  ∑ mode : Mode, (spec.finish mode).length

private theorem statefulFlatMap_action_length_le_total {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) (mode : Mode) (symbol : Γ) :
    (spec.action mode symbol).1.length ≤ statefulFlatMapActionTotal spec := by
  classical
  unfold statefulFlatMapActionTotal
  have hinner :
      (spec.action mode symbol).1.length ≤
        ∑ currentSymbol : Γ, (spec.action mode currentSymbol).1.length :=
    Finset.single_le_sum
      (f := fun currentSymbol : Γ =>
        (spec.action mode currentSymbol).1.length)
      (s := Finset.univ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ symbol)
  have houter :
      (∑ currentSymbol : Γ, (spec.action mode currentSymbol).1.length) ≤
        ∑ currentMode : Mode,
          ∑ currentSymbol : Γ,
            (spec.action currentMode currentSymbol).1.length :=
    Finset.single_le_sum
      (f := fun currentMode : Mode =>
        ∑ currentSymbol : Γ,
          (spec.action currentMode currentSymbol).1.length)
      (s := Finset.univ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ mode)
  exact hinner.trans houter

private theorem statefulFlatMap_finish_length_le_total {Mode Γ Δ : Type}
    [Fintype Mode] (spec : StatefulFlatMapSpec Mode Γ Δ) (mode : Mode) :
    (spec.finish mode).length ≤ statefulFlatMapFinishTotal spec := by
  classical
  unfold statefulFlatMapFinishTotal
  exact Finset.single_le_sum
    (f := fun currentMode => (spec.finish currentMode).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ mode)

private theorem rewriteStatefulFlatMapFrom_length_le {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) (mode : Mode) (input : List Γ) :
    (rewriteStatefulFlatMapFrom spec mode input).length ≤
      input.length * statefulFlatMapActionTotal spec +
        statefulFlatMapFinishTotal spec := by
  induction input generalizing mode with
  | nil =>
      simpa [rewriteStatefulFlatMapFrom] using
        statefulFlatMap_finish_length_le_total spec mode
  | cons symbol rest ih =>
      rcases haction : spec.action mode symbol with ⟨chunk, nextMode⟩
      simp only [rewriteStatefulFlatMapFrom, haction, List.length_append,
        List.length_cons]
      have hchunk := statefulFlatMap_action_length_le_total spec mode symbol
      have hchunk' : chunk.length ≤ statefulFlatMapActionTotal spec := by
        simpa [haction] using hchunk
      have htail := ih nextMode
      have hadd := Nat.add_le_add hchunk' htail
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hadd

/-- Linear polynomial envelope for the direct reversed transducer. -/
noncomputable def statefulFlatMapRev_polyBound {Mode Γ Δ : Type}
    [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    PolyBound (statefulFlatMapRevSteps spec) where
  polynomial :=
    Polynomial.C (statefulFlatMapActionTotal spec + 1) * Polynomial.X +
      Polynomial.C (statefulFlatMapFinishTotal spec + 2)
  bound input := by
    have hout := rewriteStatefulFlatMapFrom_length_le
      spec spec.initial input
    simp only [statefulFlatMapRevSteps, rewriteStatefulFlatMap]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    calc
      input.length +
            (rewriteStatefulFlatMapFrom spec spec.initial input).length + 2 ≤
          input.length +
            (input.length * statefulFlatMapActionTotal spec +
              statefulFlatMapFinishTotal spec) + 2 := by omega
      _ = (statefulFlatMapActionTotal spec + 1) * input.length +
            (statefulFlatMapFinishTotal spec + 2) := by ring

/-- The reverse-output finite-state flat map is polynomial-time computable. -/
noncomputable def statefulFlatMapRev_computableInPolyTime
    {Mode Γ Δ : Type} [Fintype Mode] [Fintype Γ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ => (rewriteStatefulFlatMap spec input).reverse) :=
  ComputableInPolyTime (statefulFlatMapRevProgram spec)
    (fun input => (rewriteStatefulFlatMap spec input).reverse)
    (statefulFlatMapRevSteps spec)
    (statefulFlatMapRev_outputs spec)
    (statefulFlatMapRev_polyBound spec)

/-- Composing with verified reversal returns the forward semantic stream. -/
noncomputable def statefulFlatMap_computableInPolyTime
    {Mode Γ Δ : Type} [Fintype Mode] [Fintype Γ] [Fintype Δ]
    (spec : StatefulFlatMapSpec Mode Γ Δ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteStatefulFlatMap spec) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (statefulFlatMapRev_computableInPolyTime spec)
      (reverse_computableInPolyTime (Γ := Δ))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
