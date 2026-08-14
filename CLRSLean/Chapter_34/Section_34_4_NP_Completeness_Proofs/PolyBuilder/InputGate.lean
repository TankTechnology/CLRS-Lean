import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Encoding
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Streaming general-circuit input gates

The initial Cook--Levin builder allocates one input gate at every tableau bit.
This module turns a unit clock of length `n` into the exact serialized gate
stream for input wires `0, ..., n - 1`.  The concrete builder emits the reverse
stream, which is natural for a prepend-only output stack, and the verified
reversal machine supplies the public forward encoding.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Canonical encoding of the input gate at one wire index. -/
def inputGateCode (index : Nat) : List CircuitSym :=
  .inputMark :: encNat index

/-- Forward serialization of input gates `0, ..., count - 1`. -/
def inputGateStream (count : Nat) : List CircuitSym :=
  (List.range count).flatMap inputGateCode

/-- The stream is exactly the flattened general-circuit gate encoding. -/
theorem inputGateStream_eq (count : Nat) :
    inputGateStream count =
      (List.range count).flatMap
        (fun index => encodeCircuitGate (.input index)) := by
  rfl

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

/-- Stream segment beginning at an arbitrary input index. -/
private def inputGateStreamFrom : Nat → Nat → List CircuitSym
  | _, 0 => []
  | start, count + 1 =>
      inputGateCode start ++ inputGateStreamFrom (start + 1) count

private theorem inputGateStreamFrom_zero (count : Nat) :
    inputGateStreamFrom 0 count = inputGateStream count := by
  have aux : ∀ start count,
      inputGateStreamFrom start count =
        (List.range' start count).flatMap inputGateCode := by
    intro start count
    induction count generalizing start with
    | zero => rfl
    | succ count ih =>
        change inputGateCode start ++ inputGateStreamFrom (start + 1) count = _
        rw [ih]
        rfl
  rw [inputGateStream, List.range_eq_range']
  exact aux 0 count

/-! ## Reversed input-gate streamer -/

/-- Finite control for the reversed input-gate serializer. -/
inductive InputGateLabel
  | next
  | pushInput
  | decIndex
  | saveIndex
  | pushArg
  | pushEnd
  | restore
  | restoreIndex
  | advance
  | clear
  | halt
deriving DecidableEq, Fintype

/-- Counter machine emitting `(inputGateStream input.length).reverse`. -/
def inputGateRevProgram : Program Unit CircuitSym where
  Label := InputGateLabel
  main := .next
  op
    | .next => .popInput .clear (fun _ => .pushInput)
    | .pushInput => .pushOutput .inputMark .decIndex
    | .decIndex => .dec₁ .pushEnd .saveIndex
    | .saveIndex => .inc₂ .pushArg
    | .pushArg => .pushOutput .argMark .decIndex
    | .pushEnd => .pushOutput .endMark .restore
    | .restore => .dec₂ .advance .restoreIndex
    | .restoreIndex => .inc₁ .restore
    | .advance => .inc₁ .next
    | .clear => .dec₁ .halt .clear
    | .halt => .halt

private def inputGateCfg (label : InputGateLabel)
    (buffer : Option Unit) (test : Bool) (input : List Unit)
    (output : List CircuitSym) (counter₁ counter₂ : List Unit) :
    BuilderCfg inputGateRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := counter₁
  counter₂ := counter₂
  counter₃ := []

/-- Consume and save the current index while prepending its argument marks. -/
private theorem inputGate_emitArgs_eval (index : Nat)
    (buffer : Option Unit) (test : Bool) (input : List Unit)
    (output : List CircuitSym) (saved : List Unit) :
    (flip Option.bind (step inputGateRevProgram))^[3 * index + 1]
      (some (inputGateCfg .decIndex buffer test input output
        (List.replicate index ()) saved)) =
      some (inputGateCfg .pushEnd buffer false input
        (List.replicate index .argMark ++ output) []
        (List.replicate index () ++ saved)) := by
  induction index generalizing test output saved with
  | zero => rfl
  | succ index ih =>
      rw [show 3 * (index + 1) + 1 = (3 * index + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step inputGateRevProgram))^[3 * index + 1]
          (some (inputGateCfg .decIndex buffer true input
            (.argMark :: output) (List.replicate index ()) (() :: saved))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (.argMark :: output) (() :: saved)

/-- Restore the saved index counter after one gate is serialized. -/
private theorem inputGate_restore_eval (index : Nat)
    (buffer : Option Unit) (test : Bool) (input : List Unit)
    (output : List CircuitSym) (restored : List Unit) :
    (flip Option.bind (step inputGateRevProgram))^[2 * index + 1]
      (some (inputGateCfg .restore buffer test input output restored
        (List.replicate index ()))) =
      some (inputGateCfg .advance buffer false input output
        (List.replicate index () ++ restored) []) := by
  induction index generalizing test restored with
  | zero => rfl
  | succ index ih =>
      rw [show 2 * (index + 1) + 1 = (2 * index + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step inputGateRevProgram))^[2 * index + 1]
          (some (inputGateCfg .restore buffer true input output
            (() :: restored) (List.replicate index ()))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (() :: restored)

/-- Process one unit token at the current input-gate index. -/
private def inputGate_onePhase (index : Nat) (buffer : Option Unit)
    (rest : List Unit) (output : List CircuitSym) :
    EvalsToInTime (step inputGateRevProgram)
      (inputGateCfg .next buffer false (() :: rest) output
        (List.replicate index ()) [])
      (some (inputGateCfg .next (some ()) false rest
        ((inputGateCode index).reverse ++ output)
        (List.replicate (index + 1) ()) []))
      (5 * index + 6) := by
  let afterPop := inputGateCfg .pushInput (some ()) false rest output
    (List.replicate index ()) []
  let afterInput := inputGateCfg .decIndex (some ()) false rest
    (.inputMark :: output) (List.replicate index ()) []
  let afterArgs := inputGateCfg .pushEnd (some ()) false rest
    (List.replicate index .argMark ++ .inputMark :: output) []
    (List.replicate index ())
  let afterEnd := inputGateCfg .restore (some ()) false rest
    (.endMark :: (List.replicate index .argMark ++ .inputMark :: output)) []
    (List.replicate index ())
  let afterRestore := inputGateCfg .advance (some ()) false rest
    (.endMark :: (List.replicate index .argMark ++ .inputMark :: output))
    (List.replicate index ()) []
  have hpop : EvalsToInTime (step inputGateRevProgram)
      (inputGateCfg .next buffer false (() :: rest) output
        (List.replicate index ()) []) (some afterPop) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hinput : EvalsToInTime (step inputGateRevProgram)
      afterPop (some afterInput) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hargs : EvalsToInTime (step inputGateRevProgram)
      afterInput (some afterArgs) (3 * index + 1) := by
    refine ⟨⟨3 * index + 1, ?_⟩, le_rfl⟩
    simpa [afterInput, afterArgs] using inputGate_emitArgs_eval index
      (some ()) false rest (.inputMark :: output) []
  have hend : EvalsToInTime (step inputGateRevProgram)
      afterArgs (some afterEnd) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step inputGateRevProgram)
      afterEnd (some afterRestore) (2 * index + 1) := by
    refine ⟨⟨2 * index + 1, ?_⟩, le_rfl⟩
    simpa [afterEnd, afterRestore] using inputGate_restore_eval index
      (some ()) false rest
      (.endMark :: (List.replicate index .argMark ++ .inputMark :: output)) []
  have hadvance : EvalsToInTime (step inputGateRevProgram)
      afterRestore
      (some (inputGateCfg .next (some ()) false rest
        ((inputGateCode index).reverse ++ output)
        (List.replicate (index + 1) ()) [])) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (inputGateCfg .next (some ()) false rest
      (.endMark :: (List.replicate index .argMark ++ .inputMark :: output))
      (() :: List.replicate index ()) []) = _
    simp [inputGateCode, encNat, List.reverse_append,
      List.replicate_succ, List.append_assoc]
  let h₁ := EvalsToInTime.trans (step inputGateRevProgram)
    1 1 _ afterPop _ hpop hinput
  let h₂ := EvalsToInTime.trans (step inputGateRevProgram)
    (1 + 1) (3 * index + 1) _ afterInput _ h₁ hargs
  let h₃ := EvalsToInTime.trans (step inputGateRevProgram)
    ((3 * index + 1) + (1 + 1)) 1 _ afterArgs _ h₂ hend
  let h₄ := EvalsToInTime.trans (step inputGateRevProgram)
    (1 + ((3 * index + 1) + (1 + 1))) (2 * index + 1)
    _ afterEnd _ h₃ hrestore
  let h₅ := EvalsToInTime.trans (step inputGateRevProgram)
    ((2 * index + 1) + (1 + ((3 * index + 1) + (1 + 1)))) 1
    _ afterRestore _ h₄ hadvance
  have hbound :
      1 + ((2 * index + 1) + (1 + ((3 * index + 1) + (1 + 1)))) =
        5 * index + 6 := by omega
  rw [← hbound]
  exact h₅

private def inputGatePhaseSteps : Nat → Nat → Nat
  | _, 0 => 0
  | start, count + 1 =>
      (5 * start + 6) + inputGatePhaseSteps (start + 1) count

private theorem inputGatePhaseSteps_le (start count : Nat) :
    inputGatePhaseSteps start count ≤
      5 * count * start + 6 * count ^ 2 := by
  induction count generalizing start with
  | zero => simp [inputGatePhaseSteps]
  | succ count ih =>
      simp only [inputGatePhaseSteps]
      have h := ih (start + 1)
      nlinarith

/-- Run all remaining input-gate phases from an arbitrary starting index. -/
private def inputGate_inputPhases (start : Nat) (buffer : Option Unit)
    (input : List Unit) (output : List CircuitSym) :
    Σ finalBuffer,
      EvalsToInTime (step inputGateRevProgram)
        (inputGateCfg .next buffer false input output
          (List.replicate start ()) [])
        (some (inputGateCfg .next finalBuffer false []
          ((inputGateStreamFrom start input.length).reverse ++ output)
          (List.replicate (start + input.length) ()) []))
        (inputGatePhaseSteps start input.length) := by
  induction input generalizing start buffer output with
  | nil => exact ⟨buffer, ⟨⟨0, rfl⟩, le_rfl⟩⟩
  | cons head rest ih =>
      cases head
      let first := inputGate_onePhase start buffer rest output
      rcases ih (start + 1) (some ())
          ((inputGateCode start).reverse ++ output) with
        ⟨finalBuffer, remaining⟩
      let full := EvalsToInTime.trans (step inputGateRevProgram)
        (5 * start + 6) (inputGatePhaseSteps (start + 1) rest.length)
        _
        (inputGateCfg .next (some ()) false rest
          ((inputGateCode start).reverse ++ output)
          (List.replicate (start + 1) ()) [])
        _ first remaining
      have hstart : start + 1 + rest.length =
          start + (Unit.unit :: rest).length := by simp; omega
      have hout :
          (inputGateStreamFrom (start + 1) rest.length).reverse ++
              ((inputGateCode start).reverse ++ output) =
            (inputGateStreamFrom start (Unit.unit :: rest).length).reverse ++
              output := by
        simp [inputGateStreamFrom, List.reverse_append, List.append_assoc]
      have hbound :
          inputGatePhaseSteps (start + 1) rest.length +
              (5 * start + 6) =
            inputGatePhaseSteps start (Unit.unit :: rest).length := by
        simp [inputGatePhaseSteps, Nat.add_comm]
      rw [hstart, hout] at full
      refine ⟨finalBuffer, ?_⟩
      rw [← hbound]
      exact full

/-- Exact total step count of the reversed input-gate streamer. -/
def inputGateRevSteps (input : List Unit) : Nat :=
  inputGatePhaseSteps 0 input.length + input.length + 3

/-- Clear the final index counter and halt. -/
private def inputGate_finish (count : Nat) (buffer : Option Unit)
    (output : List CircuitSym) :
    EvalsToInTime (step inputGateRevProgram)
      (inputGateCfg .next buffer false [] output
        (List.replicate count ()) [])
      (some (haltCfg inputGateRevProgram output))
      (count + 3) := by
  have hclearEval (test : Bool) :
      (flip Option.bind (step inputGateRevProgram))^[count + 1]
        (some (inputGateCfg .clear none test [] output
          (List.replicate count ()) [])) =
        some (inputGateCfg .halt none false [] output [] []) := by
    induction count generalizing test with
    | zero => rfl
    | succ count ih =>
        rw [show count + 1 + 1 = (count + 1) + 1 by omega,
          Function.iterate_succ_apply]
        change
          (flip Option.bind (step inputGateRevProgram))^[count + 1]
            (some (inputGateCfg .clear none true [] output
              (List.replicate count ()) [])) = _
        simpa using ih true
  have hnext : EvalsToInTime (step inputGateRevProgram)
      (inputGateCfg .next buffer false [] output
        (List.replicate count ()) [])
      (some (inputGateCfg .clear none false [] output
        (List.replicate count ()) [])) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step inputGateRevProgram)
      (inputGateCfg .clear none false [] output
        (List.replicate count ()) [])
      (some (inputGateCfg .halt none false [] output [] []))
      (count + 1) :=
    ⟨⟨count + 1, hclearEval false⟩, le_rfl⟩
  have hhalt : EvalsToInTime (step inputGateRevProgram)
      (inputGateCfg .halt none false [] output [] [])
      (some (haltCfg inputGateRevProgram output)) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step inputGateRevProgram)
    1 (count + 1) _ _ _ hnext hclear
  let full := EvalsToInTime.trans (step inputGateRevProgram)
    ((count + 1) + 1) 1 _ _ _ h₁ hhalt
  have hbound : 1 + ((count + 1) + 1) = count + 3 := by omega
  rw [← hbound]
  exact full

/-- Complete exact builder run for the reversed input-gate stream. -/
def inputGateRev_run (input : List Unit) :
    EvalsToInTime (step inputGateRevProgram)
      (initialCfg inputGateRevProgram input)
      (some (haltCfg inputGateRevProgram
        (inputGateStream input.length).reverse))
      (inputGateRevSteps input) := by
  rcases inputGate_inputPhases 0 none input [] with
    ⟨finalBuffer, phases⟩
  let finish := inputGate_finish input.length finalBuffer
    (inputGateStream input.length).reverse
  have hstream := inputGateStreamFrom_zero input.length
  let full := EvalsToInTime.trans (step inputGateRevProgram)
    (inputGatePhaseSteps 0 input.length) (input.length + 3)
    (initialCfg inputGateRevProgram input)
    (inputGateCfg .next finalBuffer false []
      (inputGateStream input.length).reverse
      (List.replicate input.length ()) [])
    _ (by
      simpa [initialCfg, inputGateCfg, inputGateRevProgram, hstream] using
        phases) finish
  have hbound : input.length + 3 + inputGatePhaseSteps 0 input.length =
      inputGateRevSteps input := by
    simp only [inputGateRevSteps]
    omega
  rw [← hbound]
  exact full

/-- Exact reversed-stream builder output contract. -/
theorem inputGateRev_builderOutputs :
    BuilderOutputs inputGateRevProgram
      (fun input => (inputGateStream input.length).reverse)
      inputGateRevSteps := by
  intro input
  exact ⟨inputGateRev_run input⟩

/-- Exact reversed-stream compiled TM2 output contract. -/
theorem inputGateRev_outputs :
    Outputs inputGateRevProgram
      (fun input => (inputGateStream input.length).reverse)
      inputGateRevSteps :=
  Outputs.of_builder_run inputGateRev_builderOutputs

/-- Quadratic runtime envelope for input-gate serialization. -/
noncomputable def inputGateRev_polyBound :
    PolyBound inputGateRevSteps where
  polynomial := 6 * Polynomial.X ^ 2 + Polynomial.X + 3
  bound input := by
    have hphase := inputGatePhaseSteps_le 0 input.length
    simp only [inputGateRevSteps, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

/-- Concrete polynomial-time machine producing the reversed stream. -/
noncomputable def inputGateRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit => (inputGateStream input.length).reverse) :=
  ComputableInPolyTime inputGateRevProgram _ inputGateRevSteps
    inputGateRev_outputs inputGateRev_polyBound

/-- Concrete polynomial-time machine producing the forward serialized input
gate family. -/
noncomputable def inputGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit => inputGateStream input.length) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      inputGateRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
