import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DelimitedBinarySum.Basic
import Mathlib.Tactic

/-! # Delimited binary sum: exact controller run -/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum

def finishSteps : List Bool → Bool → Nat
  | [], false => 1
  | [], true => 2
  | accumulatorBit :: accumulator, carry =>
      2 + finishSteps accumulator
        (BinaryNat.Adder.addCell false accumulatorBit carry).2

def sumSteps : List (Option Bool) → List Bool → Bool →
    List Bool → Nat
  | [], accumulator, carry, work =>
      let next := finishAdd accumulator carry work
      1 + finishSteps accumulator carry + (next.length + 1) +
        (2 * next.length + 2)
  | none :: rest, accumulator, carry, work =>
      let next := finishAdd accumulator carry work
      1 + finishSteps accumulator carry + (next.length + 1) +
        sumSteps rest next.reverse false []
  | some fieldBit :: rest, [], carry, work =>
      let cell := BinaryNat.Adder.addCell fieldBit false carry
      3 + sumSteps rest [] cell.2 (cell.1 :: work)
  | some fieldBit :: rest, accumulatorBit :: accumulator, carry, work =>
      let cell := BinaryNat.Adder.addCell fieldBit accumulatorBit carry
      3 + sumSteps rest accumulator cell.2 (cell.1 :: work)

private def load_run (input work₂ : List (Option Bool))
    (buffer₁ buffer₂ : Option (Option Bool)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .load buffer₁ buffer₂ test input [] [] work₂)
      (some (cfg (.add false) none buffer₂ test [] [] []
        (input.reverse ++ work₂)))
      (2 * input.length + 1) := by
  induction input generalizing buffer₁ work₂ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons field input ih =>
      let afterPop := cfg (.store field) (some field) buffer₂ test input [] []
        work₂
      let afterStore := cfg .load (some field) buffer₂ test input [] []
        (field :: work₂)
      have first : EvalsToInTime (step program)
          (cfg .load buffer₁ buffer₂ test (field :: input) [] [] work₂)
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterStore) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterStore, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some field) (work₂ := field :: work₂)
      let firstTwo := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * input.length + 1) _ afterStore _ firstTwo rest
      simpa [List.reverse_cons, Nat.mul_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def finish_run (accumulator work : List Bool) (carry final : Bool)
    (work₂ : List (Option Bool))
    (buffer₁ buffer₂ : Option (Option Bool)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.finish carry final) buffer₁ buffer₂ test
        (accumulator.map some) [] (work.map some) work₂)
      (some (cfg (.restore final) none buffer₂ test [] []
        ((finishAdd accumulator carry work).map some) work₂))
      (finishSteps accumulator carry) := by
  induction accumulator generalizing carry work buffer₁ with
  | nil =>
      cases carry with
      | false =>
          exact ⟨⟨1, by simp [finishAdd, flip, step, program,
            cfg, stepOp]⟩, le_rfl⟩
      | true =>
          exact ⟨⟨2, by simp [finishAdd,
            Function.iterate_succ_apply, flip, step, program, cfg, stepOp]⟩,
            le_rfl⟩
  | cons accumulatorBit accumulator ih =>
      let cell := BinaryNat.Adder.addCell false accumulatorBit carry
      let afterPop := cfg (.saveFinish final cell.2 cell.1)
        (some (some accumulatorBit)) buffer₂ test (accumulator.map some) []
        (work.map some) work₂
      let afterSave := cfg (.finish cell.2 final)
        (some (some accumulatorBit)) buffer₂ test (accumulator.map some) []
        (some cell.1 :: work.map some) work₂
      have first : EvalsToInTime (step program)
          (cfg (.finish carry final) buffer₁ buffer₂ test
            ((accumulatorBit :: accumulator).map some) []
            (work.map some) work₂)
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, cell, afterPop, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterSave) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterSave, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (carry := cell.2) (work := cell.1 :: work)
        (buffer₁ := some (some accumulatorBit))
      let firstTwo := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (finishSteps accumulator cell.2) _ afterSave _ firstTwo rest
      simpa [finishSteps, finishAdd, cell, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

private def restore_run (work : List Bool) (input : List (Option Bool))
    (final : Bool) (work₂ : List (Option Bool))
    (buffer₁ buffer₂ : Option (Option Bool)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.restore final) buffer₁ buffer₂ test input []
        (work.map some) work₂)
      (some (cfg (if final then .emit else .add false) none buffer₂ test
        (work.reverse.map some ++ input) [] [] work₂))
      (work.length + 1) := by
  induction work generalizing input buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons bit work ih =>
      let after := cfg (.restore final) (some (some bit)) buffer₂ test
        (some bit :: input) [] (work.map some) work₂
      have first : EvalsToInTime (step program)
          (cfg (.restore final) buffer₁ buffer₂ test input []
            ((bit :: work).map some) work₂)
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (input := some bit :: input)
        (buffer₁ := some (some bit))
      let full := EvalsToInTime.trans (step program)
        1 (work.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

private def emit_run (word output : List Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .emit buffer₁ buffer₂ test (word.map some) output [] [])
      (some (haltCfg program (word.reverse ++ output)))
      (2 * word.length + 2) := by
  induction word generalizing output buffer₁ with
  | nil =>
      exact ⟨⟨2, by simp [Function.iterate_succ_apply, flip, step,
        program, cfg, stepOp, haltCfg]⟩,
        le_rfl⟩
  | cons bit word ih =>
      let afterPop := cfg (.emitBit bit) (some (some bit)) buffer₂ test
        (word.map some) output [] []
      let afterEmit := cfg .emit (some (some bit)) buffer₂ test
        (word.map some) (bit :: output) [] []
      have first : EvalsToInTime (step program)
          (cfg .emit buffer₁ buffer₂ test ((bit :: word).map some)
            output [] [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterEmit) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterEmit, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (output := bit :: output)
        (buffer₁ := some (some bit))
      let firstTwo := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * word.length + 2) _ afterEmit _ firstTwo rest
      simpa [List.reverse_cons, Nat.mul_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def core_run (symbols : List (Option Bool))
    (accumulator work : List Bool) (carry : Bool)
    (buffer₁ buffer₂ : Option (Option Bool)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.add carry) buffer₁ buffer₂ test (accumulator.map some) []
        (work.map some) symbols)
      (some (haltCfg program (sumReversed symbols accumulator carry work)))
      (sumSteps symbols accumulator carry work) := by
  induction symbols generalizing accumulator carry work buffer₁ buffer₂ with
  | nil =>
      let next := finishAdd accumulator carry work
      let afterPop := cfg (.finish carry true) buffer₁ none test
        (accumulator.map some) [] (work.map some) []
      have first : EvalsToInTime (step program)
          (cfg (.add carry) buffer₁ buffer₂ test (accumulator.map some) []
            (work.map some) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have finished := finish_run accumulator work carry true [] buffer₁ none test
      have restored := restore_run next [] true [] none none test
      have restored' : EvalsToInTime (step program)
          (cfg (.restore true) none none test [] [] (next.map some) [])
          (some (cfg .emit none none test (next.reverse.map some) [] [] []))
          (next.length + 1) := by
        simpa using restored
      have emitted := emit_run next.reverse [] none none test
      have emitted' : EvalsToInTime (step program)
          (cfg .emit none none test (next.reverse.map some) [] [] [])
          (some (haltCfg program next))
          (2 * next.length + 2) := by
        simpa using emitted
      let throughFinish := EvalsToInTime.trans (step program)
        1 (finishSteps accumulator carry) _ afterPop _ first finished
      let throughRestore := EvalsToInTime.trans (step program)
        _ (next.length + 1) _ _ _ throughFinish restored'
      let full := EvalsToInTime.trans (step program)
        _ (2 * next.length + 2) _ _ _ throughRestore emitted'
      simpa [sumSteps, sumReversed, next, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | cons field symbols ih =>
      cases field with
      | none =>
          let next := finishAdd accumulator carry work
          let afterPop := cfg (.finish carry false) buffer₁
            (some none) test (accumulator.map some) [] (work.map some) symbols
          have first : EvalsToInTime (step program)
              (cfg (.add carry) buffer₁ buffer₂ test
                (accumulator.map some) [] (work.map some) (none :: symbols))
              (some afterPop) 1 :=
            ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩,
              le_rfl⟩
          have finished := finish_run accumulator work carry false symbols
            buffer₁ (some none) test
          have restored := restore_run next [] false symbols none (some none) test
          have restored' : EvalsToInTime (step program)
              (cfg (.restore false) none (some none) test [] []
                (next.map some) symbols)
              (some (cfg (.add false) none (some none) test
                (next.reverse.map some) [] [] symbols))
              (next.length + 1) := by
            simpa using restored
          have rest := ih (accumulator := next.reverse) (work := [])
            (carry := false) (buffer₁ := none) (buffer₂ := some none)
          let throughFinish := EvalsToInTime.trans (step program)
            1 (finishSteps accumulator carry) _ afterPop _ first finished
          let throughRestore := EvalsToInTime.trans (step program)
            _ (next.length + 1) _ _ _ throughFinish restored'
          let full := EvalsToInTime.trans (step program)
            _ (sumSteps symbols next.reverse false []) _ _ _ throughRestore rest
          simpa [sumSteps, sumReversed, next, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | some fieldBit =>
          let afterField := cfg (.readAccumulator carry fieldBit) buffer₁
            (some (some fieldBit)) test (accumulator.map some) []
            (work.map some) symbols
          have first : EvalsToInTime (step program)
              (cfg (.add carry) buffer₁ buffer₂ test
                (accumulator.map some) [] (work.map some)
                (some fieldBit :: symbols))
              (some afterField) 1 :=
            ⟨⟨1, by simp [flip, afterField, step, program, cfg, stepOp]⟩,
              le_rfl⟩
          cases accumulator with
          | nil =>
              let cell := BinaryNat.Adder.addCell fieldBit false carry
              let afterRead := cfg (.save cell.2 cell.1) none
                (some (some fieldBit)) test [] [] (work.map some) symbols
              let afterSave := cfg (.add cell.2) none
                (some (some fieldBit)) test [] []
                (some cell.1 :: work.map some) symbols
              have second : EvalsToInTime (step program) afterField
                  (some afterRead) 1 :=
                ⟨⟨1, by simp [flip, cell, afterField, afterRead, step,
                  program, cfg, stepOp]⟩, le_rfl⟩
              have third : EvalsToInTime (step program) afterRead
                  (some afterSave) 1 :=
                ⟨⟨1, by simp [flip, afterRead, afterSave, step, program,
                  cfg, stepOp]⟩, le_rfl⟩
              have rest := ih (accumulator := []) (work := cell.1 :: work)
                (carry := cell.2) (buffer₁ := none)
                (buffer₂ := some (some fieldBit))
              let firstTwo := EvalsToInTime.trans (step program)
                1 1 _ afterField _ first second
              let firstThree := EvalsToInTime.trans (step program)
                2 1 _ afterRead _ firstTwo third
              let full := EvalsToInTime.trans (step program)
                3 (sumSteps symbols [] cell.2 (cell.1 :: work)) _ afterSave _
                  firstThree rest
              simpa [sumSteps, sumReversed, cell, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full
          | cons accumulatorBit accumulator =>
              let cell := BinaryNat.Adder.addCell fieldBit accumulatorBit carry
              let afterRead := cfg (.save cell.2 cell.1)
                (some (some accumulatorBit)) (some (some fieldBit)) test
                (accumulator.map some) [] (work.map some) symbols
              let afterSave := cfg (.add cell.2)
                (some (some accumulatorBit)) (some (some fieldBit)) test
                (accumulator.map some) []
                (some cell.1 :: work.map some) symbols
              have second : EvalsToInTime (step program) afterField
                  (some afterRead) 1 :=
                ⟨⟨1, by simp [flip, cell, afterField, afterRead, step,
                  program, cfg, stepOp]⟩, le_rfl⟩
              have third : EvalsToInTime (step program) afterRead
                  (some afterSave) 1 :=
                ⟨⟨1, by simp [flip, afterRead, afterSave, step, program,
                  cfg, stepOp]⟩, le_rfl⟩
              have rest := ih (accumulator := accumulator)
                (work := cell.1 :: work) (carry := cell.2)
                (buffer₁ := some (some accumulatorBit))
                (buffer₂ := some (some fieldBit))
              let firstTwo := EvalsToInTime.trans (step program)
                1 1 _ afterField _ first second
              let firstThree := EvalsToInTime.trans (step program)
                2 1 _ afterRead _ firstTwo third
              let full := EvalsToInTime.trans (step program)
                3 (sumSteps symbols accumulator cell.2 (cell.1 :: work)) _
                  afterSave _ firstThree rest
              simpa [sumSteps, sumReversed, cell, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using full

def steps (input : List (Option Bool)) : Nat :=
  2 * input.length + 1 + sumSteps input.reverse [] false []

/-- Exact end-to-end run of the fixed delimited binary summation controller. -/
def run (input : List (Option Bool)) :
    EvalsToInTime (step program)
      (initialCfg program input)
      (some (haltCfg program (sumDelimited input)))
      (steps input) := by
  have loaded := load_run input [] none none false
  have loaded' : EvalsToInTime (step program)
      (initialCfg program input)
      (some (cfg (.add false) none none false [] [] [] input.reverse))
      (2 * input.length + 1) := by
    simpa [initialCfg, program, cfg] using loaded
  have summed := core_run input.reverse [] [] false none none false
  let full := EvalsToInTime.trans (step program)
    (2 * input.length + 1) (sumSteps input.reverse [] false []) _ _ _
      loaded' summed
  simpa [steps, sumDelimited, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum
