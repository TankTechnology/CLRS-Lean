import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePrefixSumCore
import Mathlib.Tactic

/-!
# Unary-frame prefix sums: exact simulation

The lemmas below verify loading, destructive unary emission, restoration,
increment consumption, the complete family loop, and final scratch cleanup.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem prefixSum_loadBase_eval (base : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) (current saved : List Unit) :
    (flip Option.bind (step unaryFramePrefixSumRevProgram))^[2 * base + 1]
      (some (unaryFramePrefixSumCfg .loadBase buffer₁ buffer₂ test
        (encodeUnaryFrameBlock base ++ tail) output current saved)) =
      some (unaryFramePrefixSumCfg .check (some .separator) buffer₂ test
        tail output (List.replicate base () ++ current) saved) := by
  induction base generalizing buffer₁ current with
  | zero => rfl
  | succ base ih =>
      rw [show 2 * (base + 1) + 1 = (2 * base + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFramePrefixSumRevProgram))^[2 * base + 1]
          (some (unaryFramePrefixSumCfg .loadBase (some .tick) buffer₂ test
            (encodeUnaryFrameBlock base ++ tail) output (() :: current)
            saved)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem prefixSum_emitCurrent_eval (value : Nat)
    (first : UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) (saved : List Unit) :
    (flip Option.bind (step unaryFramePrefixSumRevProgram))^[3 * value + 1]
      (some (unaryFramePrefixSumCfg (.emitCurrent first)
        buffer₁ buffer₂ test input output (List.replicate value ()) saved)) =
      some (unaryFramePrefixSumCfg (.pushSeparator first)
        buffer₁ buffer₂ false input (List.replicate value .tick ++ output)
        [] (List.replicate value () ++ saved)) := by
  induction value generalizing test output saved with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFramePrefixSumRevProgram))^[
            3 * value + 1]
          (some (unaryFramePrefixSumCfg (.emitCurrent first)
            buffer₁ buffer₂ true input (.tick :: output)
            (List.replicate value ()) (() :: saved))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (() :: saved)

private theorem prefixSum_restoreCurrent_eval (value : Nat)
    (first : UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (currentUnits : List Unit) :
    (flip Option.bind (step unaryFramePrefixSumRevProgram))^[2 * value + 1]
      (some (unaryFramePrefixSumCfg (.restoreCurrent first)
        buffer₁ buffer₂ test input output currentUnits
        (List.replicate value ()))) =
      some (unaryFramePrefixSumCfg (.consumeFirst first)
        buffer₁ buffer₂ false input output
        (List.replicate value () ++ currentUnits) []) := by
  induction value generalizing test currentUnits with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFramePrefixSumRevProgram))^[
            2 * value + 1]
          (some (unaryFramePrefixSumCfg (.restoreCurrent first)
            buffer₁ buffer₂ true input output (() :: currentUnits)
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (() :: currentUnits)

private theorem prefixSum_loadIncrement_eval (increment : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) (current saved : List Unit) :
    (flip Option.bind (step unaryFramePrefixSumRevProgram))^[
        2 * increment + 1]
      (some (unaryFramePrefixSumCfg .loadIncrement
        buffer₁ buffer₂ test (encodeUnaryFrameBlock increment ++ tail)
        output current saved)) =
      some (unaryFramePrefixSumCfg .check (some .separator) buffer₂ test
        tail output (List.replicate increment () ++ current) saved) := by
  induction increment generalizing buffer₁ current with
  | zero => rfl
  | succ increment ih =>
      rw [show 2 * (increment + 1) + 1 =
          (2 * increment + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFramePrefixSumRevProgram))^[
            2 * increment + 1]
          (some (unaryFramePrefixSumCfg .loadIncrement
            (some .tick) buffer₂ test
            (encodeUnaryFrameBlock increment ++ tail) output
            (() :: current) saved)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

/-- A uniform phase bound for one emitted prefix and one consumed increment. -/
def unaryFramePrefixSumPhaseCost (current increment : Nat) : Nat :=
  5 * current + 2 * increment + 5

/-- One canonical increment frame emits the old accumulator and advances it
by exactly the encoded increment. -/
def unaryFramePrefixSum_onePhase (current increment : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (rest output : List UnaryFrameSym) :
    EvalsToInTime (step unaryFramePrefixSumRevProgram)
      (unaryFramePrefixSumCfg .check buffer₁ buffer₂ test
        (encodeUnaryFrameBlock increment ++ rest) output
        (List.replicate current ()) [])
      (some (unaryFramePrefixSumCfg .check (some .separator) buffer₂ false
        rest ((encodeUnaryFrameBlock current).reverse ++ output)
        (List.replicate (current + increment) ()) []))
      (unaryFramePrefixSumPhaseCost current increment) := by
  cases increment with
  | zero =>
      let afterPop := unaryFramePrefixSumCfg
        (.emitCurrent .separator) (some .separator) buffer₂ test rest output
        (List.replicate current ()) []
      let afterEmit := unaryFramePrefixSumCfg
        (.pushSeparator .separator) (some .separator) buffer₂ false rest
        (List.replicate current .tick ++ output) []
        (List.replicate current ())
      let afterSeparator := unaryFramePrefixSumCfg
        (.restoreCurrent .separator) (some .separator) buffer₂ false rest
        ((encodeUnaryFrameBlock current).reverse ++ output) []
        (List.replicate current ())
      let afterRestore := unaryFramePrefixSumCfg
        (.consumeFirst .separator) (some .separator) buffer₂ false rest
        ((encodeUnaryFrameBlock current).reverse ++ output)
        (List.replicate current ()) []
      have hpop : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          (unaryFramePrefixSumCfg .check buffer₁ buffer₂ test
            (encodeUnaryFrameBlock 0 ++ rest) output
            (List.replicate current ()) []) (some afterPop) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hemit : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterPop (some afterEmit) (3 * current + 1) :=
        ⟨⟨3 * current + 1, by
          simpa [afterPop, afterEmit] using
            prefixSum_emitCurrent_eval current .separator
              (some .separator) buffer₂ test rest output []⟩, le_rfl⟩
      have hseparator : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterEmit (some afterSeparator) 1 :=
        ⟨⟨1, by
          change some (unaryFramePrefixSumCfg
            (.restoreCurrent .separator) (some .separator) buffer₂ false rest
            (.separator :: List.replicate current .tick ++ output) []
            (List.replicate current ())) = some afterSeparator
          simp [afterSeparator, encodeUnaryFrameBlock,
            List.reverse_append]⟩, le_rfl⟩
      have hrestore : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterSeparator (some afterRestore) (2 * current + 1) :=
        ⟨⟨2 * current + 1, by
          simpa [afterSeparator, afterRestore] using
            prefixSum_restoreCurrent_eval current .separator
              (some .separator) buffer₂ false rest
              ((encodeUnaryFrameBlock current).reverse ++ output) []⟩,
          le_rfl⟩
      have hconsume : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterRestore
          (some (unaryFramePrefixSumCfg .check (some .separator) buffer₂ false
            rest ((encodeUnaryFrameBlock current).reverse ++ output)
            (List.replicate current ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        1 (3 * current + 1) _ afterPop _ hpop hemit
      let h₂ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        _ 1 _ afterEmit _ h₁ hseparator
      let h₃ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        _ (2 * current + 1) _ afterSeparator _ h₂ hrestore
      let full := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        _ 1 _ afterRestore _ h₃ hconsume
      refine ⟨full.toEvalsTo, ?_⟩
      exact full.steps_le_m.trans (by
        simp [unaryFramePrefixSumPhaseCost]
        omega)
  | succ increment =>
      let afterPop := unaryFramePrefixSumCfg (.emitCurrent .tick)
        (some .tick) buffer₂ test (encodeUnaryFrameBlock increment ++ rest)
        output (List.replicate current ()) []
      let afterEmit := unaryFramePrefixSumCfg (.pushSeparator .tick)
        (some .tick) buffer₂ false (encodeUnaryFrameBlock increment ++ rest)
        (List.replicate current .tick ++ output) []
        (List.replicate current ())
      let afterSeparator := unaryFramePrefixSumCfg (.restoreCurrent .tick)
        (some .tick) buffer₂ false (encodeUnaryFrameBlock increment ++ rest)
        ((encodeUnaryFrameBlock current).reverse ++ output) []
        (List.replicate current ())
      let afterRestore := unaryFramePrefixSumCfg (.consumeFirst .tick)
        (some .tick) buffer₂ false (encodeUnaryFrameBlock increment ++ rest)
        ((encodeUnaryFrameBlock current).reverse ++ output)
        (List.replicate current ()) []
      let afterFirst := unaryFramePrefixSumCfg .loadIncrement
        (some .tick) buffer₂ false (encodeUnaryFrameBlock increment ++ rest)
        ((encodeUnaryFrameBlock current).reverse ++ output)
        (List.replicate (current + 1) ()) []
      have hpop : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          (unaryFramePrefixSumCfg .check buffer₁ buffer₂ test
            (encodeUnaryFrameBlock (increment + 1) ++ rest) output
            (List.replicate current ()) []) (some afterPop) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hemit : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterPop (some afterEmit) (3 * current + 1) :=
        ⟨⟨3 * current + 1, by
          simpa [afterPop, afterEmit] using
            prefixSum_emitCurrent_eval current .tick (some .tick) buffer₂ test
              (encodeUnaryFrameBlock increment ++ rest) output []⟩,
          le_rfl⟩
      have hseparator : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterEmit (some afterSeparator) 1 :=
        ⟨⟨1, by
          change some (unaryFramePrefixSumCfg (.restoreCurrent .tick)
            (some .tick) buffer₂ false
            (encodeUnaryFrameBlock increment ++ rest)
            (.separator :: List.replicate current .tick ++ output) []
            (List.replicate current ())) = some afterSeparator
          simp [afterSeparator, encodeUnaryFrameBlock,
            List.reverse_append]⟩, le_rfl⟩
      have hrestore : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterSeparator (some afterRestore) (2 * current + 1) :=
        ⟨⟨2 * current + 1, by
          simpa [afterSeparator, afterRestore] using
            prefixSum_restoreCurrent_eval current .tick (some .tick) buffer₂
              false (encodeUnaryFrameBlock increment ++ rest)
              ((encodeUnaryFrameBlock current).reverse ++ output) []⟩,
          le_rfl⟩
      have hconsume : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterRestore (some afterFirst) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hremaining : EvalsToInTime (step unaryFramePrefixSumRevProgram)
          afterFirst
          (some (unaryFramePrefixSumCfg .check (some .separator) buffer₂ false
            rest ((encodeUnaryFrameBlock current).reverse ++ output)
            (List.replicate (current + (increment + 1)) ()) []))
          (2 * increment + 1) :=
        ⟨⟨2 * increment + 1, by
          simpa [afterFirst, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            prefixSum_loadIncrement_eval increment (some .tick) buffer₂ false
              rest ((encodeUnaryFrameBlock current).reverse ++ output)
              (List.replicate (current + 1) ()) []⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        1 (3 * current + 1) _ afterPop _ hpop hemit
      let h₂ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        _ 1 _ afterEmit _ h₁ hseparator
      let h₃ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        _ (2 * current + 1) _ afterSeparator _ h₂ hrestore
      let h₄ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        _ 1 _ afterRestore _ h₃ hconsume
      let full := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        _ (2 * increment + 1) _ afterFirst _ h₄ hremaining
      refine ⟨full.toEvalsTo, ?_⟩
      exact full.steps_le_m.trans (by
        simp [unaryFramePrefixSumPhaseCost]
        omega)

/-- Accumulated uniform phase bound for a complete increment family. -/
def unaryFramePrefixSumPhaseSteps : Nat → List Nat → Nat
  | _, [] => 0
  | current, increment :: rest =>
      unaryFramePrefixSumPhaseCost current increment +
        unaryFramePrefixSumPhaseSteps (current + increment) rest

/-- Exact family-loop simulation, preserving an arbitrary reversed output
suffix. -/
def unaryFramePrefixSum_phases (current : Nat)
    (increments : List Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step unaryFramePrefixSumRevProgram)
      (unaryFramePrefixSumCfg .check buffer₁ buffer₂ test
        (encodeUnaryFrame increments ++ tail) output
        (List.replicate current ()) [])
      (some (unaryFramePrefixSumCfg .check
        (if increments.isEmpty then buffer₁ else some .separator)
        buffer₂
        (if increments.isEmpty then test else false)
        tail ((encodeUnaryFrame
          (unaryFramePrefixSumValuesFrom current increments)).reverse ++ output)
        (List.replicate (unaryFramePrefixSumFinal current increments) ()) []))
      (unaryFramePrefixSumPhaseSteps current increments) := by
  induction increments generalizing current buffer₁ buffer₂ test tail output with
  | nil =>
      exact ⟨⟨0, by simp [unaryFramePrefixSumValuesFrom,
        unaryFramePrefixSumFinal, encodeUnaryFrame]⟩, le_rfl⟩
  | cons increment rest ih =>
      let first := unaryFramePrefixSum_onePhase current increment
        buffer₁ buffer₂ test (encodeUnaryFrame rest ++ tail) output
      let remaining := ih (current + increment) (some .separator) buffer₂ false
        tail ((encodeUnaryFrameBlock current).reverse ++ output)
      let full := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
        (unaryFramePrefixSumPhaseCost current increment)
        (unaryFramePrefixSumPhaseSteps (current + increment) rest)
        _ _ _ first remaining
      simpa [unaryFramePrefixSumPhaseSteps,
        unaryFramePrefixSumValuesFrom, unaryFramePrefixSumFinal,
        encodeUnaryFrame, List.reverse_append, List.append_assoc,
        Nat.add_comm] using full

private theorem prefixSum_clearCurrent_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) (saved : List Unit) :
    (flip Option.bind (step unaryFramePrefixSumRevProgram))^[value + 1]
      (some (unaryFramePrefixSumCfg .clearCurrent buffer₁ buffer₂ test
        input output (List.replicate value ()) saved)) =
      some (unaryFramePrefixSumCfg .halt buffer₁ buffer₂ false
        input output [] saved) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFramePrefixSumRevProgram))^[value + 1]
          (some (unaryFramePrefixSumCfg .clearCurrent buffer₁ buffer₂ true
            input output (List.replicate value ()) saved)) = _
      simpa using ih true

/-- Complete reverse-output run on every canonical prefix-sum input. -/
def unaryFramePrefixSumRevSteps (frame : UnaryFramePrefixSum) : Nat :=
  2 * frame.base + 1 +
    unaryFramePrefixSumPhaseSteps frame.base frame.increments +
    unaryFramePrefixSumFinal frame.base frame.increments + 3

def unaryFramePrefixSumRev_run (frame : UnaryFramePrefixSum) :
    EvalsToInTime (step unaryFramePrefixSumRevProgram)
      (initialCfg unaryFramePrefixSumRevProgram
        (encodeUnaryFramePrefixSum frame))
      (some (haltCfg unaryFramePrefixSumRevProgram
        (unaryFramePrefixSumStream frame).reverse))
      (unaryFramePrefixSumRevSteps frame) := by
  let afterBase := unaryFramePrefixSumCfg .check (some .separator) none false
    (encodeUnaryFrame frame.increments) []
    (List.replicate frame.base ()) []
  have hbase : EvalsToInTime (step unaryFramePrefixSumRevProgram)
      (initialCfg unaryFramePrefixSumRevProgram
        (encodeUnaryFramePrefixSum frame))
      (some afterBase) (2 * frame.base + 1) := by
    exact ⟨⟨2 * frame.base + 1, by
      simpa [encodeUnaryFramePrefixSum, afterBase, initialCfg,
        unaryFramePrefixSumCfg, unaryFramePrefixSumRevProgram] using
        prefixSum_loadBase_eval frame.base none none false
          (encodeUnaryFrame frame.increments) [] [] []⟩, le_rfl⟩
  have hphases := unaryFramePrefixSum_phases frame.base frame.increments
    (some .separator) none false [] []
  let final := unaryFramePrefixSumFinal frame.base frame.increments
  let output := (unaryFramePrefixSumStream frame).reverse
  let afterPhases := unaryFramePrefixSumCfg .check
    (if frame.increments.isEmpty then some .separator else some .separator)
    none false [] output (List.replicate final ()) []
  have hphases' : EvalsToInTime (step unaryFramePrefixSumRevProgram)
      afterBase (some afterPhases)
      (unaryFramePrefixSumPhaseSteps frame.base frame.increments) := by
    simpa [afterBase, afterPhases, output, final,
      unaryFramePrefixSumStream, unaryFramePrefixSumValues] using hphases
  let afterCheck := unaryFramePrefixSumCfg .clearCurrent none none false
    [] output (List.replicate final ()) []
  let beforeHalt := unaryFramePrefixSumCfg .halt none none false
    [] output [] []
  have hcheck : EvalsToInTime (step unaryFramePrefixSumRevProgram)
      afterPhases (some afterCheck) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step unaryFramePrefixSumRevProgram)
      afterCheck (some beforeHalt) (final + 1) := by
    exact ⟨⟨final + 1, by
      simpa [afterCheck, beforeHalt] using
        prefixSum_clearCurrent_eval final none none false
          [] output []⟩,
      le_rfl⟩
  have hhalt : EvalsToInTime (step unaryFramePrefixSumRevProgram)
      beforeHalt
      (some (haltCfg unaryFramePrefixSumRevProgram output)) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
    (2 * frame.base + 1)
    (unaryFramePrefixSumPhaseSteps frame.base frame.increments)
    _ afterBase _ hbase hphases'
  let h₂ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
    _ 1 _ afterPhases _ h₁ hcheck
  let h₃ := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
    _ (final + 1) _ afterCheck _ h₂ hclear
  let full := EvalsToInTime.trans (step unaryFramePrefixSumRevProgram)
    _ 1 _ beforeHalt _ h₃ hhalt
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [unaryFramePrefixSumRevSteps, final]
    omega)

end CLRS.Chapter34.Turing.PolyBuilder
