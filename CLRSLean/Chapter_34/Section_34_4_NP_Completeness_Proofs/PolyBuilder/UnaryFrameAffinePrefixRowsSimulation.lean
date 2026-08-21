import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameAffinePrefixRowsCore
import Mathlib.Tactic

/-!
# Growing affine-prefix rows: exact simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private theorem prefixRows_replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem prefixRows_loadBase_eval (base : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[2 * base + 1]
      (some (unaryFrameAffinePrefixRowsCfg .loadBase buffer₁ buffer₂ test
        (encodeUnaryFrameBlock base ++ tail) output work₁ work₂
        current saved)) =
      some (unaryFrameAffinePrefixRowsCfg .rows (some .separator) buffer₂ test
        tail output work₁ work₂ (List.replicate base () ++ current) saved) := by
  induction base generalizing buffer₁ current with
  | zero => rfl
  | succ base ih =>
      rw [show 2 * (base + 1) + 1 = (2 * base + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
            2 * base + 1]
          (some (unaryFrameAffinePrefixRowsCfg .loadBase (some .tick)
            buffer₂ test (encodeUnaryFrameBlock base ++ tail) output work₁
            work₂ (() :: current) saved)) = _
      simpa only [List.replicate_succ, prefixRows_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem prefixRows_transfer_eval
    (source target input output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (current saved : List Unit) :
    (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
        source.length + 1]
      (some (unaryFrameAffinePrefixRowsCfg .transfer buffer₁ buffer₂ test
        input output source target current saved)) =
      some (unaryFrameAffinePrefixRowsCfg .emitRestore none buffer₂ test
        input output [] (source.reverse ++ target) current saved) := by
  induction source generalizing buffer₁ target with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
            rest.length + 1]
          (some (unaryFrameAffinePrefixRowsCfg .transfer (some symbol)
            buffer₂ test input output rest (symbol :: target) current saved)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (buffer₁ := some symbol) (target := symbol :: target)

private theorem prefixRows_emitRestore_eval
    (source input output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (current saved : List Unit) :
    (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
        3 * source.length + 1]
      (some (unaryFrameAffinePrefixRowsCfg .emitRestore buffer₁ buffer₂ test
        input output work₁ source current saved)) =
      some (unaryFrameAffinePrefixRowsCfg .pushRowEnd buffer₁ none test input
        (source.reverse ++ output) (source.reverse ++ work₁) []
        current saved) := by
  induction source generalizing buffer₂ output work₁ with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 3 * (symbol :: rest).length + 1 =
          (3 * rest.length + 1) + 1 + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
            3 * rest.length + 1]
          (some (unaryFrameAffinePrefixRowsCfg .emitRestore buffer₁
            (some symbol) test input (symbol :: output)
            (symbol :: work₁) rest current saved)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (buffer₂ := some symbol) (output := symbol :: output)
          (work₁ := symbol :: work₁)

private theorem prefixRows_appendCurrent_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) (saved : List Unit) :
    (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
        3 * value + 1]
      (some (unaryFrameAffinePrefixRowsCfg .appendCurrent buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate value ()) saved)) =
      some (unaryFrameAffinePrefixRowsCfg .pushCurrentSeparator buffer₁
        buffer₂ false input output (List.replicate value .tick ++ work₁)
        work₂ [] (List.replicate value () ++ saved)) := by
  induction value generalizing test work₁ saved with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
            3 * value + 1]
          (some (unaryFrameAffinePrefixRowsCfg .appendCurrent buffer₁ buffer₂
            true input output (.tick :: work₁) work₂
            (List.replicate value ()) (() :: saved))) = _
      simpa only [List.replicate_succ, prefixRows_replicate_append_cons,
        List.cons_append] using
        ih (test := true) (work₁ := .tick :: work₁) (saved := () :: saved)

private theorem prefixRows_restoreCurrent_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current : List Unit) :
    (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
        2 * value + 1]
      (some (unaryFrameAffinePrefixRowsCfg .restoreCurrent buffer₁ buffer₂ test
        input output work₁ work₂ current (List.replicate value ()))) =
      some (unaryFrameAffinePrefixRowsCfg .advance buffer₁ buffer₂ false input
        output work₁ work₂ (List.replicate value () ++ current) []) := by
  induction value generalizing test current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
            2 * value + 1]
          (some (unaryFrameAffinePrefixRowsCfg .restoreCurrent buffer₁ buffer₂
            true input output work₁ work₂ (() :: current)
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, prefixRows_replicate_append_cons,
        List.cons_append] using ih true (() :: current)

/-- Exact cost of one outer row. -/
def unaryFrameAffinePrefixRowsPhaseCost
    (current payloadLength : Nat) : Nat :=
  4 * payloadLength + 5 * current + 8

private def unaryFrameAffinePrefixRows_onePhase
    (current : Nat) (payload : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (rest output : List UnaryFrameSym) :
    EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      (unaryFrameAffinePrefixRowsCfg .rows buffer₁ buffer₂ test
        (.tick :: rest) output payload.reverse []
        (List.replicate current ()) [])
      (some (unaryFrameAffinePrefixRowsCfg .rows none none false rest
        ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        (payload ++ encodeUnaryFrameBlock current).reverse []
        (List.replicate (current + 1) ()) []))
      (unaryFrameAffinePrefixRowsPhaseCost current payload.length) := by
  let afterPop := unaryFrameAffinePrefixRowsCfg .transfer (some .tick) buffer₂
    test rest output payload.reverse [] (List.replicate current ()) []
  let afterTransfer := unaryFrameAffinePrefixRowsCfg .emitRestore none buffer₂
    test rest output [] payload (List.replicate current ()) []
  let afterEmit := unaryFrameAffinePrefixRowsCfg .pushRowEnd none none test rest
    (payload.reverse ++ output) payload.reverse []
    (List.replicate current ()) []
  let afterEnd := unaryFrameAffinePrefixRowsCfg .appendCurrent none none test rest
    ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output) payload.reverse []
    (List.replicate current ()) []
  let afterAppend := unaryFrameAffinePrefixRowsCfg .pushCurrentSeparator none none
    false rest ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
    (List.replicate current .tick ++ payload.reverse) [] []
    (List.replicate current ())
  let afterSeparator := unaryFrameAffinePrefixRowsCfg .restoreCurrent none none
    false rest ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
    (payload ++ encodeUnaryFrameBlock current).reverse [] []
    (List.replicate current ())
  let beforeAdvance := unaryFrameAffinePrefixRowsCfg .advance none none false rest
    ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
    (payload ++ encodeUnaryFrameBlock current).reverse []
    (List.replicate current ()) []
  have hpop : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      (unaryFrameAffinePrefixRowsCfg .rows buffer₁ buffer₂ test
        (.tick :: rest) output payload.reverse []
        (List.replicate current ()) []) (some afterPop) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have htransfer : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterPop (some afterTransfer) (payload.length + 1) :=
    ⟨⟨payload.length + 1, by
      simpa [afterPop, afterTransfer] using
        prefixRows_transfer_eval payload.reverse [] rest output
          (some .tick) buffer₂ test (List.replicate current ()) []⟩, le_rfl⟩
  have hemit : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterTransfer (some afterEmit) (3 * payload.length + 1) :=
    ⟨⟨3 * payload.length + 1, by
      simpa [afterTransfer, afterEmit] using
        prefixRows_emitRestore_eval payload rest output [] none buffer₂ test
          (List.replicate current ()) []⟩, le_rfl⟩
  have hend : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterEmit (some afterEnd) 1 := by
    exact ⟨⟨1, by
      simp [afterEmit, afterEnd, List.reverse_append]
      rfl⟩, le_rfl⟩
  have happend : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterEnd (some afterAppend) (3 * current + 1) :=
    ⟨⟨3 * current + 1, by
      simpa [afterEnd, afterAppend] using
        prefixRows_appendCurrent_eval current none none test rest
          ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
          payload.reverse [] []⟩,
      le_rfl⟩
  have hseparator : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterAppend (some afterSeparator) 1 := by
    exact ⟨⟨1, by
      simp [afterAppend, afterSeparator, encodeUnaryFrameBlock,
        List.reverse_append, List.append_assoc]
      rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterSeparator (some beforeAdvance) (2 * current + 1) :=
    ⟨⟨2 * current + 1, by
      simpa [afterSeparator, beforeAdvance] using
        prefixRows_restoreCurrent_eval current none none false rest
          ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
          (payload ++ encodeUnaryFrameBlock current).reverse [] []⟩, le_rfl⟩
  have hadvance : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      beforeAdvance
      (some (unaryFrameAffinePrefixRowsCfg .rows none none false rest
        ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        (payload ++ encodeUnaryFrameBlock current).reverse []
        (List.replicate (current + 1) ()) [])) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    1 (payload.length + 1) _ afterPop _ hpop htransfer
  let h₂ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ (3 * payload.length + 1) _ afterTransfer _ h₁ hemit
  let h₃ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ 1 _ afterEmit _ h₂ hend
  let h₄ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ (3 * current + 1) _ afterEnd _ h₃ happend
  let h₅ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ 1 _ afterAppend _ h₄ hseparator
  let h₆ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ (2 * current + 1) _ afterSeparator _ h₅ hrestore
  let full := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ 1 _ beforeAdvance _ h₆ hadvance
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [unaryFrameAffinePrefixRowsPhaseCost]
    omega)

/-- Final accumulated payload. -/
def unaryFrameAffinePrefixRowsPayloadFrom :
    Nat → List UnaryFrameSym → Nat → List UnaryFrameSym
  | _, payload, 0 => payload
  | current, payload, count + 1 =>
      unaryFrameAffinePrefixRowsPayloadFrom (current + 1)
        (payload ++ encodeUnaryFrameBlock current) count

/-- Exact accumulated cost of all row phases. -/
def unaryFrameAffinePrefixRowsPhaseSteps :
    Nat → List UnaryFrameSym → Nat → Nat
  | _, _, 0 => 0
  | current, payload, count + 1 =>
      unaryFrameAffinePrefixRowsPhaseCost current payload.length +
        unaryFrameAffinePrefixRowsPhaseSteps (current + 1)
          (payload ++ encodeUnaryFrameBlock current) count

/-- Exact row-family loop, before consuming the terminating count
separator. -/
def unaryFrameAffinePrefixRows_phases
    (current : Nat) (payload : List UnaryFrameSym) (count : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      (unaryFrameAffinePrefixRowsCfg .rows buffer₁ buffer₂ test
        (List.replicate count .tick ++ .separator :: tail) output
        payload.reverse [] (List.replicate current ()) [])
      (some (unaryFrameAffinePrefixRowsCfg .rows
        (if count = 0 then buffer₁ else none)
        (if count = 0 then buffer₂ else none)
        (if count = 0 then test else false)
        (.separator :: tail)
        ((unaryFrameAffinePrefixRowsStreamFrom current payload count).reverse ++
          output)
        (unaryFrameAffinePrefixRowsPayloadFrom current payload count).reverse []
        (List.replicate (current + count) ()) []))
      (unaryFrameAffinePrefixRowsPhaseSteps current payload count) := by
  induction count generalizing current payload buffer₁ buffer₂ test output with
  | zero =>
      exact ⟨⟨0, by simp [unaryFrameAffinePrefixRowsStreamFrom,
        unaryFrameAffinePrefixRowsPayloadFrom]⟩, le_rfl⟩
  | succ count ih =>
      let first := unaryFrameAffinePrefixRows_onePhase current payload
        buffer₁ buffer₂ test
        (List.replicate count .tick ++ .separator :: tail) output
      let remaining := ih (current + 1)
        (payload ++ encodeUnaryFrameBlock current) none none false
        ((payload ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
      let full := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
        (unaryFrameAffinePrefixRowsPhaseCost current payload.length)
        (unaryFrameAffinePrefixRowsPhaseSteps (current + 1)
          (payload ++ encodeUnaryFrameBlock current) count)
        _ _ _ first remaining
      simpa [unaryFrameAffinePrefixRowsStreamFrom,
        unaryFrameAffinePrefixRowsPayloadFrom,
        unaryFrameAffinePrefixRowsPhaseSteps, List.reverse_append,
        List.append_assoc, List.replicate_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using full

private theorem prefixRows_clearCurrent_eval (value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) (saved : List Unit) :
    (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[value + 1]
      (some (unaryFrameAffinePrefixRowsCfg .clearCurrent buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate value ()) saved)) =
      some (unaryFrameAffinePrefixRowsCfg .clearPersistent buffer₁ buffer₂ false
        input output work₁ work₂ [] saved) := by
  induction value generalizing test with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
            value + 1]
          (some (unaryFrameAffinePrefixRowsCfg .clearCurrent buffer₁ buffer₂
            true input output work₁ work₂ (List.replicate value ()) saved)) = _
      simpa using ih true

private theorem prefixRows_clearPersistent_eval
    (persistent input output work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (current saved : List Unit) :
    (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
        persistent.length + 1]
      (some (unaryFrameAffinePrefixRowsCfg .clearPersistent buffer₁ buffer₂ test
        input output persistent work₂ current saved)) =
      some (unaryFrameAffinePrefixRowsCfg .halt none buffer₂ test input output
        [] work₂ current saved) := by
  induction persistent generalizing buffer₁ with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameAffinePrefixRowsRevProgram))^[
            rest.length + 1]
          (some (unaryFrameAffinePrefixRowsCfg .clearPersistent (some symbol)
            buffer₂ test input output rest work₂ current saved)) = _
      exact ih (some symbol)

/-- Exact full reverse-output step count. -/
def unaryFrameAffinePrefixRowsRevSteps
    (family : UnaryFrameAffinePrefixRows) : Nat :=
  let payload := unaryFrameAffinePrefixRowsPayloadFrom family.base [] family.count
  2 * family.base + 1 +
    unaryFrameAffinePrefixRowsPhaseSteps family.base [] family.count +
    (family.base + family.count) + payload.length + 4

/-- Complete exact run, stated first against the recursive row stream. -/
def unaryFrameAffinePrefixRowsRev_runFrom
    (family : UnaryFrameAffinePrefixRows) :
    EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      (initialCfg unaryFrameAffinePrefixRowsRevProgram
        (encodeUnaryFrameAffinePrefixRows family))
      (some (haltCfg unaryFrameAffinePrefixRowsRevProgram
        (unaryFrameAffinePrefixRowsStreamFrom family.base []
          family.count).reverse))
      (unaryFrameAffinePrefixRowsRevSteps family) := by
  let countInput := encodeUnaryFrameBlock family.count
  let afterBase := unaryFrameAffinePrefixRowsCfg .rows (some .separator) none
    false countInput [] [] [] (List.replicate family.base ()) []
  have hbase : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      (initialCfg unaryFrameAffinePrefixRowsRevProgram
        (encodeUnaryFrameAffinePrefixRows family))
      (some afterBase) (2 * family.base + 1) := by
    exact ⟨⟨2 * family.base + 1, by
      simpa [encodeUnaryFrameAffinePrefixRows, encodeUnaryFrame, countInput,
        afterBase, initialCfg, unaryFrameAffinePrefixRowsCfg,
        unaryFrameAffinePrefixRowsRevProgram] using
        prefixRows_loadBase_eval family.base none none false countInput
          [] [] [] [] []⟩, le_rfl⟩
  have hphases := unaryFrameAffinePrefixRows_phases family.base [] family.count
    (some .separator) none false [] []
  let stream := unaryFrameAffinePrefixRowsStreamFrom family.base [] family.count
  let payload := unaryFrameAffinePrefixRowsPayloadFrom family.base [] family.count
  let current := family.base + family.count
  let afterPhases := unaryFrameAffinePrefixRowsCfg .rows
    (if family.count = 0 then some .separator else none) none
    false [.separator] stream.reverse payload.reverse []
    (List.replicate current ()) []
  have hphases' : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterBase (some afterPhases)
      (unaryFrameAffinePrefixRowsPhaseSteps family.base [] family.count) := by
    simpa [afterBase, afterPhases, countInput, encodeUnaryFrameBlock,
      stream, payload, current] using hphases
  let afterCount := unaryFrameAffinePrefixRowsCfg .clearCurrent
    (some .separator) none false [] stream.reverse payload.reverse []
    (List.replicate current ()) []
  have hcount : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterPhases (some afterCount) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let afterCurrent := unaryFrameAffinePrefixRowsCfg .clearPersistent
    (some .separator) none false [] stream.reverse payload.reverse [] [] []
  have hcurrent : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterCount (some afterCurrent) (current + 1) :=
    ⟨⟨current + 1, by
      simpa [afterCount, afterCurrent] using
        prefixRows_clearCurrent_eval current (some .separator) none false
          [] stream.reverse payload.reverse [] []⟩, le_rfl⟩
  let beforeHalt := unaryFrameAffinePrefixRowsCfg .halt none none false []
    stream.reverse [] [] [] []
  have hpersistent : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      afterCurrent (some beforeHalt) (payload.length + 1) :=
    ⟨⟨payload.length + 1, by
      simpa [afterCurrent, beforeHalt] using
        prefixRows_clearPersistent_eval payload.reverse [] stream.reverse []
          (some .separator) none false [] []⟩, le_rfl⟩
  have hhalt : EvalsToInTime (step unaryFrameAffinePrefixRowsRevProgram)
      beforeHalt
      (some (haltCfg unaryFrameAffinePrefixRowsRevProgram stream.reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    (2 * family.base + 1)
    (unaryFrameAffinePrefixRowsPhaseSteps family.base [] family.count)
    _ afterBase _ hbase hphases'
  let h₂ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ 1 _ afterPhases _ h₁ hcount
  let h₃ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ (current + 1) _ afterCount _ h₂ hcurrent
  let h₄ := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ (payload.length + 1) _ afterCurrent _ h₃ hpersistent
  let full := EvalsToInTime.trans (step unaryFrameAffinePrefixRowsRevProgram)
    _ 1 _ beforeHalt _ h₄ hhalt
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [unaryFrameAffinePrefixRowsRevSteps, current, payload]
    omega)

end CLRS.Chapter34.Turing.PolyBuilder
