import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesClause
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: variable comparison

This file verifies the reversible unary comparison of a prior occurrence's
variable code with the current occurrence's stored variable code.  The scan
copies the prior field to the restoration stack and restores counter three.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Proof-facing configuration with the compared variable code in counter three. -/
def compatibilityEdgesVariableCfg (label : CompatibilityEdgesLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (work₁ work₂ : List UnaryFrameSym)
    (upper variableCode clause : Nat) : BuilderCfg compatibilityEdgesProgram :=
  compatibilityEdgesCfg label buffer₁ buffer₂ test input output work₁ work₂
    upper clause variableCode

private def priorVariablePairBuffer
    (initial : Option UnaryFrameSym) (count : Nat) : Option UnaryFrameSym :=
  if count = 0 then initial else some .tick

private def priorVariablePairTest (initial : Bool) (count : Nat) : Bool :=
  if count = 0 then initial else true

private theorem replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    List.replicate count .tick ++ .tick :: tail =
      List.replicate (count + 1) .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

/-- Consume a prefix for which both unary variable counters are nonempty. -/
private def compatibilityEdges_priorVariablePairs_eval
    (currentPolarity clauseEqual priorPolarity : Bool) (count remaining : Nat)
    (tail input work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test input output
        (List.replicate count .tick ++ tail) work₂
        upper (remaining + count) clause)
      (some (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        (priorVariablePairBuffer buffer₁ count) buffer₂
        (priorVariablePairTest test count)
        (List.replicate count .tick ++ input) output tail work₂
        upper remaining clause)) (2 * count) := by
  induction count generalizing buffer₁ test input remaining with
  | zero => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesVariableCfg
        (.priorVariable currentPolarity clauseEqual priorPolarity false) (some .tick) buffer₂ true
        (.tick :: input) output (List.replicate count .tick ++ tail) work₂
        upper (remaining + count) clause
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
            buffer₁ buffer₂ test input output
            (List.replicate (count + 1) .tick ++ tail) work₂
            upper (remaining + (count + 1)) clause)
          (some after) 2 := by
        rw [show remaining + (count + 1) = (remaining + count) + 1 by omega]
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, after,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some .tick) (test := true)
        (input := .tick :: input) (remaining := remaining)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count) _ after _ first rest
      convert full using 1 <;>
        simp [priorVariablePairBuffer, priorVariablePairTest,
          List.replicate_add, List.append_assoc,
          Nat.add_comm] <;> omega

/-- Drain the saved equal prefix to work two while restoring counter three. -/
private def compatibilityEdges_priorVariableDrain_eval
    (currentPolarity clauseEqual priorPolarity variableEqual : Bool) (count accumulated : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg
        (.priorVariableDrain currentPolarity clauseEqual priorPolarity variableEqual)
        buffer₁ buffer₂ test (List.replicate count .tick) output
        tail work₂ upper accumulated clause)
      (some (compatibilityEdgesVariableCfg
        (.priorVariablePushSeparator currentPolarity clauseEqual priorPolarity variableEqual)
        buffer₁ none test [] output tail
        (List.replicate count .tick ++ work₂)
        upper (accumulated + count) clause)) (2 * count + 1) := by
  induction count generalizing accumulated buffer₂ work₂ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesVariableCfg, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesVariableCfg
        (.priorVariableDrain currentPolarity clauseEqual priorPolarity variableEqual)
        buffer₁ (some .tick) test (List.replicate count .tick) output
        tail (.tick :: work₂) upper (accumulated + 1) clause
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesVariableCfg
            (.priorVariableDrain currentPolarity clauseEqual priorPolarity variableEqual)
            buffer₁ buffer₂ test (List.replicate (count + 1) .tick)
            output tail work₂ upper accumulated clause)
          (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, after,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (accumulated := accumulated + 1)
        (buffer₂ := some .tick) (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count + 1) _ after _ first rest
      convert full using 1 <;>
        simp [List.replicate_add,
          List.append_assoc, Nat.add_comm,
          Nat.add_left_comm] <;> omega

/-- Once the current counter is exhausted, move further prior-variable ticks
directly to the restoration stack. -/
private def compatibilityEdges_priorVariableTooLong_eval
    (currentPolarity clauseEqual priorPolarity : Bool) (count : Nat)
    (tail input work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity true)
        (some .tick) (some .tick) false input output
        (List.replicate count .tick ++ tail) work₂ upper 0 clause)
      (some (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity true)
        (some .tick) (some .tick) false input output tail
        (List.replicate count .tick ++ work₂) upper 0 clause))
      (2 * count) := by
  induction count generalizing work₂ with
  | zero => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity true)
        (some .tick) (some .tick) false input output
        (List.replicate count .tick ++ tail) (.tick :: work₂)
        upper 0 clause
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity true)
            (some .tick) (some .tick) false input output
            (List.replicate (count + 1) .tick ++ tail) work₂
            upper 0 clause) (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, after,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count) _ after _ first rest
      convert full using 1 <;> try omega
      simp only [replicate_tick_append_tick]

/-- Enter the too-long state on the first prior-variable tick after counter three
has reached zero, then consume the remaining excess ticks. -/
private def compatibilityEdges_priorVariableExcess_eval
    (currentPolarity clauseEqual priorPolarity : Bool) (excess : Nat)
    (tail input work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test input output
        (List.replicate (excess + 1) .tick ++ tail) work₂
        upper 0 clause)
      (some (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity true)
        (some .tick) (some .tick) false input output tail
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 clause)) (2 * (excess + 1) + 1) := by
  let after := compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity true)
    (some .tick) (some .tick) false input output
    (List.replicate excess .tick ++ tail) (.tick :: work₂)
    upper 0 clause
  have first : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test input output
        (List.replicate (excess + 1) .tick ++ tail) work₂
        upper 0 clause) (some after) 3 := by
    exact ⟨⟨3, by
      simp [Function.iterate_succ_apply, flip, after, List.replicate_succ,
        step, compatibilityEdgesProgram, compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩,
      le_rfl⟩
  have rest := compatibilityEdges_priorVariableTooLong_eval currentPolarity clauseEqual priorPolarity
    excess tail input (.tick :: work₂) output upper clause
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    3 (2 * excess) _ after _ first rest
  convert full using 1 <;>
    simp [List.replicate_add, List.append_assoc] <;> omega

/-- Equal unary variable fields are recognized, copied, and counter three is
restored exactly. -/
def compatibilityEdges_priorVariableEqRun
    (currentPolarity clauseEqual priorPolarity : Bool) (variableCode : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate variableCode .tick ++ .separator :: tail) work₂
        upper variableCode clause)
      (some (compatibilityEdgesVariableCfg
        (.priorEnd currentPolarity clauseEqual priorPolarity true) (some .separator) none false
        [] output tail (.separator :: List.replicate variableCode .tick ++ work₂)
        upper variableCode clause)) (4 * variableCode + 5) := by
  have pairs := compatibilityEdges_priorVariablePairs_eval currentPolarity clauseEqual priorPolarity
    variableCode 0 (.separator :: tail) [] work₂ output buffer₁ buffer₂ test
    upper clause
  have pairs' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate variableCode .tick ++ .separator :: tail) work₂
        upper variableCode clause)
      (some (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        (priorVariablePairBuffer buffer₁ variableCode) buffer₂
        (priorVariablePairTest test variableCode) (List.replicate variableCode .tick)
        output (.separator :: tail) work₂ upper 0 clause))
      (2 * variableCode) := by
    simpa using pairs
  have middle : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        (priorVariablePairBuffer buffer₁ variableCode) buffer₂
        (priorVariablePairTest test variableCode) (List.replicate variableCode .tick)
        output (.separator :: tail) work₂ upper 0 clause)
      (some (compatibilityEdgesVariableCfg (.priorVariableDrain currentPolarity clauseEqual priorPolarity true)
        (some .separator) buffer₂ false (List.replicate variableCode .tick)
        output tail work₂ upper 0 clause)) 3 := by
    exact ⟨⟨3, by
      simp [Function.iterate_succ_apply, flip, step, compatibilityEdgesProgram,
        compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  have drain := compatibilityEdges_priorVariableDrain_eval currentPolarity clauseEqual priorPolarity true
    variableCode 0 tail work₂ output (some .separator) buffer₂ false
    upper clause
  have drain' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariableDrain currentPolarity clauseEqual priorPolarity true)
        (some .separator) buffer₂ false (List.replicate variableCode .tick)
        output tail work₂ upper 0 clause)
      (some (compatibilityEdgesVariableCfg
        (.priorVariablePushSeparator currentPolarity clauseEqual priorPolarity true)
        (some .separator) none false [] output tail
        (List.replicate variableCode .tick ++ work₂)
        upper variableCode clause)) (2 * variableCode + 1) := by
    simpa using drain
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariablePushSeparator currentPolarity clauseEqual priorPolarity true)
        (some .separator) none false [] output tail
        (List.replicate variableCode .tick ++ work₂)
        upper variableCode clause)
      (some (compatibilityEdgesVariableCfg (.priorEnd currentPolarity clauseEqual priorPolarity true)
        (some .separator) none false [] output tail
        (.separator :: List.replicate variableCode .tick ++ work₂)
        upper variableCode clause)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesVariableCfg, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * variableCode) 3 _ _ _ pairs' middle
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * variableCode + 1) _ _ _ first drain'
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ second finish
  convert full using 1 <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- If the prior variable is smaller, the comparison returns false and restores
the strictly larger current variable counter. -/
def compatibilityEdges_priorVariableLtRun
    (currentPolarity clauseEqual priorPolarity : Bool) (priorVariable excess : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate priorVariable .tick ++ .separator :: tail) work₂
        upper (priorVariable + excess + 1) clause)
      (some (compatibilityEdgesVariableCfg
        (.priorEnd currentPolarity clauseEqual priorPolarity false) (some .separator) none true
        [] output tail
        (.separator :: List.replicate priorVariable .tick ++ work₂)
        upper (priorVariable + excess + 1) clause))
      (4 * priorVariable + 6) := by
  have pairs := compatibilityEdges_priorVariablePairs_eval currentPolarity clauseEqual priorPolarity
    priorVariable (excess + 1) (.separator :: tail) [] work₂ output
    buffer₁ buffer₂ test upper clause
  have pairs' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate priorVariable .tick ++ .separator :: tail) work₂
        upper (priorVariable + excess + 1) clause)
      (some (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        (priorVariablePairBuffer buffer₁ priorVariable) buffer₂
        (priorVariablePairTest test priorVariable)
        (List.replicate priorVariable .tick) output (.separator :: tail) work₂
        upper (excess + 1) clause)) (2 * priorVariable) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pairs
  have middle : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        (priorVariablePairBuffer buffer₁ priorVariable) buffer₂
        (priorVariablePairTest test priorVariable)
        (List.replicate priorVariable .tick) output (.separator :: tail) work₂
        upper (excess + 1) clause)
      (some (compatibilityEdgesVariableCfg (.priorVariableDrain currentPolarity clauseEqual priorPolarity false)
        (some .separator) buffer₂ true (List.replicate priorVariable .tick)
        output tail work₂ upper (excess + 1) clause)) 4 := by
    exact ⟨⟨4, by
      simp [Function.iterate_succ_apply, flip, step, compatibilityEdgesProgram,
        compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp, List.replicate_succ]⟩, le_rfl⟩
  have drain := compatibilityEdges_priorVariableDrain_eval currentPolarity clauseEqual priorPolarity false
    priorVariable (excess + 1) tail work₂ output (some .separator)
    buffer₂ true upper clause
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariablePushSeparator currentPolarity clauseEqual priorPolarity false)
        (some .separator) none true [] output tail
        (List.replicate priorVariable .tick ++ work₂)
        upper (excess + 1 + priorVariable) clause)
      (some (compatibilityEdgesVariableCfg (.priorEnd currentPolarity clauseEqual priorPolarity false)
        (some .separator) none true [] output tail
        (.separator :: List.replicate priorVariable .tick ++ work₂)
        upper (excess + 1 + priorVariable) clause)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesVariableCfg, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * priorVariable) 4 _ _ _ pairs' middle
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * priorVariable + 1) _ _ _ first drain
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ second finish
  convert full using 1 <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- If the prior variable is larger, its excess unary suffix is copied directly
and the smaller current variable counter is still restored exactly. -/
def compatibilityEdges_priorVariableGtRun
    (currentPolarity clauseEqual priorPolarity : Bool) (currentVariableCode excess : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate (currentVariableCode + excess + 1) .tick ++
          .separator :: tail) work₂ upper currentVariableCode clause)
      (some (compatibilityEdgesVariableCfg
        (.priorEnd currentPolarity clauseEqual priorPolarity false) (some .separator) none false
        [] output tail
        (.separator :: List.replicate (currentVariableCode + excess + 1) .tick ++
          work₂) upper currentVariableCode clause))
      (4 * currentVariableCode + 2 * (excess + 1) + 5) := by
  let excessTail := List.replicate (excess + 1) .tick ++ .separator :: tail
  have pairs := compatibilityEdges_priorVariablePairs_eval currentPolarity clauseEqual priorPolarity
    currentVariableCode 0 excessTail [] work₂ output buffer₁ buffer₂ test
    upper clause
  have pairs' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate (currentVariableCode + excess + 1) .tick ++
          .separator :: tail) work₂ upper currentVariableCode clause)
      (some (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity false)
        (priorVariablePairBuffer buffer₁ currentVariableCode) buffer₂
        (priorVariablePairTest test currentVariableCode)
        (List.replicate currentVariableCode .tick) output excessTail work₂
        upper 0 clause)) (2 * currentVariableCode) := by
    simpa [excessTail, List.replicate_add, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pairs
  have extra := compatibilityEdges_priorVariableExcess_eval currentPolarity clauseEqual priorPolarity
    excess (.separator :: tail) (List.replicate currentVariableCode .tick) work₂
    output (priorVariablePairBuffer buffer₁ currentVariableCode) buffer₂
    (priorVariablePairTest test currentVariableCode) upper clause
  have middle : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariable currentPolarity clauseEqual priorPolarity true)
        (some .tick) (some .tick) false (List.replicate currentVariableCode .tick)
        output (.separator :: tail)
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 clause)
      (some (compatibilityEdgesVariableCfg (.priorVariableDrain currentPolarity clauseEqual priorPolarity false)
        (some .separator) (some .tick) false
        (List.replicate currentVariableCode .tick) output tail
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 clause)) 2 := by
    exact ⟨⟨2, by
      simp [Function.iterate_succ_apply, flip, step, compatibilityEdgesProgram,
        compatibilityEdgesVariableCfg, compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  have drain := compatibilityEdges_priorVariableDrain_eval currentPolarity clauseEqual priorPolarity false
    currentVariableCode 0 tail (List.replicate (excess + 1) .tick ++ work₂)
    output (some .separator) (some .tick) false upper clause
  have drain' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariableDrain currentPolarity clauseEqual priorPolarity false)
        (some .separator) (some .tick) false
        (List.replicate currentVariableCode .tick) output tail
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 clause)
      (some (compatibilityEdgesVariableCfg
        (.priorVariablePushSeparator currentPolarity clauseEqual priorPolarity false)
        (some .separator) none false [] output tail
        (List.replicate currentVariableCode .tick ++
          (List.replicate (excess + 1) .tick ++ work₂))
        upper currentVariableCode clause)) (2 * currentVariableCode + 1) := by
    simpa using drain
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesVariableCfg (.priorVariablePushSeparator currentPolarity clauseEqual priorPolarity false)
        (some .separator) none false [] output tail
        (List.replicate currentVariableCode .tick ++
          (List.replicate (excess + 1) .tick ++ work₂))
        upper currentVariableCode clause)
      (some (compatibilityEdgesVariableCfg (.priorEnd currentPolarity clauseEqual priorPolarity false)
        (some .separator) none false [] output tail
        (.separator :: (List.replicate currentVariableCode .tick ++
          (List.replicate (excess + 1) .tick ++ work₂)))
        upper currentVariableCode clause)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesVariableCfg, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * currentVariableCode) (2 * (excess + 1) + 1) _ _ _ pairs' extra
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 2 _ _ _ first middle
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * currentVariableCode + 1) _ _ _ second drain'
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ third finish
  convert full using 1 <;>
    simp [List.replicate_add, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

end TMClique
end Turing
end Chapter34
end CLRS
