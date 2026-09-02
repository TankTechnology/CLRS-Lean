import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCurrent
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: clause comparison

This file verifies the reversible unary comparison of a prior occurrence's
clause index with the current occurrence's stored clause index.  The scan
copies the prior field to the restoration stack and restores counter two.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private def priorClausePairBuffer
    (initial : Option UnaryFrameSym) (count : Nat) : Option UnaryFrameSym :=
  if count = 0 then initial else some .tick

private def priorClausePairTest (initial : Bool) (count : Nat) : Bool :=
  if count = 0 then initial else true

private theorem replicate_tick_append_tick (count : Nat)
    (tail : List UnaryFrameSym) :
    List.replicate count .tick ++ .tick :: tail =
      List.replicate (count + 1) .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

/-- Consume a prefix for which both unary clause counters are nonempty. -/
private def compatibilityEdges_priorClausePairs_eval
    (currentPolarity : Bool) (count remaining : Nat)
    (tail input work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test input output
        (List.replicate count .tick ++ tail) work₂
        upper (remaining + count) variableCount)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (priorClausePairBuffer buffer₁ count) buffer₂
        (priorClausePairTest test count)
        (List.replicate count .tick ++ input) output tail work₂
        upper remaining variableCount)) (2 * count) := by
  induction count generalizing buffer₁ test input remaining with
  | zero => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesCfg
        (.priorClause currentPolarity false) (some .tick) buffer₂ true
        (.tick :: input) output (List.replicate count .tick ++ tail) work₂
        upper (remaining + count) variableCount
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.priorClause currentPolarity false)
            buffer₁ buffer₂ test input output
            (List.replicate (count + 1) .tick ++ tail) work₂
            upper (remaining + (count + 1)) variableCount)
          (some after) 2 := by
        rw [show remaining + (count + 1) = (remaining + count) + 1 by omega]
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, after,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some .tick) (test := true)
        (input := .tick :: input) (remaining := remaining)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count) _ after _ first rest
      convert full using 1 <;>
        simp [priorClausePairBuffer, priorClausePairTest,
          List.replicate_add, List.append_assoc,
          Nat.add_comm] <;> omega

/-- Drain the saved equal prefix to work two while restoring counter two. -/
private def compatibilityEdges_priorClauseDrain_eval
    (currentPolarity clauseEqual : Bool) (count accumulated : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg
        (.priorClauseDrain currentPolarity clauseEqual)
        buffer₁ buffer₂ test (List.replicate count .tick) output
        tail work₂ upper accumulated variableCount)
      (some (compatibilityEdgesCfg
        (.priorClausePushSeparator currentPolarity clauseEqual)
        buffer₁ none test [] output tail
        (List.replicate count .tick ++ work₂)
        upper (accumulated + count) variableCount)) (2 * count + 1) := by
  induction count generalizing accumulated buffer₂ work₂ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesCfg
        (.priorClauseDrain currentPolarity clauseEqual)
        buffer₁ (some .tick) test (List.replicate count .tick) output
        tail (.tick :: work₂) upper (accumulated + 1) variableCount
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg
            (.priorClauseDrain currentPolarity clauseEqual)
            buffer₁ buffer₂ test (List.replicate (count + 1) .tick)
            output tail work₂ upper accumulated variableCount)
          (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, after,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (accumulated := accumulated + 1)
        (buffer₂ := some .tick) (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count + 1) _ after _ first rest
      convert full using 1 <;>
        simp [List.replicate_add,
          List.append_assoc, Nat.add_comm,
          Nat.add_left_comm] <;> omega

/-- Once the current counter is exhausted, move further prior-clause ticks
directly to the restoration stack. -/
private def compatibilityEdges_priorClauseTooLong_eval
    (currentPolarity : Bool) (count : Nat)
    (tail input work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (upper variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity true)
        (some .tick) (some .tick) false input output
        (List.replicate count .tick ++ tail) work₂ upper 0 variableCount)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity true)
        (some .tick) (some .tick) false input output tail
        (List.replicate count .tick ++ work₂) upper 0 variableCount))
      (2 * count) := by
  induction count generalizing work₂ with
  | zero => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | succ count ih =>
      let after := compatibilityEdgesCfg (.priorClause currentPolarity true)
        (some .tick) (some .tick) false input output
        (List.replicate count .tick ++ tail) (.tick :: work₂)
        upper 0 variableCount
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgesCfg (.priorClause currentPolarity true)
            (some .tick) (some .tick) false input output
            (List.replicate (count + 1) .tick ++ tail) work₂
            upper 0 variableCount) (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, after,
            List.replicate_succ, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * count) _ after _ first rest
      convert full using 1 <;> try omega
      simp only [replicate_tick_append_tick]

/-- Enter the too-long state on the first prior-clause tick after counter two
has reached zero, then consume the remaining excess ticks. -/
private def compatibilityEdges_priorClauseExcess_eval
    (currentPolarity : Bool) (excess : Nat)
    (tail input work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test input output
        (List.replicate (excess + 1) .tick ++ tail) work₂
        upper 0 variableCount)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity true)
        (some .tick) (some .tick) false input output tail
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 variableCount)) (2 * (excess + 1) + 1) := by
  let after := compatibilityEdgesCfg (.priorClause currentPolarity true)
    (some .tick) (some .tick) false input output
    (List.replicate excess .tick ++ tail) (.tick :: work₂)
    upper 0 variableCount
  have first : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test input output
        (List.replicate (excess + 1) .tick ++ tail) work₂
        upper 0 variableCount) (some after) 3 := by
    exact ⟨⟨3, by
      simp [Function.iterate_succ_apply, flip, after, List.replicate_succ,
        step, compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
      le_rfl⟩
  have rest := compatibilityEdges_priorClauseTooLong_eval currentPolarity
    excess tail input (.tick :: work₂) output upper variableCount
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    3 (2 * excess) _ after _ first rest
  convert full using 1 <;>
    simp [List.replicate_add, List.append_assoc] <;> omega

/-- Equal unary clause fields are recognized, copied, and counter two is
restored exactly. -/
def compatibilityEdges_priorClauseEqRun
    (currentPolarity : Bool) (clause : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate clause .tick ++ .separator :: tail) work₂
        upper clause variableCount)
      (some (compatibilityEdgesCfg
        (.priorPolarity currentPolarity true) (some .separator) none false
        [] output tail (.separator :: List.replicate clause .tick ++ work₂)
        upper clause variableCount)) (4 * clause + 5) := by
  have pairs := compatibilityEdges_priorClausePairs_eval currentPolarity
    clause 0 (.separator :: tail) [] work₂ output buffer₁ buffer₂ test
    upper variableCount
  have pairs' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate clause .tick ++ .separator :: tail) work₂
        upper clause variableCount)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (priorClausePairBuffer buffer₁ clause) buffer₂
        (priorClausePairTest test clause) (List.replicate clause .tick)
        output (.separator :: tail) work₂ upper 0 variableCount))
      (2 * clause) := by
    simpa using pairs
  have middle : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (priorClausePairBuffer buffer₁ clause) buffer₂
        (priorClausePairTest test clause) (List.replicate clause .tick)
        output (.separator :: tail) work₂ upper 0 variableCount)
      (some (compatibilityEdgesCfg (.priorClauseDrain currentPolarity true)
        (some .separator) buffer₂ false (List.replicate clause .tick)
        output tail work₂ upper 0 variableCount)) 3 := by
    exact ⟨⟨3, by
      simp [Function.iterate_succ_apply, flip, step, compatibilityEdgesProgram,
        compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  have drain := compatibilityEdges_priorClauseDrain_eval currentPolarity true
    clause 0 tail work₂ output (some .separator) buffer₂ false
    upper variableCount
  have drain' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClauseDrain currentPolarity true)
        (some .separator) buffer₂ false (List.replicate clause .tick)
        output tail work₂ upper 0 variableCount)
      (some (compatibilityEdgesCfg
        (.priorClausePushSeparator currentPolarity true)
        (some .separator) none false [] output tail
        (List.replicate clause .tick ++ work₂)
        upper clause variableCount)) (2 * clause + 1) := by
    simpa using drain
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClausePushSeparator currentPolarity true)
        (some .separator) none false [] output tail
        (List.replicate clause .tick ++ work₂)
        upper clause variableCount)
      (some (compatibilityEdgesCfg (.priorPolarity currentPolarity true)
        (some .separator) none false [] output tail
        (.separator :: List.replicate clause .tick ++ work₂)
        upper clause variableCount)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * clause) 3 _ _ _ pairs' middle
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * clause + 1) _ _ _ first drain'
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ second finish
  convert full using 1 <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- If the prior clause is smaller, the comparison returns false and restores
the strictly larger current clause counter. -/
def compatibilityEdges_priorClauseLtRun
    (currentPolarity : Bool) (priorClause excess : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate priorClause .tick ++ .separator :: tail) work₂
        upper (priorClause + excess + 1) variableCount)
      (some (compatibilityEdgesCfg
        (.priorPolarity currentPolarity false) (some .separator) none true
        [] output tail
        (.separator :: List.replicate priorClause .tick ++ work₂)
        upper (priorClause + excess + 1) variableCount))
      (4 * priorClause + 6) := by
  have pairs := compatibilityEdges_priorClausePairs_eval currentPolarity
    priorClause (excess + 1) (.separator :: tail) [] work₂ output
    buffer₁ buffer₂ test upper variableCount
  have pairs' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate priorClause .tick ++ .separator :: tail) work₂
        upper (priorClause + excess + 1) variableCount)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (priorClausePairBuffer buffer₁ priorClause) buffer₂
        (priorClausePairTest test priorClause)
        (List.replicate priorClause .tick) output (.separator :: tail) work₂
        upper (excess + 1) variableCount)) (2 * priorClause) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pairs
  have middle : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (priorClausePairBuffer buffer₁ priorClause) buffer₂
        (priorClausePairTest test priorClause)
        (List.replicate priorClause .tick) output (.separator :: tail) work₂
        upper (excess + 1) variableCount)
      (some (compatibilityEdgesCfg (.priorClauseDrain currentPolarity false)
        (some .separator) buffer₂ true (List.replicate priorClause .tick)
        output tail work₂ upper (excess + 1) variableCount)) 4 := by
    exact ⟨⟨4, by
      simp [Function.iterate_succ_apply, flip, step, compatibilityEdgesProgram,
        compatibilityEdgesCfg, stepOp, List.replicate_succ]⟩, le_rfl⟩
  have drain := compatibilityEdges_priorClauseDrain_eval currentPolarity false
    priorClause (excess + 1) tail work₂ output (some .separator)
    buffer₂ true upper variableCount
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClausePushSeparator currentPolarity false)
        (some .separator) none true [] output tail
        (List.replicate priorClause .tick ++ work₂)
        upper (excess + 1 + priorClause) variableCount)
      (some (compatibilityEdgesCfg (.priorPolarity currentPolarity false)
        (some .separator) none true [] output tail
        (.separator :: List.replicate priorClause .tick ++ work₂)
        upper (excess + 1 + priorClause) variableCount)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * priorClause) 4 _ _ _ pairs' middle
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * priorClause + 1) _ _ _ first drain
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ second finish
  convert full using 1 <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- If the prior clause is larger, its excess unary suffix is copied directly
and the smaller current clause counter is still restored exactly. -/
def compatibilityEdges_priorClauseGtRun
    (currentPolarity : Bool) (currentClause excess : Nat)
    (tail work₂ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper variableCount : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate (currentClause + excess + 1) .tick ++
          .separator :: tail) work₂ upper currentClause variableCount)
      (some (compatibilityEdgesCfg
        (.priorPolarity currentPolarity false) (some .separator) none false
        [] output tail
        (.separator :: List.replicate (currentClause + excess + 1) .tick ++
          work₂) upper currentClause variableCount))
      (4 * currentClause + 2 * (excess + 1) + 5) := by
  let excessTail := List.replicate (excess + 1) .tick ++ .separator :: tail
  have pairs := compatibilityEdges_priorClausePairs_eval currentPolarity
    currentClause 0 excessTail [] work₂ output buffer₁ buffer₂ test
    upper variableCount
  have pairs' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity false)
        buffer₁ buffer₂ test [] output
        (List.replicate (currentClause + excess + 1) .tick ++
          .separator :: tail) work₂ upper currentClause variableCount)
      (some (compatibilityEdgesCfg (.priorClause currentPolarity false)
        (priorClausePairBuffer buffer₁ currentClause) buffer₂
        (priorClausePairTest test currentClause)
        (List.replicate currentClause .tick) output excessTail work₂
        upper 0 variableCount)) (2 * currentClause) := by
    simpa [excessTail, List.replicate_add, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pairs
  have extra := compatibilityEdges_priorClauseExcess_eval currentPolarity
    excess (.separator :: tail) (List.replicate currentClause .tick) work₂
    output (priorClausePairBuffer buffer₁ currentClause) buffer₂
    (priorClausePairTest test currentClause) upper variableCount
  have middle : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClause currentPolarity true)
        (some .tick) (some .tick) false (List.replicate currentClause .tick)
        output (.separator :: tail)
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 variableCount)
      (some (compatibilityEdgesCfg (.priorClauseDrain currentPolarity false)
        (some .separator) (some .tick) false
        (List.replicate currentClause .tick) output tail
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 variableCount)) 2 := by
    exact ⟨⟨2, by
      simp [Function.iterate_succ_apply, flip, step, compatibilityEdgesProgram,
        compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  have drain := compatibilityEdges_priorClauseDrain_eval currentPolarity false
    currentClause 0 tail (List.replicate (excess + 1) .tick ++ work₂)
    output (some .separator) (some .tick) false upper variableCount
  have drain' : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClauseDrain currentPolarity false)
        (some .separator) (some .tick) false
        (List.replicate currentClause .tick) output tail
        (List.replicate (excess + 1) .tick ++ work₂)
        upper 0 variableCount)
      (some (compatibilityEdgesCfg
        (.priorClausePushSeparator currentPolarity false)
        (some .separator) none false [] output tail
        (List.replicate currentClause .tick ++
          (List.replicate (excess + 1) .tick ++ work₂))
        upper currentClause variableCount)) (2 * currentClause + 1) := by
    simpa using drain
  have finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg (.priorClausePushSeparator currentPolarity false)
        (some .separator) none false [] output tail
        (List.replicate currentClause .tick ++
          (List.replicate (excess + 1) .tick ++ work₂))
        upper currentClause variableCount)
      (some (compatibilityEdgesCfg (.priorPolarity currentPolarity false)
        (some .separator) none false [] output tail
        (.separator :: (List.replicate currentClause .tick ++
          (List.replicate (excess + 1) .tick ++ work₂)))
        upper currentClause variableCount)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * currentClause) (2 * (excess + 1) + 1) _ _ _ pairs' extra
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 2 _ _ _ first middle
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * currentClause + 1) _ _ _ second drain'
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ third finish
  convert full using 1 <;>
    simp [List.replicate_add, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

end TMClique
end Turing
end Chapter34
end CLRS
