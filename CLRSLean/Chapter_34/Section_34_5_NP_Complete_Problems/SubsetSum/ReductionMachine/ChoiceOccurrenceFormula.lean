import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceClause
import Mathlib.Tactic

/-!
# Choice occurrence counter: one formula batch

This file composes clause scans and finite-digit dispatch across one canonical
formula copy.  Empty clauses are handled explicitly, and the final batch
sentinel emits the item boundary and advances the positive variable index.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Canonical formula embedded in the batch alphabet. -/
def choiceOccurrenceFormulaInput (formula : CNF) : List ChoiceBatchSym :=
  (encCNF formula).map .formula

@[simp] theorem choiceOccurrenceFormulaInput_cons
    (clause : Clause) (formula : CNF) :
    choiceOccurrenceFormulaInput (clause :: formula) =
      .formula .clauseMark ::
        (choiceOccurrenceClauseInput clause ++
          choiceOccurrenceFormulaInput formula) := by
  simp [choiceOccurrenceFormulaInput, encCNF, encClause,
    choiceOccurrenceClauseInput,
    List.map_flatMap]
  rfl

/-- Clause scan that also covers the empty-clause case.  Its final buffer and
test bit are deliberately exposed because the following boundary pop accepts
either state. -/
private def choiceOccurrence_clauseMaybeRun (truth : Bool)
    (index clauseCount : Nat) (clause : Clause)
    (boundary : ChoiceBatchSym)
    (hboundary : boundary ≠ .formula .endMark)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan true)
        buffer₁ buffer₂ test
        (choiceOccurrenceClauseInput clause ++ boundary :: tail)
        output work₁ work₂ (index + 1) clauseCount 0)
      (some (choiceOccurrenceCfg truth (.scan true)
        (if clause.isEmpty then buffer₁ else some boundary)
        buffer₂ (if clause.isEmpty then test else false)
        (boundary :: tail) output work₁ work₂ (index + 1)
        (clauseCount + clause.count (itemLiteral index truth)) 0))
      (choiceOccurrenceClauseSteps index clause) := by
  cases clause with
  | nil =>
      exact ⟨⟨0, by
        simp [choiceOccurrenceClauseInput,
          choiceOccurrenceCfg]⟩, le_rfl⟩
  | cons literal clause =>
      simpa using choiceOccurrence_clauseRun truth index clauseCount
        literal clause boundary hboundary tail work₁ work₂ output
        buffer₁ buffer₂ test

/-- Budget from the contents of the current clause through all remaining
clauses and the final item boundary. -/
def choiceOccurrenceRemainingSteps (truth : Bool) (index : Nat) : CNF → Nat
  | [] => 0
  | clause :: formula =>
      choiceOccurrenceClauseSteps index clause + 1 +
        choiceOccurrenceDispatchSteps
          (clause.count (itemLiteral index truth)) +
        choiceOccurrenceRemainingSteps truth index formula

private def choiceOccurrence_popClauseBoundaryRun (truth : Bool)
    (index count : Nat) (next : Clause) (formula : CNF)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan true)
        buffer₁ buffer₂ test
        (.formula .clauseMark ::
          (choiceOccurrenceClauseInput next ++
            choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail))
        output work₁ work₂ (index + 1) count 0)
      (some (choiceOccurrenceCfg truth (.dispatchCount false)
        (some (.formula .clauseMark)) buffer₂ test
        (choiceOccurrenceClauseInput next ++
          choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
        output work₁ work₂ (index + 1) count 0)) 1 := by
  exact ⟨⟨1, by
    simp [flip, step, choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp]⟩,
    le_rfl⟩

private def choiceOccurrence_popBatchEndRun (truth : Bool)
    (index count : Nat) (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan true)
        buffer₁ buffer₂ test (.batchEnd :: tail)
        output work₁ work₂ (index + 1) count 0)
      (some (choiceOccurrenceCfg truth (.dispatchCount true)
        (some .batchEnd) buffer₂ test tail
        output work₁ work₂ (index + 1) count 0)) 1 := by
  exact ⟨⟨1, by
    simp [flip, step, choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp]⟩,
    le_rfl⟩

/-- Starting just after the current clause marker, process this clause, every
remaining clause, and the final batch sentinel. -/
def choiceOccurrence_remainingRun (truth : Bool)
    (index : Nat) (clause : Clause) (formula : CNF)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan true)
        buffer₁ buffer₂ test
        (choiceOccurrenceClauseInput clause ++
          choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
        output work₁ work₂ (index + 1) 0 0)
      (some (choiceOccurrenceCfg truth (.scan false)
        (some .batchEnd) buffer₂ false tail
        (.itemEnd ::
          (choiceOccurrenceDigits (clause :: formula) index truth).reverse ++
            output)
        work₁ work₂ (index + 2) 0 0))
      (choiceOccurrenceRemainingSteps truth index (clause :: formula)) := by
  induction formula generalizing clause output buffer₁ test with
  | nil =>
      have scan := choiceOccurrence_clauseMaybeRun truth index 0 clause
        .batchEnd (by simp) tail work₁ work₂ output
        buffer₁ buffer₂ test
      have pop := choiceOccurrence_popBatchEndRun truth index
        (clause.count (itemLiteral index truth)) tail work₁ work₂ output
        (if clause.isEmpty then buffer₁ else some .batchEnd) buffer₂
        (if clause.isEmpty then test else false)
      have dispatch := choiceOccurrence_dispatchRun truth true
        (clause.count (itemLiteral index truth)) (index + 1)
        tail work₁ work₂ output (some .batchEnd) buffer₂
        (if clause.isEmpty then test else false)
      let first := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceClauseSteps index clause) 1 _ _ _ scan (by
          simpa only [Nat.zero_add] using pop)
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (1 + choiceOccurrenceClauseSteps index clause)
        (choiceOccurrenceDispatchSteps
          (clause.count (itemLiteral index truth))) _ _ _ first dispatch
      simpa [choiceOccurrenceRemainingSteps, choiceOccurrenceDigits,
        choiceOccurrenceFormulaInput, encCNF,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
  | cons next formula ih =>
      have scan := choiceOccurrence_clauseMaybeRun truth index 0 clause
        (.formula .clauseMark) (by simp) (choiceOccurrenceClauseInput next ++
          choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
        work₁ work₂ output buffer₁ buffer₂ test
      have pop := choiceOccurrence_popClauseBoundaryRun truth index
        (clause.count (itemLiteral index truth)) next formula tail work₁ work₂
        output (if clause.isEmpty then buffer₁ else some (.formula .clauseMark))
        buffer₂ (if clause.isEmpty then test else false)
      have dispatch := choiceOccurrence_dispatchRun truth false
        (clause.count (itemLiteral index truth)) (index + 1)
        (choiceOccurrenceClauseInput next ++
          choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
        work₁ work₂ output (some (.formula .clauseMark)) buffer₂
        (if clause.isEmpty then test else false)
      let digit := ChoiceCountSym.digit
        (occurrenceSmallDigit (clause.count (itemLiteral index truth)))
      have rest := ih (clause := next) (output := digit :: output)
        (buffer₁ := some (.formula .clauseMark)) (test := false)
      let first := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceClauseSteps index clause) 1 _ _ _ scan (by
          simpa only [Nat.zero_add] using pop)
      let second := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (1 + choiceOccurrenceClauseSteps index clause)
        (choiceOccurrenceDispatchSteps
          (clause.count (itemLiteral index truth))) _ _ _ first dispatch
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceDispatchSteps
            (clause.count (itemLiteral index truth)) +
          (1 + choiceOccurrenceClauseSteps index clause))
        (choiceOccurrenceRemainingSteps truth index (next :: formula))
        _ _ _ second rest
      simpa [choiceOccurrenceRemainingSteps, choiceOccurrenceDigits, digit,
        List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Process one canonical formula copy, including its first marker (if any)
and final batch sentinel. -/
def choiceOccurrence_formulaRun (truth : Bool)
    (index : Nat) (formula : CNF)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan false)
        buffer₁ buffer₂ test
        (choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
        output work₁ work₂ (index + 1) 0 0)
      (some (choiceOccurrenceCfg truth (.scan false)
        (some .batchEnd) buffer₂ (if formula.isEmpty then test else false) tail
        (.itemEnd :: (choiceOccurrenceDigits formula index truth).reverse ++
          output)
        work₁ work₂ (index + 2) 0 0))
      (choiceOccurrenceRemainingSteps truth index formula + 3) := by
  cases formula with
  | nil =>
      exact ⟨⟨3, by
        simp [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          choiceOccurrenceFormulaInput, encCNF, choiceOccurrenceDigits,
          List.replicate_succ]⟩, by
          change 3 ≤ 3
          exact le_rfl⟩
  | cons clause formula =>
      let after := choiceOccurrenceCfg truth (.scan true)
        (some (.formula .clauseMark)) buffer₂ test
        (choiceOccurrenceClauseInput clause ++
          choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
        output work₁ work₂ (index + 1) 0 0
      have enter : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.scan false)
            buffer₁ buffer₂ test
            (choiceOccurrenceFormulaInput (clause :: formula) ++
              .batchEnd :: tail)
            output work₁ work₂ (index + 1) 0 0)
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [after, flip, step, choiceOccurrenceProgram,
            choiceOccurrenceCfg, stepOp]⟩, le_rfl⟩
      have rest := choiceOccurrence_remainingRun truth index clause formula
        tail work₁ work₂ output (some (.formula .clauseMark)) buffer₂ test
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        1 (choiceOccurrenceRemainingSteps truth index (clause :: formula))
        _ after _ enter rest
      refine ⟨full.toEvalsTo, full.steps_le_m.trans ?_⟩
      omega

end CLRS.Chapter34.Turing.SubsetSumReduction
