import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceFormula
import Mathlib.Tactic

/-!
# Choice occurrence counter: dimensions and batch family

The verified formula run is prefixed by the runtime width and variable-budget
cells, then iterated over consecutive variable indices.  The resulting output
is the exact reverse of the semantic occurrence stream for that index range.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

private def choiceOccurrenceDimensionSym (width : Bool) : ChoiceBatchSym :=
  if width then .widthTick else .variableTick

private def choiceOccurrence_skipDimensionRun (truth width : Bool)
    (count indexCode : Nat) (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan false)
        buffer₁ buffer₂ test
        (List.replicate count (choiceOccurrenceDimensionSym width) ++ tail)
        output work₁ work₂ indexCode 0 0)
      (some (choiceOccurrenceCfg truth (.scan false)
        (if count = 0 then buffer₁
         else some (choiceOccurrenceDimensionSym width))
        buffer₂ test tail output work₁ work₂ indexCode 0 0)) count := by
  induction count generalizing buffer₁ with
  | zero => exact ⟨⟨0, by simp [choiceOccurrenceCfg]⟩, le_rfl⟩
  | succ count ih =>
      let after := choiceOccurrenceCfg truth (.scan false)
        (some (choiceOccurrenceDimensionSym width)) buffer₂ test
        (List.replicate count (choiceOccurrenceDimensionSym width) ++ tail)
        output work₁ work₂ indexCode 0 0
      have first : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.scan false)
            buffer₁ buffer₂ test
            (List.replicate (count + 1)
              (choiceOccurrenceDimensionSym width) ++ tail)
            output work₁ work₂ indexCode 0 0)
          (some after) 1 := by
        cases width <;>
          exact ⟨⟨1, by
            simp [after, choiceOccurrenceDimensionSym,
              List.replicate_succ, flip, step, choiceOccurrenceProgram,
              choiceOccurrenceCfg, stepOp]⟩, le_rfl⟩
      have rest := ih
        (buffer₁ := some (choiceOccurrenceDimensionSym width))
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        1 count _ after _ first rest
      simpa [Nat.add_assoc] using full

/-- One complete runtime batch with explicit dimension counts. -/
def choiceOccurrenceBatchInput (width variableCount : Nat)
    (formula : CNF) : List ChoiceBatchSym :=
  List.replicate width .widthTick ++
    List.replicate variableCount .variableTick ++
    choiceOccurrenceFormulaInput formula ++ [.batchEnd]

/-- Exact cost of one complete runtime batch. -/
def choiceOccurrenceBatchSteps (truth : Bool) (index width variableCount : Nat)
    (formula : CNF) : Nat :=
  width + variableCount +
    (choiceOccurrenceRemainingSteps truth index formula + 3)

/-- Skip both dimension prefixes and process one complete formula copy. -/
def choiceOccurrence_batchRun (truth : Bool)
    (index width variableCount : Nat) (formula : CNF)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan false)
        buffer₁ buffer₂ test
        (choiceOccurrenceBatchInput width variableCount formula ++ tail)
        output work₁ work₂ (index + 1) 0 0)
      (some (choiceOccurrenceCfg truth (.scan false)
        (some .batchEnd) buffer₂
        (if formula.isEmpty then test else false) tail
        (.itemEnd :: (choiceOccurrenceDigits formula index truth).reverse ++
          output)
        work₁ work₂ (index + 2) 0 0))
      (choiceOccurrenceBatchSteps truth index width variableCount formula) := by
  let afterWidthBuffer :=
    if width = 0 then buffer₁ else some ChoiceBatchSym.widthTick
  let afterVariableBuffer :=
    if variableCount = 0 then afterWidthBuffer
    else some ChoiceBatchSym.variableTick
  have widthRun := choiceOccurrence_skipDimensionRun truth true width
    (index + 1)
    (List.replicate variableCount .variableTick ++
      choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
    work₁ work₂ output buffer₁ buffer₂ test
  have variableRun := choiceOccurrence_skipDimensionRun truth false variableCount
    (index + 1) (choiceOccurrenceFormulaInput formula ++ .batchEnd :: tail)
    work₁ work₂ output afterWidthBuffer buffer₂ test
  have formulaRun := choiceOccurrence_formulaRun truth index formula
    tail work₁ work₂ output afterVariableBuffer buffer₂ test
  let first := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
    width variableCount _ _ _ (by
      simpa [choiceOccurrenceBatchInput, choiceOccurrenceDimensionSym,
        afterWidthBuffer, List.append_assoc] using widthRun)
    (by
      simpa [choiceOccurrenceDimensionSym, afterWidthBuffer,
        afterVariableBuffer] using variableRun)
  let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
    (variableCount + width)
    (choiceOccurrenceRemainingSteps truth index formula + 3)
    _ _ _ first formulaRun
  simpa [choiceOccurrenceBatchInput, choiceOccurrenceBatchSteps,
    List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

/-- Semantic stream for a consecutive range of variable indices. -/
def choiceOccurrenceStreamFrom (formula : CNF) (truth : Bool)
    (start count : Nat) : List ChoiceCountSym :=
  (List.range' start count).flatMap fun index =>
    choiceOccurrenceDigits formula index truth ++ [.itemEnd]

/-- Repeated explicit runtime batches. -/
def choiceOccurrenceBatchFamilyInput (width variableCount count : Nat)
    (formula : CNF) : List ChoiceBatchSym :=
  (List.replicate count
    (choiceOccurrenceBatchInput width variableCount formula)).flatten

/-- Sum of consecutive batch costs. -/
def choiceOccurrenceBatchFamilySteps (truth : Bool)
    (start count width variableCount : Nat) (formula : CNF) : Nat :=
  (List.range' start count).map (fun index =>
    choiceOccurrenceBatchSteps truth index width variableCount formula) |>.sum

private def choiceOccurrenceFamilyBuffer (count : Nat)
    (initial : Option ChoiceBatchSym) : Option ChoiceBatchSym :=
  if count = 0 then initial else some .batchEnd

private def choiceOccurrenceFamilyTest (formula : CNF) (count : Nat)
    (initial : Bool) : Bool :=
  if count = 0 then initial else if formula.isEmpty then initial else false

/-- Iterate the batch theorem over a consecutive variable range. -/
def choiceOccurrence_batchFamilyRun (truth : Bool)
    (start count width variableCount : Nat) (formula : CNF)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan false)
        buffer₁ buffer₂ test
        (choiceOccurrenceBatchFamilyInput width variableCount count formula ++
          tail)
        output work₁ work₂ (start + 1) 0 0)
      (some (choiceOccurrenceCfg truth (.scan false)
        (choiceOccurrenceFamilyBuffer count buffer₁) buffer₂
        (choiceOccurrenceFamilyTest formula count test) tail
        ((choiceOccurrenceStreamFrom formula truth start count).reverse ++
          output)
        work₁ work₂ (start + count + 1) 0 0))
      (choiceOccurrenceBatchFamilySteps truth start count width variableCount
        formula) := by
  induction count generalizing start output buffer₁ test with
  | zero =>
      exact ⟨⟨0, by
        simp [choiceOccurrenceBatchFamilyInput,
          choiceOccurrenceStreamFrom,
          choiceOccurrenceFamilyBuffer, choiceOccurrenceFamilyTest,
          choiceOccurrenceCfg]⟩, le_rfl⟩
  | succ count ih =>
      let payload := choiceOccurrenceBatchInput width variableCount formula
      let segment := choiceOccurrenceDigits formula start truth ++ [.itemEnd]
      have first := choiceOccurrence_batchRun truth start width variableCount
        formula
        (choiceOccurrenceBatchFamilyInput width variableCount count formula ++
          tail)
        work₁ work₂ output buffer₁ buffer₂ test
      have rest := ih (start := start + 1)
        (output := segment.reverse ++ output)
        (buffer₁ := some .batchEnd)
        (test := if formula.isEmpty then test else false)
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceBatchSteps truth start width variableCount formula)
        (choiceOccurrenceBatchFamilySteps truth (start + 1) count width
          variableCount formula)
        _ _ _ (by
          simpa [choiceOccurrenceBatchFamilyInput, payload,
            segment, List.reverse_append, List.replicate_succ,
            List.append_assoc, Nat.add_assoc] using first) rest
      simpa [choiceOccurrenceBatchFamilyInput,
        choiceOccurrenceBatchFamilySteps, choiceOccurrenceStreamFrom,
        choiceOccurrenceFamilyBuffer, choiceOccurrenceFamilyTest,
        segment, List.range'_succ, List.reverse_append,
        List.replicate_succ,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.SubsetSumReduction
