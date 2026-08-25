import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceBatch
import Mathlib.Tactic

/-!
# Choice occurrence counter: canonical runtime

This file connects the local batch-family simulation to the actual batches
generated from a raw CNF word.  It also proves the final counter cleanup, so
the fixed builder reaches the fully cleared successful halt configuration.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- The explicit batch expected by the occurrence controller is exactly the
payload produced by the verified batch source. -/
theorem choiceOccurrenceBatchInput_eq_payload (input : List CNFSym) :
    choiceOccurrenceBatchInput
        (reductionBlockWidth (decodeCNF input))
        (reductionVariableCount (decodeCNF input))
        (decodeCNF input) =
      choiceBatchPayload input := by
  simp [choiceOccurrenceBatchInput, choiceBatchPayload,
    choiceOccurrenceFormulaInput, reductionBlockWidthTicks_eq,
    variableBudgetTicks_eq,
    TMClique.normalizeCNFInput_eq_encCNF_decodeCNF,
    List.append_assoc]

/-- The whole explicit batch family consumed by the controller is the output
of the already verified nested-loop batch generator. -/
theorem choiceOccurrenceBatchFamilyInput_eq_choiceBatches
    (input : List CNFSym) :
    choiceOccurrenceBatchFamilyInput
        (reductionBlockWidth (decodeCNF input))
        (reductionVariableCount (decodeCNF input))
        (reductionVariableCount (decodeCNF input))
        (decodeCNF input) =
      choiceBatches input := by
  rw [choiceBatches_eq]
  simp only [choiceOccurrenceBatchFamilyInput,
    choiceOccurrenceBatchInput_eq_payload]

@[simp] theorem choiceOccurrenceStreamFrom_zero (formula : CNF)
    (truth : Bool) :
    choiceOccurrenceStreamFrom formula truth 0
        (reductionVariableCount formula) =
      choiceOccurrenceStream formula truth := by
  rw [choiceOccurrenceStreamFrom, choiceOccurrenceStream,
    ← List.range_eq_range']

private theorem choiceOccurrence_clearIndex_eval (truth : Bool)
    (count : Nat) (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool)
    (output : List ChoiceCountSym) :
    (flip Option.bind (step (choiceOccurrenceProgram truth)))^[count + 1]
      (some (choiceOccurrenceCfg truth .clearIndex buffer₁ buffer₂ test
        [] output [] [] count 0 0)) =
      some (choiceOccurrenceCfg truth .halt buffer₁ buffer₂ false
        [] output [] [] 0 0 0) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (choiceOccurrenceProgram truth)))^[count + 1]
          (some (choiceOccurrenceCfg truth .clearIndex buffer₁ buffer₂ true
            [] output [] [] count 0 0)) = _
      exact ih true

/-- Empty-input dispatch, unary-index cleanup, and the final halt take exactly
`indexCode + 3` steps. -/
def choiceOccurrence_cleanupRun (truth : Bool) (indexCode : Nat)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool)
    (output : List ChoiceCountSym) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan false) buffer₁ buffer₂ test
        [] output [] [] indexCode 0 0)
      (some (haltCfg (choiceOccurrenceProgram truth) output))
      (indexCode + 3) := by
  have scanEmpty : EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.scan false) buffer₁ buffer₂ test
        [] output [] [] indexCode 0 0)
      (some (choiceOccurrenceCfg truth .clearIndex none buffer₂ test
        [] output [] [] indexCode 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have clearIndex : EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth .clearIndex none buffer₂ test
        [] output [] [] indexCode 0 0)
      (some (choiceOccurrenceCfg truth .halt none buffer₂ false
        [] output [] [] 0 0 0)) (indexCode + 1) :=
    ⟨⟨indexCode + 1,
      choiceOccurrence_clearIndex_eval truth indexCode none buffer₂ test
        output⟩, le_rfl⟩
  have halt : EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth .halt none buffer₂ false
        [] output [] [] 0 0 0)
      (some (haltCfg (choiceOccurrenceProgram truth) output)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let throughClear := EvalsToInTime.trans
    (step (choiceOccurrenceProgram truth)) 1 (indexCode + 1)
    _ _ _ scanEmpty clearIndex
  let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
    (indexCode + 2) 1 _ _ _ throughClear halt
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact cost of the canonical occurrence-count run on a raw CNF word after
the batch source has produced its output. -/
def choiceOccurrenceCanonicalSteps (truth : Bool)
    (input : List CNFSym) : Nat :=
  let formula := decodeCNF input
  let count := reductionVariableCount formula
  1 + choiceOccurrenceBatchFamilySteps truth 0 count
      (reductionBlockWidth formula) count formula + (count + 4)

/-- A fixed occurrence controller consumes the canonical batch source and
halts with the exact reversed semantic occurrence stream. -/
def choiceOccurrenceCanonical_run (truth : Bool) (input : List CNFSym) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (initialCfg (choiceOccurrenceProgram truth) (choiceBatches input))
      (some (haltCfg (choiceOccurrenceProgram truth)
        (choiceOccurrenceStream (decodeCNF input) truth).reverse))
      (choiceOccurrenceCanonicalSteps truth input) := by
  let formula := decodeCNF input
  let count := reductionVariableCount formula
  let width := reductionBlockWidth formula
  have initRun : EvalsToInTime (step (choiceOccurrenceProgram truth))
      (initialCfg (choiceOccurrenceProgram truth) (choiceBatches input))
      (some (choiceOccurrenceCfg truth (.scan false) none none false
        (choiceBatches input) [] [] [] 1 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have batches := choiceOccurrence_batchFamilyRun truth
    0 count width count formula [] [] [] [] none none false
  have cleanup := choiceOccurrence_cleanupRun truth (count + 1)
    (if count = 0 then none else some .batchEnd) none
    (if count = 0 then false else if formula.isEmpty then false else false)
    (choiceOccurrenceStream formula truth).reverse
  let throughBatches := EvalsToInTime.trans
    (step (choiceOccurrenceProgram truth)) 1
    (choiceOccurrenceBatchFamilySteps truth 0 count width count formula)
    _ _ _ initRun (by
      simpa [formula, count, width,
        choiceOccurrenceBatchFamilyInput_eq_choiceBatches,
        choiceOccurrenceFamilyBuffer, choiceOccurrenceFamilyTest,
        choiceOccurrenceStreamFrom_zero, Nat.zero_add] using batches)
  let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
    (choiceOccurrenceBatchFamilySteps truth 0 count width count formula + 1)
    (count + 4) _ _ _ throughBatches (by
      simpa [choiceOccurrenceFamilyBuffer, choiceOccurrenceFamilyTest]
        using cleanup)
  simpa [choiceOccurrenceCanonicalSteps, formula, count, width,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.SubsetSumReduction
