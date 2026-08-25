import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceCompare
import Mathlib.Tactic

/-!
# Choice occurrence counter: finite-digit dispatch

This file verifies that the unary clause counter is drained completely and
encoded as the intended finite digit.  The item-final branch additionally
emits its boundary and advances the positive variable index.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

private def choiceOccurrence_countOverflowRun (truth finishItem : Bool)
    (count indexCode : Nat)
    (input work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.countOverflow finishItem)
        buffer₁ buffer₂ test input output work₁ work₂
        indexCode count 0)
      (some (choiceOccurrenceCfg truth (.pushDigit .zero finishItem)
        buffer₁ buffer₂ false input output work₁ work₂
        indexCode 0 0))
      (count + 1) := by
  induction count generalizing test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, choiceOccurrenceProgram, choiceOccurrenceCfg,
          stepOp]⟩, le_rfl⟩
  | succ count ih =>
      let after := choiceOccurrenceCfg truth (.countOverflow finishItem)
        buffer₁ buffer₂ true input output work₁ work₂
        indexCode count 0
      have first : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.countOverflow finishItem)
            buffer₁ buffer₂ test input output work₁ work₂
            indexCode (count + 1) 0)
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [after, flip, step, choiceOccurrenceProgram,
            choiceOccurrenceCfg, stepOp, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (test := true)
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        1 (count + 1) _ after _ first rest
      simpa [Nat.add_assoc] using full

private def choiceOccurrence_pushDigitRun (truth finishItem : Bool)
    (digit : SmallDigit) (indexCode : Nat)
    (input work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.pushDigit digit finishItem)
        buffer₁ buffer₂ false input output work₁ work₂
        indexCode 0 0)
      (some (choiceOccurrenceCfg truth
        (if finishItem then .scan false else .scan true)
        buffer₁ buffer₂ false input
        (if finishItem then .itemEnd :: .digit digit :: output
         else .digit digit :: output)
        work₁ work₂ (indexCode + if finishItem then 1 else 0) 0 0))
      (if finishItem then 3 else 1) := by
  cases finishItem <;>
    exact ⟨⟨_, by
      simp [Function.iterate_succ_apply, flip, step,
        choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
        List.replicate_succ]⟩, le_rfl⟩

/-- Uniform linear budget for draining and emitting one clause count. -/
def choiceOccurrenceDispatchSteps (count : Nat) : Nat :=
  2 * count + 5

/-- The counter dispatcher implements `occurrenceSmallDigit` on every natural
count.  Counts above three take the controller's total overflow-to-zero path;
the three-CNF theorem later proves that path unreachable on valid inputs. -/
def choiceOccurrence_dispatchRun (truth finishItem : Bool)
    (count indexCode : Nat)
    (input work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.dispatchCount finishItem)
        buffer₁ buffer₂ test input output work₁ work₂
        indexCode count 0)
      (some (choiceOccurrenceCfg truth
        (if finishItem then .scan false else .scan true)
        buffer₁ buffer₂ false input
        (if finishItem then
          .itemEnd :: .digit (occurrenceSmallDigit count) :: output
         else .digit (occurrenceSmallDigit count) :: output)
        work₁ work₂ (indexCode + if finishItem then 1 else 0) 0 0))
      (choiceOccurrenceDispatchSteps count) := by
  by_cases hsmall : count ≤ 3
  · cases hfinish : finishItem
    · interval_cases count
      · exact ⟨⟨2, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit]⟩, by simp [choiceOccurrenceDispatchSteps]⟩
      · exact ⟨⟨3, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit, List.replicate_succ]⟩, by
          simp [choiceOccurrenceDispatchSteps]⟩
      · exact ⟨⟨4, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit, List.replicate_succ]⟩, by
          simp [choiceOccurrenceDispatchSteps]⟩
      · exact ⟨⟨5, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit, List.replicate_succ]⟩, by
          simp [choiceOccurrenceDispatchSteps]⟩
    · interval_cases count
      · exact ⟨⟨4, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit, List.replicate_succ]⟩, by
          simp [choiceOccurrenceDispatchSteps]⟩
      · exact ⟨⟨5, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit, List.replicate_succ]⟩, by
          simp [choiceOccurrenceDispatchSteps]⟩
      · exact ⟨⟨6, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit, List.replicate_succ]⟩, by
          simp [choiceOccurrenceDispatchSteps]⟩
      · exact ⟨⟨7, by simp_all [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          occurrenceSmallDigit, List.replicate_succ]⟩, by
          simp [choiceOccurrenceDispatchSteps]⟩
  · let excess := count - 4
    have hcount : count = excess + 4 := by
      dsimp [excess]
      omega
    let after := choiceOccurrenceCfg truth (.countOverflow finishItem)
      buffer₁ buffer₂ true input output work₁ work₂
      indexCode excess 0
    have prefixRun : EvalsToInTime (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceCfg truth (.dispatchCount finishItem)
          buffer₁ buffer₂ test input output work₁ work₂
          indexCode count 0)
        (some after) 4 := by
      rw [hcount]
      exact ⟨⟨4, by
        simp [Function.iterate_succ_apply, after, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
    have overflow := choiceOccurrence_countOverflowRun truth finishItem
      excess indexCode input work₁ work₂ output buffer₁ buffer₂ true
    have push := choiceOccurrence_pushDigitRun truth finishItem .zero
      indexCode input work₁ work₂ output buffer₁ buffer₂
    let first := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
      4 (excess + 1) _ after _ prefixRun overflow
    let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
      ((excess + 1) + 4) (if finishItem then 3 else 1)
      _ _ _ first push
    have hdigit : occurrenceSmallDigit count = .zero := by
      rw [hcount]
      cases excess <;> rfl
    rw [hdigit]
    refine ⟨full.toEvalsTo, full.steps_le_m.trans ?_⟩
    cases finishItem <;>
      simp [choiceOccurrenceDispatchSteps, hcount] <;> omega

end CLRS.Chapter34.Turing.SubsetSumReduction
