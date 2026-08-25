import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceCore
import Mathlib.Tactic

/-!
# Choice occurrence counter: reversible unary comparison

This file verifies the hard local step of the choice-item controller.  A
literal's unary variable code is compared with the current positive batch
index, the index counter is restored exactly, the following boundary is put
back on the input, and the clause counter changes precisely on a full match.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

/-- Consume a prefix for which both unary codes remain nonempty. -/
private def choiceOccurrence_comparePairsRun (truth polarity : Bool)
    (count remaining saved clauseCount : Nat)
    (boundary : ChoiceBatchSym) (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.compare polarity false)
        buffer₁ buffer₂ test
        (List.replicate count (.formula .endMark) ++ boundary :: tail)
        output work₁ work₂ (remaining + count) clauseCount saved)
      (some (choiceOccurrenceCfg truth (.compare polarity false)
        (if count = 0 then buffer₁ else some (.formula .endMark))
        buffer₂ (if count = 0 then test else true)
        (boundary :: tail) output work₁ work₂ remaining clauseCount
        (count + saved)))
      (3 * count) := by
  induction count generalizing buffer₁ test remaining saved with
  | zero => exact ⟨⟨0, by simp [choiceOccurrenceCfg]⟩, le_rfl⟩
  | succ count ih =>
      let after := choiceOccurrenceCfg truth (.compare polarity false)
        (some (.formula .endMark)) buffer₂ true
        (List.replicate count (.formula .endMark) ++ boundary :: tail)
        output work₁ work₂ (remaining + count) clauseCount (saved + 1)
      have first : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.compare polarity false)
            buffer₁ buffer₂ test
            (List.replicate (count + 1) (.formula .endMark) ++
              boundary :: tail)
            output work₁ work₂ (remaining + (count + 1)) clauseCount saved)
          (some after) 3 := by
        rw [show remaining + (count + 1) = (remaining + count) + 1 by omega]
        exact ⟨⟨3, by
          simp [Function.iterate_succ_apply, flip, after,
            List.replicate_succ, step, choiceOccurrenceProgram,
            choiceOccurrenceCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some (.formula .endMark))
        (test := true) (remaining := remaining) (saved := saved + 1)
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        3 (3 * count) _ after _ first rest
      convert full using 1
      all_goals simp [Nat.add_comm, Nat.add_left_comm] <;> omega

/-- In the too-long branch, consume all remaining code cells and stop after
the following non-code boundary has been popped. -/
private def choiceOccurrence_overflowRun (truth polarity : Bool)
    (excess indexCode clauseCount : Nat)
    (boundary : ChoiceBatchSym)
    (hboundary : boundary ≠ .formula .endMark)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.compare polarity true)
        buffer₁ buffer₂ test
        (List.replicate excess (.formula .endMark) ++ boundary :: tail)
        output work₁ work₂ 0 clauseCount indexCode)
      (some (choiceOccurrenceCfg truth
        (.saveBoundary polarity true boundary)
        (some boundary) buffer₂ test tail output work₁ work₂
        0 clauseCount indexCode))
      (excess + 1) := by
  induction excess generalizing buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, choiceOccurrenceProgram, choiceOccurrenceCfg,
          stepOp, hboundary]⟩, le_rfl⟩
  | succ excess ih =>
      let after := choiceOccurrenceCfg truth (.compare polarity true)
        (some (.formula .endMark)) buffer₂ test
        (List.replicate excess (.formula .endMark) ++ boundary :: tail)
        output work₁ work₂ 0 clauseCount indexCode
      have first : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.compare polarity true)
            buffer₁ buffer₂ test
            (List.replicate (excess + 1) (.formula .endMark) ++
              boundary :: tail)
            output work₁ work₂ 0 clauseCount indexCode)
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [after, List.replicate_succ, flip, step,
            choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (buffer₁ := some (.formula .endMark))
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        1 (excess + 1) _ after _ first rest
      simpa [Nat.add_assoc] using full

/-- Restore the saved suffix of the current positive index into counter one.
The `accumulated` parameter is essential in the short-code branch, where one
unmatched part of the index is still present before restoration begins. -/
private def choiceOccurrence_restoreRun (truth shouldCount : Bool)
    (saved accumulated clauseCount : Nat)
    (boundary : ChoiceBatchSym) (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.restoreIndex shouldCount)
        buffer₁ buffer₂ test tail output
        (boundary :: work₁) work₂ accumulated clauseCount saved)
      (some (choiceOccurrenceCfg truth
        (if shouldCount then .incrementCount else .restoreBoundary)
        buffer₁ buffer₂ false tail output
        (boundary :: work₁) work₂ (accumulated + saved) clauseCount 0))
      (2 * saved + 1) := by
  induction saved generalizing accumulated buffer₁ test with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, choiceOccurrenceProgram, choiceOccurrenceCfg,
          stepOp]⟩, le_rfl⟩
  | succ saved ih =>
      let after := choiceOccurrenceCfg truth
        (.restoreIndex shouldCount) buffer₁ buffer₂ true tail output
        (boundary :: work₁) work₂ (accumulated + 1) clauseCount saved
      have first : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.restoreIndex shouldCount)
            buffer₁ buffer₂ test tail output (boundary :: work₁) work₂
            accumulated clauseCount (saved + 1))
          (some after) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, after, step,
            choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (accumulated := accumulated + 1)
        (buffer₁ := buffer₁) (test := true)
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        2 (2 * saved + 1) _ after _ first rest
      convert full using 1
      all_goals simp [Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Finish a restored comparison by optionally incrementing the clause count
and putting the saved boundary back on the input. -/
private def choiceOccurrence_finishComparisonRun (truth matched : Bool)
    (indexCode clauseCount : Nat)
    (boundary : ChoiceBatchSym) (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth
        (if matched then .incrementCount else .restoreBoundary)
        buffer₁ buffer₂ false tail output (boundary :: work₁) work₂
        indexCode clauseCount 0)
      (some (choiceOccurrenceCfg truth (.scan true)
        (some boundary) buffer₂ false (boundary :: tail) output
        work₁ work₂ indexCode (clauseCount + if matched then 1 else 0) 0))
      (if matched then 2 else 1) := by
  cases matched <;>
    exact ⟨⟨_, by
      simp [Function.iterate_succ_apply, flip, step,
        choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
        List.replicate_succ]⟩, le_rfl⟩

/-- Uniform linear budget for one reversible unary literal comparison. -/
def choiceOccurrenceComparisonSteps
    (indexCode literalCode : Nat) : Nat :=
  8 * (indexCode + literalCode + 1)

private def evalsToInTime_weaken {state : Type}
    {transition : state → Option state} {start : state}
    {finish : Option state} {small large : Nat}
    (run : EvalsToInTime transition start finish small)
    (hbound : small ≤ large) :
    EvalsToInTime transition start finish large :=
  ⟨run.toEvalsTo, run.steps_le_m.trans hbound⟩

/-- Total local comparison contract.  The advertised linear budget is uniform
across equal, short, and long literal codes. -/
def choiceOccurrence_literalComparisonRun (truth polarity : Bool)
    (indexCode literalCode clauseCount : Nat)
    (boundary : ChoiceBatchSym)
    (hboundary : boundary ≠ .formula .endMark)
    (tail work₁ work₂ : List ChoiceBatchSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool) :
    EvalsToInTime (step (choiceOccurrenceProgram truth))
      (choiceOccurrenceCfg truth (.compare polarity false)
        buffer₁ buffer₂ test
        (List.replicate literalCode (.formula .endMark) ++ boundary :: tail)
        output work₁ work₂ indexCode clauseCount 0)
      (some (choiceOccurrenceCfg truth (.scan true)
        (some boundary) buffer₂ false (boundary :: tail) output work₁ work₂
        indexCode
        (clauseCount + if polarity && decide (literalCode = indexCode)
          then 1 else 0) 0))
      (choiceOccurrenceComparisonSteps indexCode literalCode) := by
  by_cases hle : literalCode ≤ indexCode
  · let remaining := indexCode - literalCode
    have hindex : indexCode = remaining + literalCode := by
      dsimp [remaining]
      omega
    have pairs := choiceOccurrence_comparePairsRun truth polarity
      literalCode remaining 0 clauseCount boundary tail work₁ work₂
      output buffer₁ buffer₂ test
    by_cases heq : literalCode = indexCode
    · have hremaining0 : remaining = 0 := by
        dsimp [remaining]
        omega
      have save : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.compare polarity false)
            (if literalCode = 0 then buffer₁ else some (.formula .endMark))
            buffer₂ (if literalCode = 0 then test else true)
            (boundary :: tail) output work₁ work₂ 0 clauseCount literalCode)
          (some (choiceOccurrenceCfg truth (.restoreIndex polarity)
            (some boundary) buffer₂ false tail output (boundary :: work₁)
            work₂ 0 clauseCount literalCode)) 3 := by
        exact ⟨⟨3, by
          simp [Function.iterate_succ_apply, flip, step,
            choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
            hboundary]⟩, le_rfl⟩
      have restore := choiceOccurrence_restoreRun truth polarity literalCode 0
        clauseCount boundary tail work₁ work₂ output (some boundary)
        buffer₂ false
      have finish := choiceOccurrence_finishComparisonRun truth polarity
        literalCode clauseCount boundary tail work₁ work₂ output
        (some boundary) buffer₂
      let first := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (3 * literalCode) 3 _ _ _ (by
          simpa [heq, hremaining0] using pairs) save
      let second := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (3 + 3 * literalCode) (2 * literalCode + 1) _ _ _ first restore
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        ((2 * literalCode + 1) + (3 + 3 * literalCode))
        (if polarity then 2 else 1) _ _ _ second (by
          simpa only [Nat.zero_add] using finish)
      refine evalsToInTime_weaken (by simpa [heq] using full) ?_
      cases polarity <;>
        simp [choiceOccurrenceComparisonSteps, heq] <;> omega
    · have hshort : literalCode < indexCode := by omega
      have hremaining_ne : remaining ≠ 0 := by
        dsimp [remaining]
        omega
      have hremaining : remaining = (indexCode - literalCode - 1) + 1 := by
        dsimp [remaining]
        omega
      let savedCode := literalCode + 1
      have save : EvalsToInTime (step (choiceOccurrenceProgram truth))
          (choiceOccurrenceCfg truth (.compare polarity false)
            (if literalCode = 0 then buffer₁ else some (.formula .endMark))
            buffer₂ (if literalCode = 0 then test else true)
            (boundary :: tail) output work₁ work₂ remaining clauseCount
            literalCode)
          (some (choiceOccurrenceCfg truth (.restoreIndex false)
            (some boundary) buffer₂ true tail output (boundary :: work₁)
            work₂ (remaining - 1) clauseCount savedCode)) 4 := by
        exact ⟨⟨4, by
          simp [Function.iterate_succ_apply, flip, step,
            choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp,
            hboundary, hremaining, savedCode, List.replicate_succ]⟩,
          le_rfl⟩
      have hrestoreCode : (remaining - 1) + savedCode = indexCode := by
        dsimp [savedCode, remaining]
        omega
      have restore := choiceOccurrence_restoreRun truth false savedCode
        (remaining - 1) clauseCount boundary tail work₁ work₂ output
        (some boundary) buffer₂ true
      have finish := choiceOccurrence_finishComparisonRun truth false
        indexCode clauseCount boundary tail work₁ work₂ output
        (some boundary) buffer₂
      let first := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (3 * literalCode) 4 _ _ _ (by simpa [hindex] using pairs) save
      let second := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        (4 + 3 * literalCode) (2 * savedCode + 1) _ _ _ first (by
          simpa [hrestoreCode] using restore)
      let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
        ((2 * savedCode + 1) + (4 + 3 * literalCode)) 1
        _ _ _ second (by simpa [heq] using finish)
      refine evalsToInTime_weaken (by
        simpa [hindex, hremaining_ne] using full) ?_
      simp [choiceOccurrenceComparisonSteps, savedCode]
      omega
  · have hlong : indexCode < literalCode := by omega
    have hne : literalCode ≠ indexCode := by omega
    let excess := literalCode - indexCode - 1
    have hliteral : literalCode = indexCode + excess + 1 := by
      dsimp [excess]
      omega
    have hinput :
        List.replicate literalCode (.formula .endMark) ++ boundary :: tail =
          List.replicate indexCode (.formula .endMark) ++
            .formula .endMark ::
              (List.replicate excess (.formula .endMark) ++ boundary :: tail) := by
      rw [hliteral]
      rw [show indexCode + excess + 1 = indexCode + (excess + 1) by omega]
      rw [List.replicate_add, List.replicate_succ]
      simp only [List.cons_append, List.append_assoc]
    have pairs := choiceOccurrence_comparePairsRun truth polarity
      indexCode 0 0 clauseCount (.formula .endMark)
      (List.replicate excess (.formula .endMark) ++ boundary :: tail)
      work₁ work₂ output buffer₁ buffer₂ test
    have enter : EvalsToInTime (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceCfg truth (.compare polarity false)
          (if indexCode = 0 then buffer₁ else some (.formula .endMark))
          buffer₂ (if indexCode = 0 then test else true)
          (.formula .endMark ::
            (List.replicate excess (.formula .endMark) ++ boundary :: tail))
          output work₁ work₂ 0 clauseCount indexCode)
        (some (choiceOccurrenceCfg truth (.compare polarity true)
          (some (.formula .endMark)) buffer₂ false
          (List.replicate excess (.formula .endMark) ++ boundary :: tail)
          output work₁ work₂ 0 clauseCount indexCode)) 2 := by
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, step,
          choiceOccurrenceProgram, choiceOccurrenceCfg, stepOp]⟩, le_rfl⟩
    have overflow := choiceOccurrence_overflowRun truth polarity excess
      indexCode clauseCount boundary hboundary tail work₁ work₂ output
      (some (.formula .endMark)) buffer₂ false
    have save : EvalsToInTime (step (choiceOccurrenceProgram truth))
        (choiceOccurrenceCfg truth (.saveBoundary polarity true boundary)
          (some boundary) buffer₂ false tail output work₁ work₂
          0 clauseCount indexCode)
        (some (choiceOccurrenceCfg truth (.restoreIndex false)
          (some boundary) buffer₂ false tail output (boundary :: work₁)
          work₂ 0 clauseCount indexCode)) 1 := by
      exact ⟨⟨1, rfl⟩, le_rfl⟩
    have restore := choiceOccurrence_restoreRun truth false indexCode 0
      clauseCount boundary tail work₁ work₂ output (some boundary)
      buffer₂ false
    have finish := choiceOccurrence_finishComparisonRun truth false
      indexCode clauseCount boundary tail work₁ work₂ output
      (some boundary) buffer₂
    let first := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
      (3 * indexCode) 2 _ _ _ (by simpa [hliteral, List.replicate_add,
        List.append_assoc] using pairs) enter
    let second := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
      (2 + 3 * indexCode) (excess + 1) _ _ _ first overflow
    let third := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
      ((excess + 1) + (2 + 3 * indexCode)) 1 _ _ _ second save
    let fourth := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
      (1 + ((excess + 1) + (2 + 3 * indexCode)))
      (2 * indexCode + 1) _ _ _ third restore
    let full := EvalsToInTime.trans (step (choiceOccurrenceProgram truth))
      ((2 * indexCode + 1) +
        (1 + ((excess + 1) + (2 + 3 * indexCode)))) 1
      _ _ _ fourth (by simpa using finish)
    refine evalsToInTime_weaken (by
      rw [hinput]
      simpa [hne] using full) ?_
    simp [choiceOccurrenceComparisonSteps]
    omega

end CLRS.Chapter34.Turing.SubsetSumReduction
