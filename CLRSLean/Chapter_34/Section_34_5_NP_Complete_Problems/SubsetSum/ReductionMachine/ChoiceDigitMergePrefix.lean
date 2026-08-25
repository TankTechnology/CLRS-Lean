import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceDigitMergeSource
import Mathlib.Tactic

/-!
# Choice digits: one-hot prefix simulation

This file proves the local controller phases that generate one zero-based
one-hot row and restore both the row ordinal and the persistent width template.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

private def zeroDigit : ChoiceCountSym := .digit .zero

@[simp] private theorem replicate_append_self_cons {α : Type}
    (value : α) (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: List.replicate count value ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ] using congrArg (List.cons value) ih

private def prefixBeforeSteps : Nat → Nat
  | 0 => 3
  | count + 1 => prefixBeforeSteps count + 4

private def prefixAfterSteps : Nat → Nat
  | 0 => 1
  | count + 1 => prefixAfterSteps count + 2

private def restoreIndexSteps : Nat → Nat
  | 0 => 2
  | count + 1 => restoreIndexSteps count + 2

private def restoreTemplateSteps : Nat → Nat
  | 0 => 1
  | count + 1 => restoreTemplateSteps count + 1

/-- Exact controller cost for producing one one-hot prefix and restoring the
persistent variable template. -/
def choiceDigitMergePrefixSteps (before after : Nat) : Nat :=
  restoreTemplateSteps (before + 1 + after) +
    (restoreIndexSteps before +
      (prefixAfterSteps after + prefixBeforeSteps before))

private theorem prefixBeforeSteps_eq (count : Nat) :
    prefixBeforeSteps count = 4 * count + 3 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prefixBeforeSteps, ih]
      omega

private theorem prefixAfterSteps_eq (count : Nat) :
    prefixAfterSteps count = 2 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prefixAfterSteps, ih]
      omega

private theorem restoreIndexSteps_eq (count : Nat) :
    restoreIndexSteps count = 2 * count + 2 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [restoreIndexSteps, ih]
      omega

private theorem restoreTemplateSteps_eq (count : Nat) :
    restoreTemplateSteps count = count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [restoreTemplateSteps, ih]

/-- Closed form used by the polynomial runtime audit. -/
theorem choiceDigitMergePrefixSteps_eq (before after : Nat) :
    choiceDigitMergePrefixSteps before after =
      7 * before + 3 * after + 8 := by
  simp [choiceDigitMergePrefixSteps, prefixBeforeSteps_eq,
    prefixAfterSteps_eq, restoreIndexSteps_eq,
    restoreTemplateSteps_eq]
  omega

private def choiceDigitMerge_prefixBefore_run
    (first : ChoiceCountSym) (before after saved : Nat)
    (tail work₂ : List ChoiceDigitMergeSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg (.prefixMoveBefore first)
        buffer₁ buffer₂ test tail output
        (List.replicate before .variableTick ++
          .variableTick :: List.replicate after .variableTick)
        work₂ before saved)
      (some (choiceDigitMergeCfg (.prefixMoveAfter first)
        (some .variableTick) buffer₂ false tail
        (.digit .one :: List.replicate before zeroDigit ++ output)
        (List.replicate after .variableTick)
        (List.replicate (before + 1) .variableTick ++ work₂)
        0 (saved + before)))
      (prefixBeforeSteps before) := by
  induction before generalizing saved work₂ output buffer₁ test with
  | zero =>
      exact ⟨⟨3, by
        simp [Function.iterate_succ_apply, flip, step,
          choiceDigitMergeProgram, choiceDigitMergeCfg, stepOp,
          zeroDigit]⟩, by
            change 3 ≤ 3
            exact le_rfl⟩
  | succ before ih =>
      let afterFirst := choiceDigitMergeCfg (.prefixMoveBefore first)
        (some .variableTick) buffer₂ true tail
        (zeroDigit :: output)
        (List.replicate before .variableTick ++
          .variableTick :: List.replicate after .variableTick)
        (.variableTick :: work₂) before (saved + 1)
      have firstRun : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg (.prefixMoveBefore first)
            buffer₁ buffer₂ test tail output
            (List.replicate (before + 1) .variableTick ++
              .variableTick :: List.replicate after .variableTick)
            work₂ (before + 1) saved)
          (some afterFirst) 4 := by
        exact ⟨⟨4, by
          simp [Function.iterate_succ_apply, flip, step,
            choiceDigitMergeProgram, choiceDigitMergeCfg, stepOp,
            afterFirst, zeroDigit, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1)
        (work₂ := .variableTick :: work₂)
        (output := zeroDigit :: output)
        (buffer₁ := some .variableTick) (test := true)
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        4 (prefixBeforeSteps before) _ afterFirst _ firstRun rest
      have hsaved : saved + (before + 1) = saved + 1 + before := by omega
      convert full using 1 <;>
        simp [zeroDigit, List.replicate_succ, prefixBeforeSteps, hsaved]

private def choiceDigitMerge_prefixAfter_run
    (first : ChoiceCountSym) (count : Nat)
    (tail work₂ : List ChoiceDigitMergeSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool)
    (saved : Nat) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg (.prefixMoveAfter first)
        buffer₁ buffer₂ test tail output
        (List.replicate count .variableTick) work₂ 0 saved)
      (some (choiceDigitMergeCfg (.restoreIndex first)
        none buffer₂ test tail
        (List.replicate count zeroDigit ++ output)
        [] (List.replicate count .variableTick ++ work₂) 0 saved))
      (prefixAfterSteps count) := by
  induction count generalizing work₂ output buffer₁ with
  | zero =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | succ count ih =>
      let afterFirst := choiceDigitMergeCfg (.prefixMoveAfter first)
        (some .variableTick) buffer₂ test tail (zeroDigit :: output)
        (List.replicate count .variableTick)
        (.variableTick :: work₂) 0 saved
      have firstRun : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg (.prefixMoveAfter first)
            buffer₁ buffer₂ test tail output
            (List.replicate (count + 1) .variableTick) work₂ 0 saved)
          (some afterFirst) 2 := by
        exact ⟨⟨2, by simp [Function.iterate_succ_apply, flip,
          choiceDigitMergeProgram, choiceDigitMergeCfg, step, stepOp,
          afterFirst, List.replicate_succ, zeroDigit]⟩, le_rfl⟩
      have rest := ih (work₂ := .variableTick :: work₂)
        (output := zeroDigit :: output)
        (buffer₁ := some .variableTick)
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        2 (prefixAfterSteps count) _ afterFirst _ firstRun rest
      simpa [afterFirst, List.replicate_succ, zeroDigit,
        prefixAfterSteps] using full

private def choiceDigitMerge_restoreIndex_run
    (first : ChoiceCountSym) (count index : Nat)
    (tail work₁ work₂ : List ChoiceDigitMergeSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg (.restoreIndex first)
        buffer₁ buffer₂ test tail output work₁ work₂ index count)
      (some (choiceDigitMergeCfg (.restoreTemplate first)
        buffer₁ buffer₂ false tail output work₁ work₂
        (index + count + 1) 0))
      (restoreIndexSteps count) := by
  induction count generalizing index test with
  | zero =>
      exact ⟨⟨2, by simp [Function.iterate_succ_apply, flip,
        choiceDigitMergeProgram, choiceDigitMergeCfg, step, stepOp,
        List.replicate_succ]⟩,
        le_rfl⟩
  | succ count ih =>
      let afterFirst := choiceDigitMergeCfg (.restoreIndex first)
        buffer₁ buffer₂ true tail output work₁ work₂ (index + 1) count
      have firstRun : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg (.restoreIndex first)
            buffer₁ buffer₂ test tail output work₁ work₂ index (count + 1))
          (some afterFirst) 2 := by
        exact ⟨⟨2, by simp [Function.iterate_succ_apply, flip,
          choiceDigitMergeProgram, choiceDigitMergeCfg, step, stepOp,
          afterFirst, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (index := index + 1) (test := true)
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        2 (restoreIndexSteps count) _ afterFirst _ firstRun (by
          simpa [afterFirst] using rest)
      simpa [afterFirst, restoreIndexSteps, List.replicate_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def choiceDigitMerge_restoreTemplate_run
    (first : ChoiceCountSym) (count : Nat)
    (tail work₁ : List ChoiceDigitMergeSym) (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool)
    (index : Nat) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg (.restoreTemplate first)
        buffer₁ buffer₂ test tail output work₁
        (List.replicate count .variableTick) index 0)
      (some (choiceDigitMergeCfg (.emitFirst first)
        buffer₁ none test tail output
        (List.replicate count .variableTick ++ work₁) [] index 0))
      (restoreTemplateSteps count) := by
  induction count generalizing work₁ buffer₂ with
  | zero =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | succ count ih =>
      let afterFirst := choiceDigitMergeCfg (.restoreTemplate first)
        buffer₁ (some .variableTick) test tail output
        (.variableTick :: work₁)
        (List.replicate count .variableTick) index 0
      have firstRun : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg (.restoreTemplate first)
            buffer₁ buffer₂ test tail output work₁
            (List.replicate (count + 1) .variableTick) index 0)
          (some afterFirst) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have rest := ih (work₁ := .variableTick :: work₁)
        (buffer₂ := some .variableTick)
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        1 (restoreTemplateSteps count) _ afterFirst _ firstRun (by
          simpa [afterFirst] using rest)
      simpa [afterFirst, List.replicate_succ,
        restoreTemplateSteps] using full

/-- One complete prefix restores the persistent template and advances the
zero-based item ordinal. -/
def choiceDigitMerge_prefix_run
    (first : ChoiceCountSym) (before after : Nat)
    (tail : List ChoiceDigitMergeSym) (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg (.prefixMoveBefore first)
        buffer₁ buffer₂ test tail output
        (List.replicate before .variableTick ++
          .variableTick :: List.replicate after .variableTick)
        [] before 0)
      (some (choiceDigitMergeCfg (.emitFirst first)
        none none false tail
        ((List.replicate before zeroDigit ++ [ChoiceCountSym.digit .one] ++
          List.replicate after zeroDigit).reverse ++ output)
        (List.replicate (before + 1 + after) .variableTick)
        [] (before + 1) 0))
      (choiceDigitMergePrefixSteps before after) := by
  have firstRun := choiceDigitMerge_prefixBefore_run first before after 0
    tail [] output buffer₁ buffer₂ test
  have afterRun := choiceDigitMerge_prefixAfter_run first after tail
    (List.replicate (before + 1) .variableTick)
    (.digit .one :: List.replicate before zeroDigit ++ output)
    (some .variableTick) buffer₂ false before
  have restoreIndex := choiceDigitMerge_restoreIndex_run first before 0 tail []
    (List.replicate (before + (after + 1)) .variableTick)
    (List.replicate after zeroDigit ++
      (.digit .one :: List.replicate before zeroDigit ++ output))
    none buffer₂ false
  have restoreTemplate := choiceDigitMerge_restoreTemplate_run first
    (before + (after + 1)) tail []
    (List.replicate after zeroDigit ++
      (.digit .one :: List.replicate before zeroDigit ++ output))
    none buffer₂ false (before + 1)
  let throughAfter := EvalsToInTime.trans (step choiceDigitMergeProgram)
    (prefixBeforeSteps before) (prefixAfterSteps after) _ _ _ firstRun (by
      simpa [zeroDigit, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using afterRun)
  let throughIndex := EvalsToInTime.trans (step choiceDigitMergeProgram)
    (prefixAfterSteps after + prefixBeforeSteps before)
    (restoreIndexSteps before)
    _ _ _ throughAfter restoreIndex
  let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
    (restoreIndexSteps before +
      (prefixAfterSteps after + prefixBeforeSteps before))
    (restoreTemplateSteps (before + (after + 1))) _ _ _ throughIndex
    (by simpa only [Nat.zero_add] using restoreTemplate)
  convert full using 1 <;>
    simp [choiceDigitMergePrefixSteps, zeroDigit, List.reverse_append,
      List.append_assoc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

end CLRS.Chapter34.Turing.SubsetSumReduction
