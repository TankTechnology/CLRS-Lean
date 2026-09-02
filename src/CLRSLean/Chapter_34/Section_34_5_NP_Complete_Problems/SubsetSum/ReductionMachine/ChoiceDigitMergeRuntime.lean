import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceDigitMergePrefix
import Mathlib.Tactic

/-!
# Choice digits: canonical merger runtime

This file lifts the local one-hot-prefix simulation to the complete canonical
occurrence stream.  The fixed controller loads one persistent variable-width
template, processes every choice item, clears its unary state, and halts with
the merged digit stream in reverse output order.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Exact cost of loading the persistent unary variable template and its
separator. -/
def choiceDigitMergeLoadSteps (count : Nat) : Nat := 2 * count + 1

private def choiceDigitMerge_loadTemplate_run
    (count : Nat) (tail work₁ work₂ : List ChoiceDigitMergeSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool)
    (index saved : Nat) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .loadTemplate buffer₁ buffer₂ test
        (List.replicate count .variableTick ++ .separator :: tail)
        output work₁ work₂ index saved)
      (some (choiceDigitMergeCfg .nextItem (some .separator) buffer₂ test
        tail output (List.replicate count .variableTick ++ work₁) work₂
        index saved))
      (choiceDigitMergeLoadSteps count) := by
  induction count generalizing work₁ buffer₁ with
  | zero =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | succ count ih =>
      let afterFirst := choiceDigitMergeCfg .loadTemplate
        (some .variableTick) buffer₂ test
        (List.replicate count .variableTick ++ .separator :: tail)
        output (.variableTick :: work₁) work₂ index saved
      have firstRun : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg .loadTemplate buffer₁ buffer₂ test
            (List.replicate (count + 1) .variableTick ++ .separator :: tail)
            output work₁ work₂ index saved)
          (some afterFirst) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, step,
            choiceDigitMergeProgram, choiceDigitMergeCfg, stepOp,
            afterFirst, List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (work₁ := .variableTick :: work₁)
        (buffer₁ := some .variableTick)
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        2 (choiceDigitMergeLoadSteps count) _ afterFirst _ firstRun rest
      simpa [afterFirst, choiceDigitMergeLoadSteps, List.replicate_succ,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Cost of copying the remaining clause digits and their item boundary. -/
def choiceDigitMergeCopySteps (formula : CNF) : Nat :=
  2 * (formula.length + 1)

private def choiceDigitMerge_copyOccurrence_run
    (formula : CNF) (index : Nat) (truth : Bool)
    (tail work₁ work₂ : List ChoiceDigitMergeSym)
    (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool)
    (ordinal saved : Nat) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .copyOccurrence buffer₁ buffer₂ test
        (((choiceOccurrenceDigits formula index truth ++
          [ChoiceCountSym.itemEnd]).map
          .count) ++ tail)
        output work₁ work₂ ordinal saved)
      (some (choiceDigitMergeCfg .nextItem (some (.count .itemEnd)) buffer₂
        test tail
        ((choiceOccurrenceDigits formula index truth ++
          [ChoiceCountSym.itemEnd]).reverse ++
          output)
        work₁ work₂ ordinal saved))
      (choiceDigitMergeCopySteps formula) := by
  induction formula generalizing output buffer₁ with
  | nil =>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, step,
          choiceDigitMergeProgram, choiceDigitMergeCfg, stepOp,
          choiceOccurrenceDigits]⟩, le_rfl⟩
  | cons clause formula ih =>
      let digit := ChoiceCountSym.digit
        (occurrenceSmallDigit (clause.count (itemLiteral index truth)))
      let afterFirst := choiceDigitMergeCfg .copyOccurrence
        (some (.count digit)) buffer₂ test
        (((choiceOccurrenceDigits formula index truth ++
          [ChoiceCountSym.itemEnd]).map
          .count) ++ tail)
        (digit :: output) work₁ work₂ ordinal saved
      have firstRun : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg .copyOccurrence buffer₁ buffer₂ test
            (((choiceOccurrenceDigits (clause :: formula) index truth ++
              [ChoiceCountSym.itemEnd]).map .count) ++ tail)
            output work₁ work₂ ordinal saved)
          (some afterFirst) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, step,
            choiceDigitMergeProgram, choiceDigitMergeCfg, stepOp,
            choiceOccurrenceDigits, digit, afterFirst]⟩, le_rfl⟩
      have rest := ih (output := digit :: output)
        (buffer₁ := some (.count digit))
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        2 (choiceDigitMergeCopySteps formula) _ afterFirst _ firstRun rest
      convert full using 1 <;> simp [afterFirst, digit, choiceOccurrenceDigits,
        choiceDigitMergeCopySteps, List.reverse_cons,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] <;> omega

/-- Exact cost of merging one choice row once the persistent template has
already been loaded. -/
def choiceDigitMergeItemSteps (before after : Nat) (formula : CNF) : Nat :=
  choiceDigitMergePrefixSteps before after + 2 + 2 * formula.length

def choiceDigitMergeItemBuffer (formula : CNF) :
    Option ChoiceDigitMergeSym :=
  if formula.isEmpty then none else some (.count .itemEnd)

/-- Process one semantic occurrence row, prefix it with the one-hot variable
digits, and leave the restored template ready for the next row. -/
def choiceDigitMerge_itemRun
    (before after : Nat) (formula : CNF) (truth : Bool)
    (tail : List ChoiceDigitMergeSym) (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .nextItem buffer₁ buffer₂ test
        (((choiceOccurrenceDigits formula before truth ++
          [ChoiceCountSym.itemEnd]).map .count) ++ tail)
        output
        (List.replicate before .variableTick ++
          .variableTick :: List.replicate after .variableTick)
        [] before 0)
      (some (choiceDigitMergeCfg .nextItem
        (choiceDigitMergeItemBuffer formula) none false tail
        ((List.replicate before (ChoiceCountSym.digit .zero) ++
            ChoiceCountSym.digit .one ::
              List.replicate after (ChoiceCountSym.digit .zero) ++
              choiceOccurrenceDigits formula before truth ++
                [ChoiceCountSym.itemEnd]).reverse ++ output)
        (List.replicate (before + 1 + after) .variableTick)
        [] (before + 1) 0))
      (choiceDigitMergeItemSteps before after formula) := by
  cases formula with
  | nil =>
      have popFirst : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg .nextItem buffer₁ buffer₂ test
            ([.count ChoiceCountSym.itemEnd] ++ tail) output
            (List.replicate before .variableTick ++
              .variableTick :: List.replicate after .variableTick)
            [] before 0)
          (some (choiceDigitMergeCfg (.prefixMoveBefore .itemEnd)
            (some (.count .itemEnd)) buffer₂ test tail output
            (List.replicate before .variableTick ++
              .variableTick :: List.replicate after .variableTick)
            [] before 0)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have prefixRun := choiceDigitMerge_prefix_run ChoiceCountSym.itemEnd
        before after tail output (some (.count .itemEnd)) buffer₂ test
      have emit : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg (.emitFirst .itemEnd) none none false tail
            ((List.replicate before (ChoiceCountSym.digit .zero) ++
              [ChoiceCountSym.digit .one] ++
              List.replicate after (ChoiceCountSym.digit .zero)).reverse ++ output)
            (List.replicate (before + 1 + after) .variableTick)
            [] (before + 1) 0)
          (some (choiceDigitMergeCfg .nextItem
            none none false tail
            (.itemEnd ::
              (List.replicate before (ChoiceCountSym.digit .zero) ++
                [ChoiceCountSym.digit .one] ++
                List.replicate after (ChoiceCountSym.digit .zero)).reverse ++ output)
            (List.replicate (before + 1 + after) .variableTick)
            [] (before + 1) 0)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      let throughPrefix := EvalsToInTime.trans (step choiceDigitMergeProgram)
        1 (choiceDigitMergePrefixSteps before after) _ _ _ popFirst prefixRun
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        (choiceDigitMergePrefixSteps before after + 1) 1 _ _ _
        throughPrefix emit
      convert full using 1 <;> simp [choiceOccurrenceDigits,
        choiceDigitMergeItemSteps,
        choiceDigitMergeItemBuffer,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] <;> omega
  | cons clause formula =>
      let digit := ChoiceCountSym.digit
        (occurrenceSmallDigit (clause.count (itemLiteral before truth)))
      let remaining :=
        ((choiceOccurrenceDigits formula before truth ++
          [ChoiceCountSym.itemEnd]).map ChoiceDigitMergeSym.count) ++ tail
      have popFirst : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg .nextItem buffer₁ buffer₂ test
            (.count digit :: remaining) output
            (List.replicate before .variableTick ++
              .variableTick :: List.replicate after .variableTick)
            [] before 0)
          (some (choiceDigitMergeCfg (.prefixMoveBefore digit)
            (some (.count digit)) buffer₂ test remaining output
            (List.replicate before .variableTick ++
              .variableTick :: List.replicate after .variableTick)
            [] before 0)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have prefixRun := choiceDigitMerge_prefix_run digit before after remaining
        output (some (.count digit)) buffer₂ test
      have emit : EvalsToInTime (step choiceDigitMergeProgram)
          (choiceDigitMergeCfg (.emitFirst digit) none none false remaining
            ((List.replicate before (ChoiceCountSym.digit .zero) ++
              [ChoiceCountSym.digit .one] ++
              List.replicate after (ChoiceCountSym.digit .zero)).reverse ++ output)
            (List.replicate (before + 1 + after) .variableTick)
            [] (before + 1) 0)
          (some (choiceDigitMergeCfg .copyOccurrence none none false
            remaining
            (digit ::
              (List.replicate before (ChoiceCountSym.digit .zero) ++
                [ChoiceCountSym.digit .one] ++
                List.replicate after (ChoiceCountSym.digit .zero)).reverse ++ output)
            (List.replicate (before + 1 + after) .variableTick)
            [] (before + 1) 0)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have copy := choiceDigitMerge_copyOccurrence_run formula before truth
        tail (List.replicate (before + 1 + after) .variableTick) []
        (digit ::
          (List.replicate before (ChoiceCountSym.digit .zero) ++
            [ChoiceCountSym.digit .one] ++
            List.replicate after (ChoiceCountSym.digit .zero)).reverse ++ output)
        none none false (before + 1) 0
      let throughPrefix := EvalsToInTime.trans (step choiceDigitMergeProgram)
        1 (choiceDigitMergePrefixSteps before after) _ _ _ popFirst prefixRun
      let throughEmit := EvalsToInTime.trans (step choiceDigitMergeProgram)
        (choiceDigitMergePrefixSteps before after + 1) 1 _ _ _
        throughPrefix emit
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        (1 + (choiceDigitMergePrefixSteps before after + 1))
        (choiceDigitMergeCopySteps formula) _ _ _ throughEmit copy
      convert full using 1 <;> simp [remaining, digit, choiceOccurrenceDigits,
        choiceDigitMergeItemBuffer,
        choiceDigitMergeItemSteps, choiceDigitMergeCopySteps,
        List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Canonical tagged occurrence rows for a consecutive index range. -/
def choiceDigitMergeRowsFrom (formula : CNF) (truth : Bool) :
    Nat → Nat → List ChoiceDigitMergeSym
  | _, 0 => []
  | start, count + 1 =>
      (choiceOccurrenceDigits formula start truth ++
        [ChoiceCountSym.itemEnd]).map .count ++
        choiceDigitMergeRowsFrom formula truth (start + 1) count

/-- Merged semantic rows for the same consecutive index range. -/
def choiceDigitStreamFrom (formula : CNF) (truth : Bool) :
    Nat → Nat → List ChoiceCountSym
  | _, 0 => []
  | start, count + 1 =>
      choiceVariableDigits formula start ++
        choiceOccurrenceDigits formula start truth ++
          [ChoiceCountSym.itemEnd] ++
            choiceDigitStreamFrom formula truth (start + 1) count

/-- Sum of the exact per-row merger costs. -/
def choiceDigitMergeFamilySteps (formula : CNF) : Nat → Nat → Nat
  | _, 0 => 0
  | start, count + 1 =>
      choiceDigitMergeItemSteps start count formula +
        choiceDigitMergeFamilySteps formula (start + 1) count

private def choiceDigitMergeFamilyBuffer (formula : CNF) (count : Nat)
    (initial : Option ChoiceDigitMergeSym) : Option ChoiceDigitMergeSym :=
  if count = 0 then initial else choiceDigitMergeItemBuffer formula

private def choiceDigitMergeFamilyBuffer₂ (count : Nat)
    (initial : Option ChoiceDigitMergeSym) : Option ChoiceDigitMergeSym :=
  if count = 0 then initial else none

private def choiceDigitMergeFamilyTest (count : Nat) (initial : Bool) : Bool :=
  if count = 0 then initial else false

/-- Iterate the one-row theorem over a consecutive family. -/
def choiceDigitMerge_familyRun
    (formula : CNF) (truth : Bool) (start count : Nat)
    (htotal : reductionVariableCount formula = start + count)
    (tail : List ChoiceDigitMergeSym) (output : List ChoiceCountSym)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .nextItem buffer₁ buffer₂ test
        (choiceDigitMergeRowsFrom formula truth start count ++ tail)
        output (List.replicate (start + count) .variableTick) [] start 0)
      (some (choiceDigitMergeCfg .nextItem
        (choiceDigitMergeFamilyBuffer formula count buffer₁)
        (choiceDigitMergeFamilyBuffer₂ count buffer₂)
        (choiceDigitMergeFamilyTest count test) tail
        ((choiceDigitStreamFrom formula truth start count).reverse ++ output)
        (List.replicate (start + count) .variableTick) []
        (start + count) 0))
      (choiceDigitMergeFamilySteps formula start count) := by
  induction count generalizing start output buffer₁ buffer₂ test with
  | zero =>
      exact ⟨⟨0, by
        simp [choiceDigitMergeRowsFrom, choiceDigitStreamFrom,
          choiceDigitMergeFamilySteps, choiceDigitMergeFamilyBuffer,
          choiceDigitMergeFamilyBuffer₂, choiceDigitMergeFamilyTest,
          choiceDigitMergeCfg]⟩, le_rfl⟩
  | succ count ih =>
      have hafter : reductionVariableCount formula - start - 1 = count := by
        omega
      have hafter' : count + (start + 1) - start - 1 = count := by
        omega
      have htemplate : count + (start + 1) = (count + start) + 1 := by
        omega
      have hwork :
          List.replicate (count + (start + 1))
              ChoiceDigitMergeSym.variableTick =
            ChoiceDigitMergeSym.variableTick ::
              List.replicate (count + start) .variableTick := by
        rw [htemplate, List.replicate_succ]
      let segment := choiceVariableDigits formula start ++
        choiceOccurrenceDigits formula start truth ++
          [ChoiceCountSym.itemEnd]
      have first := choiceDigitMerge_itemRun start count formula truth
        (choiceDigitMergeRowsFrom formula truth (start + 1) count ++ tail)
        output buffer₁ buffer₂ test
      have rest := ih (start := start + 1) (by omega)
        (output := segment.reverse ++ output)
        (buffer₁ := choiceDigitMergeItemBuffer formula)
        (buffer₂ := none) (test := false)
      let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
        (choiceDigitMergeItemSteps start count formula)
        (choiceDigitMergeFamilySteps formula (start + 1) count)
        _ _ _ (by
          simpa [choiceDigitMergeRowsFrom, choiceVariableDigits,
            htotal, hafter, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first)
        (by
          simpa [segment, choiceVariableDigits, htotal, hafter, hafter',
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest)
      simpa [segment, choiceDigitMergeRowsFrom, choiceDigitStreamFrom,
        choiceVariableDigits, htotal, hafter, hafter', hwork,
        choiceDigitMergeFamilySteps, choiceDigitMergeFamilyBuffer,
        choiceDigitMergeFamilyBuffer₂, choiceDigitMergeFamilyTest,
        List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private theorem choiceDigitMergeRowsFrom_eq (formula : CNF) (truth : Bool)
    (start count : Nat) :
    choiceDigitMergeRowsFrom formula truth start count =
      (List.range' start count).flatMap fun index =>
        (choiceOccurrenceDigits formula index truth ++
          [ChoiceCountSym.itemEnd]).map .count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [choiceDigitMergeRowsFrom, List.range'_succ,
        List.flatMap_cons]
      rw [ih]

@[simp] theorem choiceDigitMergeRowsFrom_zero (formula : CNF)
    (truth : Bool) :
    choiceDigitMergeRowsFrom formula truth 0
        (reductionVariableCount formula) =
      (choiceOccurrenceStream formula truth).map .count := by
  rw [choiceDigitMergeRowsFrom_eq, choiceOccurrenceStream,
    List.range_eq_range']
  simp only [List.map_flatMap]

private theorem choiceDigitStreamFrom_eq (formula : CNF) (truth : Bool)
    (start count : Nat) :
    choiceDigitStreamFrom formula truth start count =
      (List.range' start count).flatMap fun index =>
        choiceVariableDigits formula index ++
          choiceOccurrenceDigits formula index truth ++
            [ChoiceCountSym.itemEnd] := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [choiceDigitStreamFrom, List.range'_succ,
        List.flatMap_cons]
      rw [ih]

@[simp] theorem choiceDigitStreamFrom_zero (formula : CNF) (truth : Bool) :
    choiceDigitStreamFrom formula truth 0
        (reductionVariableCount formula) =
      choiceDigitStream formula truth := by
  rw [choiceDigitStreamFrom_eq, choiceDigitStream,
    List.range_eq_range']

private theorem choiceDigitMerge_clearIndex_eval (count : Nat)
    (buffer₁ : Option ChoiceDigitMergeSym) (test : Bool)
    (output : List ChoiceCountSym) (work₁ : List ChoiceDigitMergeSym) :
    (flip Option.bind (step choiceDigitMergeProgram))^[count + 1]
      (some (choiceDigitMergeCfg .clearIndex buffer₁ none test
        [] output work₁ [] count 0)) =
      some (choiceDigitMergeCfg .clearTemplate buffer₁ none false
        [] output work₁ [] 0 0) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step choiceDigitMergeProgram))^[count + 1]
          (some (choiceDigitMergeCfg .clearIndex buffer₁ none true
            [] output work₁ [] count 0)) = _
      exact ih true

private theorem choiceDigitMerge_clearTemplate_eval
    (work₁ : List ChoiceDigitMergeSym) (buffer₁ : Option ChoiceDigitMergeSym)
    (output : List ChoiceCountSym) :
    (flip Option.bind (step choiceDigitMergeProgram))^[work₁.length + 1]
      (some (choiceDigitMergeCfg .clearTemplate buffer₁ none false
        [] output work₁ [] 0 0)) =
      some (choiceDigitMergeCfg .halt none none false
        [] output [] [] 0 0) := by
  induction work₁ generalizing buffer₁ with
  | nil => rfl
  | cons symbol work₁ ih =>
      rw [show (symbol :: work₁).length + 1 =
          (work₁.length + 1) + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step choiceDigitMergeProgram))^[work₁.length + 1]
          (some (choiceDigitMergeCfg .clearTemplate (some symbol) none false
            [] output work₁ [] 0 0)) = _
      exact ih (some symbol)

/-- Empty-input dispatch, unary-index cleanup, template cleanup, and the final
halt take exactly `2 * count + 4` steps. -/
def choiceDigitMerge_cleanupRun (count : Nat)
    (buffer₁ : Option ChoiceDigitMergeSym) (test : Bool)
    (output : List ChoiceCountSym) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .nextItem buffer₁ none test [] output
        (List.replicate count .variableTick) [] count 0)
      (some (haltCfg choiceDigitMergeProgram output))
      (2 * count + 4) := by
  have empty : EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .nextItem buffer₁ none test [] output
        (List.replicate count .variableTick) [] count 0)
      (some (choiceDigitMergeCfg .clearIndex none none test [] output
        (List.replicate count .variableTick) [] count 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have clearIndex : EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .clearIndex none none test [] output
        (List.replicate count .variableTick) [] count 0)
      (some (choiceDigitMergeCfg .clearTemplate none none false [] output
        (List.replicate count .variableTick) [] 0 0)) (count + 1) :=
    ⟨⟨count + 1, choiceDigitMerge_clearIndex_eval count none test
      output (List.replicate count .variableTick)⟩, le_rfl⟩
  have clearTemplate : EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .clearTemplate none none false [] output
        (List.replicate count .variableTick) [] 0 0)
      (some (choiceDigitMergeCfg .halt none none false
        [] output [] [] 0 0)) (count + 1) := by
    exact ⟨⟨count + 1, by
      simpa using choiceDigitMerge_clearTemplate_eval
        (List.replicate count ChoiceDigitMergeSym.variableTick) none output⟩,
      le_rfl⟩
  have halt : EvalsToInTime (step choiceDigitMergeProgram)
      (choiceDigitMergeCfg .halt none none false [] output [] [] 0 0)
      (some (haltCfg choiceDigitMergeProgram output)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let throughIndex := EvalsToInTime.trans (step choiceDigitMergeProgram)
    1 (count + 1) _ _ _ empty clearIndex
  let throughTemplate := EvalsToInTime.trans (step choiceDigitMergeProgram)
    (count + 2) (count + 1) _ _ _ throughIndex clearTemplate
  let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
    (count + 1 + (count + 2)) 1 _ _ _ throughTemplate halt
  refine ⟨full.toEvalsTo, full.steps_le_m.trans ?_⟩
  omega

/-- Exact cost of the canonical merger run after its source has produced the
tagged template-and-occurrence word. -/
def choiceDigitMergeCanonicalSteps (input : List CNFSym) : Nat :=
  let formula := decodeCNF input
  let count := reductionVariableCount formula
  choiceDigitMergeLoadSteps count +
    choiceDigitMergeFamilySteps formula 0 count +
      (2 * count + 4)

/-- The fixed merger consumes its canonical source and halts with precisely
the reversed semantic choice-digit stream. -/
def choiceDigitMergeCanonical_run (truth : Bool) (input : List CNFSym) :
    EvalsToInTime (step choiceDigitMergeProgram)
      (initialCfg choiceDigitMergeProgram (choiceDigitMergeInput truth input))
      (some (haltCfg choiceDigitMergeProgram
        (choiceDigitStream (decodeCNF input) truth).reverse))
      (choiceDigitMergeCanonicalSteps input) := by
  let formula := decodeCNF input
  let count := reductionVariableCount formula
  have load := choiceDigitMerge_loadTemplate_run count
    (choiceDigitMergeRowsFrom formula truth 0 count) [] [] []
    none none false 0 0
  have family := choiceDigitMerge_familyRun formula truth 0 count
    (by simp [count]) [] [] (some .separator) none false
  have cleanup := choiceDigitMerge_cleanupRun count
    (choiceDigitMergeFamilyBuffer formula count (some .separator))
    (choiceDigitMergeFamilyTest count false)
    (choiceDigitStream formula truth).reverse
  let throughFamily := EvalsToInTime.trans (step choiceDigitMergeProgram)
    (choiceDigitMergeLoadSteps count)
    (choiceDigitMergeFamilySteps formula 0 count) _ _ _ (by
      simpa [choiceDigitMergeInput, choiceOccurrenceCounts, formula, count,
        initialCfg, choiceDigitMergeRowsFrom_zero,
        List.append_assoc] using load) (by
      simpa [choiceDigitStreamFrom_zero, count] using family)
  let full := EvalsToInTime.trans (step choiceDigitMergeProgram)
    (choiceDigitMergeFamilySteps formula 0 count +
      choiceDigitMergeLoadSteps count)
    (2 * count + 4) _ _ _ throughFamily (by
      simpa [choiceDigitMergeFamilyBuffer₂] using cleanup)
  simpa [choiceDigitMergeCanonicalSteps, choiceDigitMergeInput,
    choiceOccurrenceCounts, initialCfg, choiceDigitMergeCfg, formula, count,
    choiceDigitMergeProgram,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.SubsetSumReduction
