import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Choice-item occurrence counter: semantic target and core controller

The batched source repeats the canonical formula once per variable.  This
controller keeps the batch ordinal as a unary counter, compares it with every
literal's unary variable code, and emits one finite occurrence digit per
clause plus an item boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

inductive ChoiceCountSym
  | digit (value : SmallDigit)
  | itemEnd
deriving DecidableEq, Fintype, Repr

/-- Clause digits for one choice item. -/
def choiceOccurrenceDigits (formula : CNF) (index : Nat)
    (truth : Bool) : List ChoiceCountSym :=
  formula.map fun clause =>
    .digit (occurrenceSmallDigit (clause.count (itemLiteral index truth)))

/-- Complete count stream for one truth family. -/
def choiceOccurrenceStream (formula : CNF) (truth : Bool) :
    List ChoiceCountSym :=
  (List.range (reductionVariableCount formula)).flatMap fun index =>
    choiceOccurrenceDigits formula index truth ++ [.itemEnd]

inductive ChoiceOccurrenceLabel
  | initIndex
  | scan (startedClause : Bool)
  | expectVariable (polarityMatches : Bool)
  | compare (polarityMatches overflow : Bool)
  | compareDec (polarityMatches : Bool)
  | saveBoundary (polarityMatches overflow : Bool)
      (boundary : ChoiceBatchSym)
  | checkRemaining (polarityMatches : Bool)
  | saveShort (polarityMatches : Bool)
  | saveRemaining
  | restoreIndex (shouldCount : Bool)
  | restoreIncrement (shouldCount : Bool)
  | incrementCount
  | restoreBoundary
  | dispatchCount (finishItem : Bool)
  | countOne (finishItem : Bool)
  | countTwo (finishItem : Bool)
  | countThree (finishItem : Bool)
  | countOverflow (finishItem : Bool)
  | pushDigit (digit : SmallDigit) (finishItem : Bool)
  | pushItemEnd
  | advanceIndex
  | clearIndex | halt | invalid
deriving DecidableEq, Fintype

/-- Fixed controller for one polarity family.  Counter one is the positive
unary variable code `index + 1`, counter two is the current clause count, and
counter three restores counter one after a literal comparison. -/
def choiceOccurrenceProgram (truth : Bool) :
    Program ChoiceBatchSym ChoiceCountSym where
  Label := ChoiceOccurrenceLabel
  main := .initIndex
  op
    | .initIndex => .inc₁ (.scan false)
    | .scan started => .popInput .clearIndex fun
        | .widthTick | .variableTick => .scan started
        | .formula .clauseMark =>
            if started then .dispatchCount false else .scan true
        | .formula .posMark => .expectVariable truth
        | .formula .negMark => .expectVariable (!truth)
        | .batchEnd =>
            if started then .dispatchCount true else .pushItemEnd
        | _ => .invalid
    | .expectVariable polarityMatches => .popInput .invalid fun
        | .formula .varMark => .compare polarityMatches false
        | _ => .invalid
    | .compare polarityMatches overflow => .popInput .invalid fun symbol =>
        if symbol = .formula .endMark then
          if overflow then .compare polarityMatches true
          else .compareDec polarityMatches
        else .saveBoundary polarityMatches overflow symbol
    | .compareDec polarityMatches =>
        .dec₁ (.compare polarityMatches true) (.saveShort polarityMatches)
    | .saveShort polarityMatches =>
        .inc₃ (.compare polarityMatches false)
    | .saveBoundary polarityMatches overflow boundary =>
        .pushWork₁ boundary
          (if overflow then .restoreIndex false
           else .checkRemaining polarityMatches)
    | .checkRemaining polarityMatches =>
        .dec₁ (.restoreIndex polarityMatches) .saveRemaining
    | .saveRemaining => .inc₃ (.restoreIndex false)
    | .restoreIndex shouldCount =>
        .dec₃
          (if shouldCount then .incrementCount else .restoreBoundary)
          (.restoreIncrement shouldCount)
    | .restoreIncrement shouldCount => .inc₁ (.restoreIndex shouldCount)
    | .incrementCount => .inc₂ .restoreBoundary
    | .restoreBoundary => .moveWork₁Input .invalid (fun _ => .scan true)
    | .dispatchCount finishItem =>
        .dec₂ (.pushDigit .zero finishItem) (.countOne finishItem)
    | .countOne finishItem =>
        .dec₂ (.pushDigit .one finishItem) (.countTwo finishItem)
    | .countTwo finishItem =>
        .dec₂ (.pushDigit .two finishItem) (.countThree finishItem)
    | .countThree finishItem =>
        .dec₂ (.pushDigit .three finishItem) (.countOverflow finishItem)
    | .countOverflow finishItem =>
        .dec₂ (.pushDigit .zero finishItem) (.countOverflow finishItem)
    | .pushDigit digit finishItem =>
        .pushOutput (.digit digit)
          (if finishItem then .pushItemEnd else .scan true)
    | .pushItemEnd => .pushOutput .itemEnd .advanceIndex
    | .advanceIndex => .inc₁ (.scan false)
    | .clearIndex => .dec₁ .halt .clearIndex
    | .halt => .halt
    | .invalid => .halt

/-- Proof-facing configuration. -/
def choiceOccurrenceCfg (truth : Bool) (label : ChoiceOccurrenceLabel)
    (buffer₁ buffer₂ : Option ChoiceBatchSym) (test : Bool)
    (input : List ChoiceBatchSym) (output : List ChoiceCountSym)
    (work₁ work₂ : List ChoiceBatchSym)
    (indexCode clauseCount saved : Nat) :
    BuilderCfg (choiceOccurrenceProgram truth) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := List.replicate indexCode ()
  counter₂ := List.replicate clauseCount ()
  counter₃ := List.replicate saved ()

end CLRS.Chapter34.Turing.SubsetSumReduction
