import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceOccurrenceOutput
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Choice digits: variable-prefix and occurrence merge

Each choice item needs a one-hot variable prefix before its clause-occurrence
digits.  The controller below keeps one persistent unary variable template,
uses the item ordinal as a unary counter, and copies the already verified
occurrence stream behind the generated prefix.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Tagged input for the prefix/occurrence merger. -/
inductive ChoiceDigitMergeSym
  | variableTick | separator
  | count (symbol : ChoiceCountSym)
deriving DecidableEq, Fintype, Repr

/-- One-hot variable digits for one choice item. -/
def choiceVariableDigits (formula : CNF) (index : Nat) :
    List ChoiceCountSym :=
  (List.range (reductionVariableCount formula)).map fun column =>
    .digit (if column = index then .one else .zero)

/-- Complete digit stream before fixed-width block expansion. -/
def choiceDigitStream (formula : CNF) (truth : Bool) :
    List ChoiceCountSym :=
  (List.range (reductionVariableCount formula)).flatMap fun index =>
    choiceVariableDigits formula index ++
      choiceOccurrenceDigits formula index truth ++ [.itemEnd]

/-- Finite control for merging one-hot prefixes with occurrence rows. -/
inductive ChoiceDigitMergeLabel
  | loadTemplate
  | saveTemplate
  | nextItem
  | prefixMoveBefore (first : ChoiceCountSym)
  | prefixCheck (first : ChoiceCountSym)
  | prefixSaveZero (first : ChoiceCountSym)
  | prefixPushZero (first : ChoiceCountSym)
  | prefixPushOne (first : ChoiceCountSym)
  | prefixMoveAfter (first : ChoiceCountSym)
  | prefixPushAfterZero (first : ChoiceCountSym)
  | restoreIndex (first : ChoiceCountSym)
  | restoreIndexInc (first : ChoiceCountSym)
  | incrementIndex (first : ChoiceCountSym)
  | restoreTemplate (first : ChoiceCountSym)
  | emitFirst (first : ChoiceCountSym)
  | copyOccurrence
  | pushOccurrence (digit : SmallDigit)
  | pushOccurrenceEnd
  | clearIndex | clearTemplate | halt | invalid
deriving DecidableEq, Fintype

/-- Fixed controller.  Counter one is the current zero-based item ordinal;
counter three restores it after the one-hot scan. -/
def choiceDigitMergeProgram :
    Program ChoiceDigitMergeSym ChoiceCountSym where
  Label := ChoiceDigitMergeLabel
  main := .loadTemplate
  op
    | .loadTemplate => .popInput .invalid fun
        | .variableTick => .saveTemplate
        | .separator => .nextItem
        | .count _ => .invalid
    | .saveTemplate => .pushWork₁ .variableTick .loadTemplate
    | .nextItem => .popInput .clearIndex fun
        | .count first => .prefixMoveBefore first
        | _ => .invalid
    | .prefixMoveBefore first =>
        .moveWork₁Work₂ .invalid fun
          | .variableTick => .prefixCheck first
          | _ => .invalid
    | .prefixCheck first =>
        .dec₁ (.prefixPushOne first) (.prefixSaveZero first)
    | .prefixSaveZero first => .inc₃ (.prefixPushZero first)
    | .prefixPushZero first =>
        .pushOutput (.digit .zero) (.prefixMoveBefore first)
    | .prefixPushOne first =>
        .pushOutput (.digit .one) (.prefixMoveAfter first)
    | .prefixMoveAfter first =>
        .moveWork₁Work₂ (.restoreIndex first) fun
          | .variableTick => .prefixPushAfterZero first
          | _ => .invalid
    | .prefixPushAfterZero first =>
        .pushOutput (.digit .zero) (.prefixMoveAfter first)
    | .restoreIndex first =>
        .dec₃ (.incrementIndex first) (.restoreIndexInc first)
    | .restoreIndexInc first => .inc₁ (.restoreIndex first)
    | .incrementIndex first => .inc₁ (.restoreTemplate first)
    | .restoreTemplate first =>
        .moveWork₂Work₁ (.emitFirst first) fun
          | .variableTick => .restoreTemplate first
          | _ => .invalid
    | .emitFirst (.digit digit) =>
        .pushOutput (.digit digit) .copyOccurrence
    | .emitFirst .itemEnd => .pushOutput .itemEnd .nextItem
    | .copyOccurrence => .popInput .invalid fun
        | .count (.digit digit) => .pushOccurrence digit
        | .count .itemEnd => .pushOccurrenceEnd
        | _ => .invalid
    | .pushOccurrence digit =>
        .pushOutput (.digit digit) .copyOccurrence
    | .pushOccurrenceEnd => .pushOutput .itemEnd .nextItem
    | .clearIndex => .dec₁ .clearTemplate .clearIndex
    | .clearTemplate => .popWork₁ .halt fun _ => .clearTemplate
    | .halt => .halt
    | .invalid => .halt

/-- Proof-facing merger configuration. -/
def choiceDigitMergeCfg (label : ChoiceDigitMergeLabel)
    (buffer₁ buffer₂ : Option ChoiceDigitMergeSym) (test : Bool)
    (input : List ChoiceDigitMergeSym) (output : List ChoiceCountSym)
    (work₁ work₂ : List ChoiceDigitMergeSym)
    (index saved : Nat) : BuilderCfg choiceDigitMergeProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := List.replicate index ()
  counter₂ := []
  counter₃ := List.replicate saved ()

end CLRS.Chapter34.Turing.SubsetSumReduction
