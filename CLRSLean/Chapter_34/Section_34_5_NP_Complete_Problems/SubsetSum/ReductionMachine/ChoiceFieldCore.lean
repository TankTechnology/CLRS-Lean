import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceBlockSemantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.BinaryCanonicalizer
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ItemFields
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Choice fields: fixed segment formatter

This controller reverses each little-endian item segment on a work tape,
canonicalizes the resulting big-endian bits, and adds the public numeric-field
delimiters.  It is independent of the input formula and block width.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

inductive ChoiceFieldLabel
  | scan
  | saveBit (bit : Bool)
  | startField
  | canon (started : Bool)
  | emitBit (bit : Bool)
  | emitZero
  | finishField
  | halt
  | invalid
deriving DecidableEq, Fintype

def choiceFieldProgram : Program ChoiceBlockSym SubsetSumSym where
  Label := ChoiceFieldLabel
  main := .scan
  op
    | .scan => .popInput .halt fun
        | .bit bit => .saveBit bit
        | .itemEnd => .startField
    | .saveBit bit => .pushWork₁ (.bit bit) .scan
    | .startField => .pushOutput .numberMark (.canon false)
    | .canon started => .popWork₁
        (if started then .finishField else .emitZero) fun
        | .bit bit =>
            if started then .emitBit bit
            else if bit then .emitBit true else .canon false
        | .itemEnd => .invalid
    | .emitBit bit => .pushOutput (.bit bit) (.canon true)
    | .emitZero => .pushOutput (.bit false) .finishField
    | .finishField => .pushOutput .fieldEnd .scan
    | .halt => .halt
    | .invalid => .halt

def choiceFieldCfg (label : ChoiceFieldLabel)
    (buffer₁ buffer₂ : Option ChoiceBlockSym) (test : Bool)
    (input : List ChoiceBlockSym) (output : List SubsetSumSym)
    (work₁ work₂ : List ChoiceBlockSym) : BuilderCfg choiceFieldProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

/-- Canonical public field generated from one little-endian fixed-width item. -/
def choiceBitField (bitsLE : List Bool) : List SubsetSumSym :=
  encodeCanonicalBitField (binaryCanonicalizer bitsLE.reverse)

/-- Delimiter-bearing input for a list of item bit payloads. -/
def choiceBlockItemsInput (items : List (List Bool)) :
    List ChoiceBlockSym :=
  items.flatMap fun bits => bits.map .bit ++ [.itemEnd]

/-- Public fields corresponding to the same list of payloads. -/
def choiceBitFields (items : List (List Bool)) : List SubsetSumSym :=
  items.flatMap choiceBitField

end CLRS.Chapter34.Turing.SubsetSumReduction
