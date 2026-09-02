import CLRSLean.Chapter_34.BinaryNat.Machine.Adder.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# Summing a stream of delimited binary words

The input consists of big-endian Boolean words separated by absence symbols.
The controller first reverses the whole stream.  It then adds each now
little-endian field to an accumulator, using the verified binary full-adder
cell, and finally emits one big-endian sum word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum

open StateTransition

/-- Finish one binary addition after the current field has ended.  `work` is
the already produced big-endian prefix, represented in stack order. -/
def finishAdd : List Bool → Bool → List Bool → List Bool
  | [], false, work => work
  | [], true, work => true :: work
  | accumulatorBit :: accumulator, carry, work =>
      let cell := BinaryNat.Adder.addCell false accumulatorBit carry
      finishAdd accumulator cell.2 (cell.1 :: work)

/-- Total semantics from a reversed delimited stream and an internal
little-endian accumulator. -/
def sumReversed : List (Option Bool) → List Bool → Bool →
    List Bool → List Bool
  | [], accumulator, carry, work => finishAdd accumulator carry work
  | none :: rest, accumulator, carry, work =>
      let next := finishAdd accumulator carry work
      sumReversed rest next.reverse false []
  | some fieldBit :: rest, [], carry, work =>
      let cell := BinaryNat.Adder.addCell fieldBit false carry
      sumReversed rest [] cell.2 (cell.1 :: work)
  | some fieldBit :: rest, accumulatorBit :: accumulator, carry, work =>
      let cell := BinaryNat.Adder.addCell fieldBit accumulatorBit carry
      sumReversed rest accumulator cell.2 (cell.1 :: work)

/-- Word-level semantics of the total delimited sum controller. -/
def sumDelimited (input : List (Option Bool)) : List Bool :=
  sumReversed input.reverse [] false []

inductive Label
  | load
  | store (field : Option Bool)
  | add (carry : Bool)
  | readAccumulator (carry fieldBit : Bool)
  | save (carry bit : Bool)
  | finish (carry final : Bool)
  | saveFinish (final carry bit : Bool)
  | saveCarry (final : Bool)
  | restore (final : Bool)
  | emit
  | emitBit (bit : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Fixed stack controller for summing arbitrarily many compact binary words. -/
def program : Program (Option Bool) Bool where
  Label := Label
  main := .load
  op
    | .load => .popInput (.add false) .store
    | .store field => .pushWork₂ field .load
    | .add carry => .popWork₂ (.finish carry true) fun
        | none => .finish carry false
        | some bit => .readAccumulator carry bit
    | .readAccumulator carry fieldBit =>
        .popInput
          (let cell := BinaryNat.Adder.addCell fieldBit false carry
           .save cell.2 cell.1)
          fun
            | none =>
                let cell := BinaryNat.Adder.addCell fieldBit false carry
                .save cell.2 cell.1
            | some accumulatorBit =>
                let cell := BinaryNat.Adder.addCell fieldBit accumulatorBit carry
                .save cell.2 cell.1
    | .save carry bit => .pushWork₁ (some bit) (.add carry)
    | .finish carry final =>
        .popInput
          (if carry then .saveCarry final else .restore final)
          fun
            | none => .finish carry final
            | some accumulatorBit =>
                let cell := BinaryNat.Adder.addCell false accumulatorBit carry
                .saveFinish final cell.2 cell.1
    | .saveFinish final carry bit =>
        .pushWork₁ (some bit) (.finish carry final)
    | .saveCarry final => .pushWork₁ (some true) (.restore final)
    | .restore final =>
        .moveWork₁Input (if final then .emit else .add false) fun _ =>
          .restore final
    | .emit => .popInput .halt fun
        | none => .emit
        | some bit => .emitBit bit
    | .emitBit bit => .pushOutput bit .emit
    | .halt => .halt

def cfg (label : Label) (buffer₁ buffer₂ : Option (Option Bool))
    (test : Bool) (input : List (Option Bool)) (output : List Bool)
    (work₁ work₂ : List (Option Bool)) : BuilderCfg program where
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

end CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum
