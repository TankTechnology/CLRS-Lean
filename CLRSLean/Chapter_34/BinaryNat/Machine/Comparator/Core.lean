import CLRSLean.Chapter_34.BinaryNat.Length
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Fixed binary comparator: controller and word semantics

The controller reverses both big-endian words onto work stacks and compares
from least to most significant bit. A more significant difference replaces
the accumulated answer; equal bits preserve it. Missing high bits are zero,
so the algorithm also handles leading zeroes and unequal word lengths.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.BinaryNat.Comparator

open PolyBuilder

/-- Update the comparison after seeing one more-significant bit pair. -/
def leCell (left right previous : Bool) : Bool :=
  if left == right then previous else !left && right

/-- Compare little-endian words, with `previous` recording the comparison of
the already-consumed less-significant prefixes. -/
def compareLittle : List Bool → List Bool → Bool → Bool
  | [], [], previous => previous
  | left :: lefts, [], previous =>
      compareLittle lefts [] (leCell left false previous)
  | [], right :: rights, previous =>
      compareLittle [] rights (leCell false right previous)
  | left :: lefts, right :: rights, previous =>
      compareLittle lefts rights (leCell left right previous)

/-- Total numeric comparison on arbitrary big-endian bit words. -/
def leWords (left right : List Bool) : Bool :=
  compareLittle left.reverse right.reverse true

inductive Label
  | loadLeft
  | storeLeft (bit : Bool)
  | loadRight
  | storeRight (bit : Bool)
  | compareLeft (result : Bool)
  | compareRight (result : Bool) (left : Option Bool)
  | finish (result : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Fixed two-work-stack binary comparison controller. -/
def program : Program (Option Bool) Bool where
  Label := Label
  main := .loadLeft
  op
    | .loadLeft => .popInput (.finish true) fun
        | none => .loadRight
        | some bit => .storeLeft bit
    | .storeLeft bit => .pushWork₁ (some bit) .loadLeft
    | .loadRight => .popInput (.compareLeft true) fun
        | none => .loadRight
        | some bit => .storeRight bit
    | .storeRight bit => .pushWork₂ (some bit) .loadRight
    | .compareLeft result => .popWork₁ (.compareRight result none) fun
        | none => .compareRight result none
        | some bit => .compareRight result (some bit)
    | .compareRight result left => .popWork₂
        (match left with
          | none => .finish result
          | some leftBit =>
              .compareLeft (leCell leftBit false result))
        fun
          | none =>
              match left with
              | none => .finish result
              | some leftBit =>
                  .compareLeft (leCell leftBit false result)
          | some rightBit =>
              .compareLeft (leCell (left.getD false) rightBit result)
    | .finish result => .pushOutput result .halt
    | .halt => .halt

/-- Uniform proof-facing controller configuration. -/
def cfg (label : Label) (buffer₁ buffer₂ : Option (Option Bool))
    (input : List (Option Bool)) (output : List Bool)
    (work₁ work₂ : List (Option Bool)) : BuilderCfg program :=
  { initialCfg program input with
      label := some label
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      output := output
      work₁ := work₁
      work₂ := work₂ }

end CLRS.Chapter34.Turing.BinaryNat.Comparator
