import CLRSLean.Chapter_34.BinaryNat.Length
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Fixed binary adder: controller and word semantics

The public codec is big-endian.  The controller first reverses the two input
words onto separate work stacks, so the addition phase sees least-significant
bits first.  Each produced bit is prepended to the output stack; consequently
the final result is big-endian again.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.BinaryNat.Adder

open PolyBuilder

/-- One full-adder cell, returning `(sum bit, carry bit)`. -/
def addCell (left right carry : Bool) : Bool × Bool :=
  let parity := left != right
  (parity != carry, (left && right) || (carry && parity))

/-- Add two little-endian bit lists and return a big-endian word.

The recursive result contains the more significant suffix.  Appending the
current sum bit therefore agrees with the prepend-only output stack used by
the concrete controller. -/
def addLittle : List Bool → List Bool → Bool → List Bool
  | [], [], false => []
  | [], [], true => [true]
  | left :: lefts, [], carry =>
      let cell := addCell left false carry
      addLittle lefts [] cell.2 ++ [cell.1]
  | [], right :: rights, carry =>
      let cell := addCell false right carry
      addLittle [] rights cell.2 ++ [cell.1]
  | left :: lefts, right :: rights, carry =>
      let cell := addCell left right carry
      addLittle lefts rights cell.2 ++ [cell.1]

/-- Total word-level semantics of the fixed adder. -/
def addWords (left right : List Bool) : List Bool :=
  addLittle left.reverse right.reverse false

inductive Label
  | loadLeft
  | storeLeft (bit : Bool)
  | loadRight
  | storeRight (bit : Bool)
  | addLeft (carry : Bool)
  | addRight (carry : Bool) (left : Option Bool)
  | emit (carry bit : Bool)
  | finish (carry : Bool)
  | halt
deriving DecidableEq, Fintype

/-- Fixed two-work-stack binary addition controller. -/
def program : Program (Option Bool) Bool where
  Label := Label
  main := .loadLeft
  op
    | .loadLeft => .popInput (.finish false) fun
        | none => .loadRight
        | some bit => .storeLeft bit
    | .storeLeft bit => .pushWork₁ (some bit) .loadLeft
    | .loadRight => .popInput (.addLeft false) fun
        | none => .loadRight
        | some bit => .storeRight bit
    | .storeRight bit => .pushWork₂ (some bit) .loadRight
    | .addLeft carry => .popWork₁ (.addRight carry none) fun
        | none => .addRight carry none
        | some bit => .addRight carry (some bit)
    | .addRight carry left => .popWork₂
        (match left with
          | none => .finish carry
          | some leftBit =>
              let cell := addCell leftBit false carry
              .emit cell.2 cell.1)
        fun
          | none =>
              match left with
              | none => .finish carry
              | some leftBit =>
                  let cell := addCell leftBit false carry
                  .emit cell.2 cell.1
          | some rightBit =>
              let cell := addCell (left.getD false) rightBit carry
              .emit cell.2 cell.1
    | .emit carry bit => .pushOutput bit (.addLeft carry)
    | .finish false => .halt
    | .finish true => .pushOutput true .halt
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

end CLRS.Chapter34.Turing.BinaryNat.Adder
