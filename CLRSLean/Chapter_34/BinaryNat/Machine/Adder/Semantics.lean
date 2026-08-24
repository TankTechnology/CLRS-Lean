import CLRSLean.Chapter_34.BinaryNat.Machine.Adder.Core
import Mathlib.Tactic

/-! # Numeric semantics of the fixed binary adder -/

namespace CLRS.Chapter34.Turing.BinaryNat.Adder

/-- Numeric value of a least-significant-bit-first word. -/
def littleValue (bits : List Bool) : Nat :=
  Nat.ofDigits 2 (bits.map Bool.toNat)

/-- One full-adder cell preserves the elementary base-two value equation. -/
theorem addCell_value (left right carry : Bool) :
    (addCell left right carry).1.toNat +
        2 * (addCell left right carry).2.toNat =
      left.toNat + right.toNat + carry.toNat := by
  cases left <;> cases right <;> cases carry <;> decide

private theorem binaryNatValue_append_bit (headBits : List Bool) (bit : Bool) :
    CLRS.Chapter34.binaryNatValue (headBits ++ [bit]) =
      bit.toNat + 2 * CLRS.Chapter34.binaryNatValue headBits := by
  simp [CLRS.Chapter34.binaryNatValue, List.reverse_append,
    Nat.ofDigits_cons]

/-- The recursive bit algorithm has exactly the sum of the two little-endian
operand values and the incoming carry. -/
theorem addLittle_value (left right : List Bool) (carry : Bool) :
    CLRS.Chapter34.binaryNatValue (addLittle left right carry) =
      littleValue left + littleValue right + carry.toNat := by
  induction left generalizing right carry with
  | nil =>
      induction right generalizing carry with
      | nil => cases carry <;> simp [addLittle, littleValue,
          CLRS.Chapter34.binaryNatValue]
      | cons right rights ih =>
          let cell := addCell false right carry
          rw [addLittle, binaryNatValue_append_bit, ih cell.2]
          simp only [littleValue, List.map_cons, Nat.ofDigits_cons,
            List.map_nil, Nat.ofDigits_nil, Nat.zero_add]
          have hcell := addCell_value false right carry
          simp only [Bool.toNat_false, Nat.zero_add] at hcell
          dsimp [cell]
          omega
  | cons left lefts ih =>
      cases right with
      | nil =>
          let cell := addCell left false carry
          rw [addLittle, binaryNatValue_append_bit, ih [] cell.2]
          simp only [littleValue, List.map_cons, Nat.ofDigits_cons,
            List.map_nil, Nat.ofDigits_nil, Nat.add_zero]
          have hcell := addCell_value left false carry
          simp only [Bool.toNat_false, Nat.add_zero] at hcell
          dsimp [cell]
          omega
      | cons right rights =>
          let cell := addCell left right carry
          rw [addLittle, binaryNatValue_append_bit, ih rights cell.2]
          simp only [littleValue, List.map_cons, Nat.ofDigits_cons]
          have hcell := addCell_value left right carry
          dsimp [cell]
          omega

/-- Exact numeric correctness on arbitrary bit words.  Canonical inputs are
not required: leading zeroes, if present, have their usual numeric meaning. -/
theorem binaryNatValue_addWords (left right : List Bool) :
    CLRS.Chapter34.binaryNatValue (addWords left right) =
      CLRS.Chapter34.binaryNatValue left +
        CLRS.Chapter34.binaryNatValue right := by
  rw [addWords, addLittle_value]
  simp [littleValue, CLRS.Chapter34.binaryNatValue]

/-- In particular, encoded natural operands are added numerically exactly. -/
theorem binaryNatValue_add_encoded (left right : Nat) :
    CLRS.Chapter34.binaryNatValue
        (addWords (CLRS.Chapter34.encodeBinaryNat left)
          (CLRS.Chapter34.encodeBinaryNat right)) =
      left + right := by
  rw [binaryNatValue_addWords, CLRS.Chapter34.binaryNatValue_encode,
    CLRS.Chapter34.binaryNatValue_encode]

end CLRS.Chapter34.Turing.BinaryNat.Adder
