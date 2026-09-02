import CLRSLean.Chapter_34.BinaryNat.Machine.Comparator.Core
import Mathlib.Tactic

/-! # Numeric semantics of the fixed binary comparator -/

namespace CLRS.Chapter34.Turing.BinaryNat.Comparator

/-- Numeric value of a least-significant-bit-first word. -/
def littleValue (bits : List Bool) : Nat :=
  Nat.ofDigits 2 (bits.map Bool.toNat)

private theorem comparison_step (left right previous : Bool) (a b : Nat) :
    (if a < b then true else if b < a then false
      else leCell left right previous) =
    (if left.toNat + 2 * a < right.toNat + 2 * b then true
      else if right.toNat + 2 * b < left.toNat + 2 * a then false
      else previous) := by
  apply Bool.eq_iff_iff.mpr
  cases left <;> cases right <;> cases previous <;>
    simp [leCell] <;> omega

private theorem compareLittle_characterization
    (left right : List Bool) (previous : Bool) :
    compareLittle left right previous =
      if littleValue left < littleValue right then true
      else if littleValue right < littleValue left then false
      else previous := by
  induction left generalizing right previous with
  | nil =>
      induction right generalizing previous with
      | nil => simp [compareLittle, littleValue]
      | cons right rights ih =>
          rw [compareLittle, ih]
          change
            (if 0 < littleValue rights then true
              else if littleValue rights < 0 then false
              else leCell false right previous) =
            (if false.toNat + 2 * 0 <
                  right.toNat + 2 * littleValue rights then true
              else if right.toNat + 2 * littleValue rights <
                  false.toNat + 2 * 0 then false
              else previous)
          exact comparison_step false right previous 0 (littleValue rights)
  | cons left lefts ih =>
      cases right with
      | nil =>
          rw [compareLittle, ih]
          change
            (if littleValue lefts < 0 then true
              else if 0 < littleValue lefts then false
              else leCell left false previous) =
            (if left.toNat + 2 * littleValue lefts <
                  false.toNat + 2 * 0 then true
              else if false.toNat + 2 * 0 <
                  left.toNat + 2 * littleValue lefts then false
              else previous)
          exact comparison_step left false previous (littleValue lefts) 0
      | cons right rights =>
          rw [compareLittle, ih]
          change
            (if littleValue lefts < littleValue rights then true
              else if littleValue rights < littleValue lefts then false
              else leCell left right previous) =
            (if left.toNat + 2 * littleValue lefts <
                  right.toNat + 2 * littleValue rights then true
              else if right.toNat + 2 * littleValue rights <
                  left.toNat + 2 * littleValue lefts then false
              else previous)
          exact comparison_step left right previous
            (littleValue lefts) (littleValue rights)

/-- Exact numeric correctness on arbitrary bit words. -/
theorem leWords_eq_decide (left right : List Bool) :
    leWords left right =
      decide (CLRS.Chapter34.binaryNatValue left ≤
        CLRS.Chapter34.binaryNatValue right) := by
  rw [leWords, compareLittle_characterization]
  simp only [littleValue, CLRS.Chapter34.binaryNatValue,
    List.map_reverse]
  by_cases hlt : Nat.ofDigits 2 (List.map Bool.toNat left).reverse <
      Nat.ofDigits 2 (List.map Bool.toNat right).reverse
  · simp [hlt, Nat.le_of_lt hlt]
  · by_cases hgt : Nat.ofDigits 2 (List.map Bool.toNat right).reverse <
        Nat.ofDigits 2 (List.map Bool.toNat left).reverse
    · simp [hlt, hgt, Nat.not_le_of_gt hgt]
    · simp [hlt, hgt, Nat.le_of_not_gt hgt]

theorem leWords_eq_true_iff (left right : List Bool) :
    leWords left right = true ↔
      CLRS.Chapter34.binaryNatValue left ≤
        CLRS.Chapter34.binaryNatValue right := by
  rw [leWords_eq_decide, decide_eq_true_eq]

theorem leWords_encoded_eq_true_iff (left right : Nat) :
    leWords (CLRS.Chapter34.encodeBinaryNat left)
        (CLRS.Chapter34.encodeBinaryNat right) = true ↔
      left ≤ right := by
  rw [leWords_eq_true_iff, CLRS.Chapter34.binaryNatValue_encode,
    CLRS.Chapter34.binaryNatValue_encode]

end CLRS.Chapter34.Turing.BinaryNat.Comparator
