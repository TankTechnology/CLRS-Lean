import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.SlackProgressionSource
import Mathlib.Tactic

/-!
# Closed binary form of SUBSET-SUM slack items

A slack item has exactly one nonzero radix digit.  The lemmas below reduce
its packed natural value and canonical binary payload to a single leading one
followed by a runtime affine number of zeroes.
-/

namespace CLRS.Chapter34

open SubsetSumReduction

theorem bits_two_pow (exponent : Nat) :
    Nat.bits (2 ^ exponent) =
      List.replicate exponent false ++ [true] := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [show 2 ^ (exponent + 1) = Nat.bit false (2 ^ exponent) by
        simp [pow_succ, Nat.mul_comm]]
      rw [Nat.bits_append_bit (2 ^ exponent) false (by simp), ih]
      simp [List.replicate_succ]

theorem encodeBinaryNat_two_pow (exponent : Nat) :
    encodeBinaryNat (2 ^ exponent) =
      true :: List.replicate exponent false := by
  rw [encodeBinaryNat, if_neg (by positivity), bits_two_pow]
  simp

namespace SubsetSumReduction

theorem packColumns_zero_digits (base width : Nat) :
    packColumns base width (fun _ => 0) = 0 := by
  induction width with
  | zero => rfl
  | succ width ih => simp [packColumns, ih]

/-- Packing a unique unit digit returns the corresponding radix power. -/
theorem packColumns_single (base width index : Nat) :
    packColumns base width (fun column => if column = index then 1 else 0) =
      if index < width then base ^ index else 0 := by
  induction width generalizing index with
  | zero => simp
  | succ width ih =>
      cases index with
      | zero => simp [packColumns, packColumns_zero_digits]
      | succ index =>
          rw [packColumns_succ]
          simp only [Nat.zero_ne_add_one, ↓reduceIte, zero_add]
          have hshift :
              (fun column => if column + 1 = index + 1 then 1 else 0) =
                (fun column => if column = index then 1 else 0) := by
            funext column
            simp
          rw [hshift, ih]
          by_cases h : index < width
          · simp [h, pow_succ, Nat.mul_comm]
          · simp [h]

/-- Exact natural value of an in-range slack label. -/
theorem itemValue_slack_eq (formula : CNF) {clause slot : Nat}
    (hclause : clause < formula.length) :
    itemValue formula (.slack clause slot) =
      reductionBase formula ^
        (reductionVariableCount formula + clause) := by
  rw [itemValue]
  let index := reductionVariableCount formula + clause
  have hdigits : ∀ column < reductionWidth formula,
      itemDigit formula (.slack clause slot) column =
        if column = index then 1 else 0 := by
    intro column hcolumn
    by_cases hvariable : column < reductionVariableCount formula
    · have hne : column ≠ index := by omega
      simp [itemDigit, hvariable, hne]
    · have hdiff :
          column - reductionVariableCount formula < formula.length := by
        simp only [reductionWidth] at hcolumn
        omega
      by_cases heq :
          column - reductionVariableCount formula = clause
      · have hcolumnEq : column = index := by omega
        subst column
        simp [itemDigit, index]
      · have hcolumnNe : column ≠ index := by omega
        simp [itemDigit, hvariable, heq, hcolumnNe]
  rw [packColumns_congr hdigits, packColumns_single]
  simp [index, reductionWidth, hclause]

end SubsetSumReduction

namespace Turing.SubsetSumReduction

open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Closed canonical payload of every in-range slack item. -/
theorem reductionItemBits_slack_eq {formula : CNF}
    (hthree : IsThreeCNF formula) {clause slot : Nat}
    (hclause : clause < formula.length) :
    reductionItemBits formula (.slack clause slot) =
      true :: List.replicate
        (reductionBlockWidth formula *
          (reductionVariableCount formula + clause)) false := by
  rw [reductionItemBits_eq hthree,
    itemValue_slack_eq formula hclause, reductionBase]
  rw [← pow_mul]
  exact encodeBinaryNat_two_pow _

end Turing.SubsetSumReduction
end CLRS.Chapter34
