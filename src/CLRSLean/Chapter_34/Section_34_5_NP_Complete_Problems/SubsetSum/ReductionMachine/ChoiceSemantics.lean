import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceBatchSource
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.SmallDigitBlock
import Mathlib.Tactic

/-!
# Bit-block semantics of SUBSET-SUM choice items

Every choice item consists of a one-hot variable prefix followed by one
literal-occurrence digit per clause.  This file proves that decomposition
directly at the fixed-width bit-block level used by the reduction machine.
-/

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Fixed-width packing distributes across a split of its column range. -/
theorem packedBitsLE_add (blockWidth left right : Nat)
    (digits : Nat → Nat) :
    packedBitsLE blockWidth (left + right) digits =
      packedBitsLE blockWidth left digits ++
        packedBitsLE blockWidth right (fun column =>
          digits (left + column)) := by
  induction left generalizing digits with
  | zero => simp
  | succ left ih =>
      rw [Nat.succ_add, packedBitsLE_succ,
        ih (fun column => digits (column + 1)), packedBitsLE_succ,
        List.append_assoc]
      congr 2
      apply congrArg (packedBitsLE blockWidth right)
      funext column
      congr 1
      omega

/-- Packing depends only on digits in its explicit column range. -/
theorem packedBitsLE_congr {blockWidth width : Nat}
    {left right : Nat → Nat}
    (h : ∀ column < width, left column = right column) :
    packedBitsLE blockWidth width left =
      packedBitsLE blockWidth width right := by
  induction width generalizing left right with
  | zero => rfl
  | succ width ih =>
      rw [packedBitsLE_succ, packedBitsLE_succ,
        h 0 (by omega)]
      apply congrArg
      exact ih (fun column hcolumn => h (column + 1) (by omega))

/-- Little-endian one-hot variable-column prefix for one choice item. -/
def choiceVariableBlocksLE (formula : CNF) (index : Nat) : List Bool :=
  packedBitsLE (reductionBlockWidth formula)
    (reductionVariableCount formula)
    (fun column => if column = index then 1 else 0)

/-- Little-endian clause-occurrence suffix for one literal choice. -/
def choiceClauseBlocksLE (formula : CNF) (index : Nat)
    (truth : Bool) : List Bool :=
  packedBitsLE (reductionBlockWidth formula) formula.length
    (fun clause =>
      (formula.getD clause []).count (itemLiteral index truth))

/-- Complete little-endian fixed-block payload of a choice item. -/
def choicePackedBitsLE (formula : CNF) (index : Nat)
    (truth : Bool) : List Bool :=
  choiceVariableBlocksLE formula index ++
    choiceClauseBlocksLE formula index truth

/-- The split payload is byte-for-byte the generic item-digit packer. -/
theorem choicePackedBitsLE_eq (formula : CNF) (index : Nat)
    (truth : Bool) :
    choicePackedBitsLE formula index truth =
      packedBitsLE (reductionBlockWidth formula)
        (reductionWidth formula)
        (itemDigit formula (.choice index truth)) := by
  rw [choicePackedBitsLE, reductionWidth,
    packedBitsLE_add]
  congr 1
  · apply packedBitsLE_congr
    intro column hcolumn
    exact (itemDigit_variable_column formula truth hcolumn).symm
  · apply packedBitsLE_congr
    intro clause hclause
    exact (itemDigit_variable_clause_column formula truth).symm

/-- Canonical public bit payload obtained from the split block stream. -/
def choiceItemBits (formula : CNF) (index : Nat)
    (truth : Bool) : List Bool :=
  canonicalizeBinaryBits
    (choicePackedBitsLE formula index truth).reverse

/-- Exact semantic target for the later choice-item machine. -/
theorem choiceItemBits_eq (formula : CNF) (index : Nat)
    (truth : Bool) :
    choiceItemBits formula index truth =
      reductionItemBits formula (.choice index truth) := by
  rw [choiceItemBits, reductionItemBits, encodePackedColumns,
    choicePackedBitsLE_eq]

/-- Finite digit selected by a clause occurrence count.  Counts above three
are mapped to zero; the three-CNF branch proves that case unreachable. -/
def occurrenceSmallDigit (count : Nat) : SmallDigit :=
  match count with
  | 0 => .zero
  | 1 => .one
  | 2 => .two
  | 3 => .three
  | _ => .zero

@[simp] theorem occurrenceSmallDigit_value_of_le_three
    {count : Nat} (hcount : count ≤ 3) :
    (occurrenceSmallDigit count).value = count := by
  interval_cases count <;> rfl

theorem clause_count_le_three {formula : CNF}
    (hthree : IsThreeCNF formula) {clause index : Nat}
    (truth : Bool) (hclause : clause < formula.length) :
    (formula.getD clause []).count (itemLiteral index truth) ≤ 3 := by
  have hlength : (formula.getD clause []).length ≤ 3 := by
    have hgetD : formula.getD clause [] = formula[clause] := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hclause]
      rfl
    rw [hgetD]
    exact hthree formula[clause] (List.getElem_mem hclause)
  exact List.count_le_length.trans hlength

/-- On a three-CNF formula, the finite controller's digit agrees with the
mathematical occurrence count for every in-range clause. -/
theorem occurrenceSmallDigit_clause_value {formula : CNF}
    (hthree : IsThreeCNF formula) {clause index : Nat}
    (truth : Bool) (hclause : clause < formula.length) :
    (occurrenceSmallDigit
      ((formula.getD clause []).count
        (itemLiteral index truth))).value =
      (formula.getD clause []).count (itemLiteral index truth) :=
  occurrenceSmallDigit_value_of_le_three
    (clause_count_le_three hthree truth hclause)

end CLRS.Chapter34.Turing.SubsetSumReduction
