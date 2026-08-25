import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.SourceBounds
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.ColumnSemantics
import CLRSLean.Chapter_34.BinaryNat.Length

/-! # Numeric bounds for the serialized 3-CNF to SUBSET-SUM map -/

namespace CLRS.Chapter34.SubsetSumReduction

/-- A bounded base-`base` column vector represents a number below
`base ^ width`. -/
theorem packColumns_lt_pow {base width : Nat} {digits : Nat → Nat}
    (_hbase : 0 < base)
    (hdigits : ∀ column < width, digits column < base) :
    packColumns base width digits < base ^ width := by
  induction width generalizing digits with
  | zero => simp [packColumns]
  | succ width ih =>
      have hhead := hdigits 0 (by omega)
      have htail := ih
        (fun column hcolumn => hdigits (column + 1) (by omega))
      simp only [packColumns_succ, pow_succ]
      nlinarith

/-- With a power-of-two radix, the binary size of a bounded packed vector is
at most the number of fixed-width bit cells. -/
theorem size_packColumns_pow_two_le {blockWidth width : Nat}
    {digits : Nat → Nat}
    (hdigits : ∀ column < width, digits column < 2 ^ blockWidth) :
    Nat.size (packColumns (2 ^ blockWidth) width digits) ≤
      blockWidth * width := by
  rw [Nat.size_le]
  simpa [pow_mul] using
    (packColumns_lt_pow (by simp) hdigits)

@[simp] theorem variableItemList_length (variableCount : Nat) :
    (variableItemList variableCount).length = 2 * variableCount := by
  simp [variableItemList]
  omega

@[simp] theorem slackItemList_length (clauseCount : Nat) :
    (slackItemList clauseCount).length = 3 * clauseCount := by
  simp [slackItemList]
  omega

@[simp] theorem reductionItemList_length (formula : CNF) :
    (reductionItemList formula).length =
      2 * reductionVariableCount formula + 3 * formula.length := by
  simp [reductionItemList]

theorem reductionItems_card_eq (formula : CNF) :
    (reductionItems formula).card = (reductionItemList formula).length := by
  classical
  have heq : (reductionItemList formula).toFinset =
      reductionItems formula := by
    ext item
    simp [mem_reductionItemList_iff]
  rw [← heq, List.toFinset_card_of_nodup
    (reductionItemList_nodup formula)]

theorem reductionBlockWidth_eq (formula : CNF) :
    reductionBlockWidth formula =
      2 * reductionVariableCount formula + 3 * formula.length + 3 := by
  rw [reductionBlockWidth, reductionItems_card_eq,
    reductionItemList_length]

theorem reductionWidth_le (formula : CNF) :
    reductionWidth formula ≤
      reductionVariableCount formula + formula.length := by
  rfl

theorem reductionTarget_size_le (formula : CNF) :
    Nat.size (reductionTarget formula) ≤
      reductionBlockWidth formula * reductionWidth formula := by
  rw [reductionTarget, reductionBase]
  exact size_packColumns_pow_two_le
    (fun column _ => targetDigit_lt_reductionBase formula column)

theorem itemValue_size_le {formula : CNF}
    (hthree : IsThreeCNF formula) (item : SubsetSumItem) :
    Nat.size (itemValue formula item) ≤
      reductionBlockWidth formula * reductionWidth formula := by
  rw [itemValue, reductionBase]
  apply size_packColumns_pow_two_le
  intro column _
  have hdigit := itemDigit_le_three hthree item column
  have hbase : 4 < 2 ^ reductionBlockWidth formula := by
    simpa [reductionBase] using four_lt_reductionBase formula
  omega

end CLRS.Chapter34.SubsetSumReduction
