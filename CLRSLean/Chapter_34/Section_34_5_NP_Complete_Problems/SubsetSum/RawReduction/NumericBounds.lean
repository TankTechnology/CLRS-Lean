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

/-- The binary size of a bounded packed vector is at most `base * width`.
This deliberately coarse estimate is convenient for later polynomial bounds. -/
theorem size_packColumns_le {base width : Nat} {digits : Nat → Nat}
    (hbase : 0 < base)
    (hdigits : ∀ column < width, digits column < base) :
    Nat.size (packColumns base width digits) ≤ base * width := by
  rw [Nat.size_le]
  have hpacked := packColumns_lt_pow hbase hdigits
  have hbasePow : base ^ width ≤ (2 ^ base) ^ width :=
    Nat.pow_le_pow_left (Nat.le_of_lt base.lt_two_pow_self) width
  exact lt_of_lt_of_le hpacked (by
    simpa [pow_mul] using hbasePow)

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
      2 * cnfVarCount formula + 3 * formula.length := by
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

theorem reductionBase_le (formula : CNF) :
    reductionBase formula ≤
      6 * cnfVarCount formula + 9 * formula.length + 5 := by
  rw [reductionBase, reductionItems_card_eq,
    reductionItemList_length]
  omega

theorem reductionWidth_le (formula : CNF) :
    reductionWidth formula ≤
      cnfVarCount formula + formula.length := by
  rfl

theorem reductionTarget_size_le (formula : CNF) :
    Nat.size (reductionTarget formula) ≤
      reductionBase formula * reductionWidth formula := by
  exact size_packColumns_le (reductionBase_pos formula)
    (fun column _ => targetDigit_lt_reductionBase formula column)

theorem itemValue_size_le {formula : CNF}
    (hthree : IsThreeCNF formula) (item : SubsetSumItem) :
    Nat.size (itemValue formula item) ≤
      reductionBase formula * reductionWidth formula := by
  apply size_packColumns_le (reductionBase_pos formula)
  intro column _
  have hdigit := itemDigit_le_three hthree item column
  have hbase : 5 ≤ reductionBase formula := by simp [reductionBase]
  omega

end CLRS.Chapter34.SubsetSumReduction
