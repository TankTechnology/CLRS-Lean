import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.RadixBounds

/-!
# Column semantics of the SUBSET-SUM construction

The input-dependent radix is larger than every possible selected column sum.
Consequently equality of the packed natural numbers is equivalent to equality
in every variable and clause column.
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- Total contribution of a chosen item set to one unpacked column. -/
def columnSum (formula : CNF) (chosen : Finset SubsetSumItem)
    (column : Nat) : Nat :=
  ∑ item ∈ chosen, itemDigit formula item column

theorem clauseAt_length_le_three
    {formula : CNF} (hthree : IsThreeCNF formula) (clause : Nat) :
    (formula.getD clause []).length ≤ 3 := by
  by_cases hclause : clause < formula.length
  · rw [List.getD_eq_getElem formula [] hclause]
    exact hthree _ (List.getElem_mem hclause)
  · simp [List.getD, hclause]

theorem itemDigit_le_three
    {formula : CNF} (hthree : IsThreeCNF formula)
    (item : SubsetSumItem) (column : Nat) :
    itemDigit formula item column ≤ 3 := by
  cases item with
  | choice index truth =>
      simp only [itemDigit]
      split
      · split <;> omega
      · exact le_trans List.count_le_length
          (clauseAt_length_le_three hthree _)
  | slack clause slot =>
      simp only [itemDigit]
      split
      · omega
      · split <;> omega

theorem columnSum_le_three_mul_card
    {formula : CNF} (hthree : IsThreeCNF formula)
    (chosen : Finset SubsetSumItem) (column : Nat) :
    columnSum formula chosen column ≤ 3 * chosen.card := by
  unfold columnSum
  have hsum := Finset.sum_le_card_nsmul chosen
    (fun item => itemDigit formula item column) 3
    (fun item _ => itemDigit_le_three hthree item column)
  simpa [Nat.mul_comm] using hsum

theorem columnSum_lt_reductionBase
    {formula : CNF} {chosen : Finset SubsetSumItem}
    (hthree : IsThreeCNF formula)
    (hsubset : chosen ⊆ reductionItems formula) (column : Nat) :
    columnSum formula chosen column < reductionBase formula := by
  have hsum := columnSum_le_three_mul_card hthree chosen column
  have hcard := Finset.card_le_card hsubset
  exact lt_of_le_of_lt (le_trans hsum (Nat.mul_le_mul_left 3 hcard))
    (three_mul_reductionItems_card_lt_base formula)

theorem targetDigit_lt_reductionBase (formula : CNF) (column : Nat) :
    targetDigit formula column < reductionBase formula := by
  have hbase := four_lt_reductionBase formula
  simp only [targetDigit]
  split <;> omega

theorem sum_itemValue_eq_pack_columnSum
    (formula : CNF) (chosen : Finset SubsetSumItem) :
    (∑ item ∈ chosen, itemValue formula item) =
      packColumns (reductionBase formula) (reductionWidth formula)
        (columnSum formula chosen) := by
  exact sum_packColumns chosen (reductionBase formula)
    (reductionWidth formula) (itemDigit formula)

theorem columnSum_eq_targetDigit_of_sum_eq
    {formula : CNF} {chosen : Finset SubsetSumItem}
    (hthree : IsThreeCNF formula)
    (hsubset : chosen ⊆ reductionItems formula)
    (hsum : ∑ item ∈ chosen, itemValue formula item = reductionTarget formula) :
    ∀ column < reductionWidth formula,
      columnSum formula chosen column = targetDigit formula column := by
  apply packColumns_injective_of_lt_base
    (reductionBase_pos formula)
    (fun column _ => columnSum_lt_reductionBase hthree hsubset column)
    (fun column _ => targetDigit_lt_reductionBase formula column)
  rw [← sum_itemValue_eq_pack_columnSum]
  exact hsum

end CLRS.Chapter34.SubsetSumReduction
