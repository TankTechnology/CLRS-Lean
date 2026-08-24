import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.ColumnSemantics

/-!
# Extracting an assignment from variable columns
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- Assignment read from the selected positive variable item. -/
def assignmentFromItems (chosen : Finset SubsetSumItem) (index : Nat) : Bool :=
  decide (.choice index true ∈ chosen)

theorem variableColumnSum_eq (formula : CNF)
    (chosen : Finset SubsetSumItem) {column : Nat}
    (hcolumn : column < cnfVarCount formula) :
    columnSum formula chosen column =
      (if .choice column false ∈ chosen then 1 else 0) +
      (if .choice column true ∈ chosen then 1 else 0) := by
  induction chosen using Finset.induction_on with
  | empty => simp [columnSum]
  | @insert item chosen hnot ih =>
      rw [columnSum, Finset.sum_insert hnot, ← columnSum, ih]
      cases item with
      | choice index truth =>
          by_cases hindex : index = column
          · subst index
            cases truth <;> simp_all [itemDigit, Nat.add_comm]
          · have hne : column ≠ index := Ne.symm hindex
            cases truth <;> simp [itemDigit, hcolumn, hne]
      | slack clause slot =>
          simp [itemDigit, hcolumn]

/-- A variable column equal to one forces exactly the item agreeing with the
extracted assignment. -/
theorem choice_mem_iff_assignmentFromItems
    (formula : CNF) (chosen : Finset SubsetSumItem)
    {index : Nat} (hindex : index < cnfVarCount formula)
    (hsum : columnSum formula chosen index = 1) (truth : Bool) :
    .choice index truth ∈ chosen ↔
      truth = assignmentFromItems chosen index := by
  have hone :
      (if .choice index false ∈ chosen then 1 else 0) +
        (if .choice index true ∈ chosen then 1 else 0) = 1 := by
    rw [← variableColumnSum_eq formula chosen hindex]
    exact hsum
  cases truth <;>
    by_cases hfalse : .choice index false ∈ chosen <;>
    by_cases htrue : .choice index true ∈ chosen <;>
    simp_all [assignmentFromItems]

theorem evalLit_itemLiteral_assignmentFromItems
    (chosen : Finset SubsetSumItem) (index : Nat) :
    evalLit (assignmentFromItems chosen)
      (itemLiteral index (assignmentFromItems chosen index)) := by
  cases hvalue : assignmentFromItems chosen index <;>
    simp [itemLiteral, evalLit, hvalue]

end CLRS.Chapter34.SubsetSumReduction
