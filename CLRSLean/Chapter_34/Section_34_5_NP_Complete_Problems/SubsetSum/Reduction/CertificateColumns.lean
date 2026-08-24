import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.CertificateBuilder

/-!
# Column totals of the assignment certificate

The selected variable item contributes one to its own variable column and the
number of true literal occurrences to each clause column.  The selected unit
slack copies fill every satisfied clause column to four.
-/

namespace CLRS.Chapter34.SubsetSumReduction

theorem assignmentChoiceItems_variable_column
    (formula : CNF) (assignment : Nat → Bool)
    {column : Nat} (hcolumn : column < cnfVarCount formula) :
    columnSum formula (assignmentChoiceItems formula assignment) column = 1 := by
  simp [columnSum, assignmentChoiceItems, Finset.sum_image, hcolumn]

theorem assignmentChoiceItems_clause_column
    (formula : CNF) (assignment : Nat → Bool) (clause : Nat) :
    columnSum formula (assignmentChoiceItems formula assignment)
        (cnfVarCount formula + clause) =
      assignmentClauseCount (cnfVarCount formula) assignment
        (formula.getD clause []) := by
  simp [columnSum, assignmentChoiceItems, Finset.sum_image,
    assignmentClauseCount]

theorem assignmentSlackItems_variable_column
    (formula : CNF) (assignment : Nat → Bool)
    {column : Nat} (hcolumn : column < cnfVarCount formula) :
    columnSum formula (assignmentSlackItems formula assignment) column = 0 := by
  simp [columnSum, assignmentSlackItems, Finset.sum_image, hcolumn]

theorem assignmentSlackItems_clause_column
    (formula : CNF) (assignment : Nat → Bool) {clause : Nat}
    (hclause : clause < formula.length)
    (hpos : 0 < assignmentClauseCount (cnfVarCount formula) assignment
      (formula.getD clause []))
    (hle : assignmentClauseCount (cnfVarCount formula) assignment
      (formula.getD clause []) ≤ 3) :
    columnSum formula (assignmentSlackItems formula assignment)
        (cnfVarCount formula + clause) =
      4 - assignmentClauseCount (cnfVarCount formula) assignment
        (formula.getD clause []) := by
  unfold columnSum assignmentSlackItems
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    calc
      _ = ∑ source ∈ Finset.range formula.length,
          ∑ slot ∈ Finset.range 3,
            if slot < 4 - assignmentClauseCount (cnfVarCount formula)
                assignment (formula.getD source []) then
              itemDigit formula (.slack source slot)
                (cnfVarCount formula + clause)
            else 0 := Finset.sum_product _ _ _
      _ = _ := by
        rw [Finset.sum_eq_single clause]
        · simp only [itemDigit_slack_clause_column, ↓reduceIte]
          change (∑ slot ∈ Finset.range 3,
              if slot < 4 - assignmentClauseCount (cnfVarCount formula)
                  assignment (List.getD formula clause []) then 1 else 0) =
            4 - assignmentClauseCount (cnfVarCount formula) assignment
              (List.getD formula clause [])
          have hcountCases :
              assignmentClauseCount (cnfVarCount formula) assignment
                  (formula.getD clause []) = 1 ∨
              assignmentClauseCount (cnfVarCount formula) assignment
                  (formula.getD clause []) = 2 ∨
              assignmentClauseCount (cnfVarCount formula) assignment
                  (formula.getD clause []) = 3 := by
            omega
          rcases hcountCases with hcount | hcount | hcount
          · rw [hcount]
            decide
          · rw [hcount]
            decide
          · rw [hcount]
            decide
        · intro source hsource hne
          simp [Ne.symm hne]
        · simp [hclause]
  · intro a ha b hb hab
    injection hab with hfirst hsecond
    exact Prod.ext hfirst hsecond

theorem assignmentClauseCount_bounds_of_eval
    {formula : CNF} {assignment : Nat → Bool}
    (hthree : IsThreeCNF formula) (heval : evalCNF assignment formula)
    {clause : Nat} (hclause : clause < formula.length) :
    0 < assignmentClauseCount (cnfVarCount formula) assignment
          (formula.getD clause []) ∧
      assignmentClauseCount (cnfVarCount formula) assignment
          (formula.getD clause []) ≤ 3 := by
  have hmem : formula[clause] ∈ formula := List.getElem_mem hclause
  have hbound : ∀ literal ∈ formula.getD clause [],
      literalIndex literal < cnfVarCount formula := by
    rw [List.getD_eq_getElem formula [] hclause]
    intro literal hliteral
    exact literalIndex_lt_cnfVarCount hmem hliteral
  constructor
  · apply assignmentClauseCount_pos assignment hbound
    rw [List.getD_eq_getElem formula [] hclause]
    exact heval _ hmem
  · exact le_trans (assignmentClauseCount_le_length assignment hbound)
      (clauseAt_length_le_three hthree clause)

theorem columnSum_assignmentItems_variable
    (formula : CNF) (assignment : Nat → Bool)
    {column : Nat} (hcolumn : column < cnfVarCount formula) :
    columnSum formula (assignmentItems formula assignment) column =
      targetDigit formula column := by
  rw [assignmentItems, columnSum,
    Finset.sum_union
      (assignmentChoiceItems_disjoint_assignmentSlackItems formula assignment)]
  rw [← columnSum, ← columnSum,
    assignmentChoiceItems_variable_column formula assignment hcolumn,
    assignmentSlackItems_variable_column formula assignment hcolumn]
  simp [targetDigit, hcolumn]

theorem columnSum_assignmentItems_clause
    {formula : CNF} {assignment : Nat → Bool}
    (hthree : IsThreeCNF formula) (heval : evalCNF assignment formula)
    {clause : Nat} (hclause : clause < formula.length) :
    columnSum formula (assignmentItems formula assignment)
        (cnfVarCount formula + clause) =
      targetDigit formula (cnfVarCount formula + clause) := by
  obtain ⟨hpos, hle⟩ :=
    assignmentClauseCount_bounds_of_eval hthree heval hclause
  rw [assignmentItems, columnSum,
    Finset.sum_union
      (assignmentChoiceItems_disjoint_assignmentSlackItems formula assignment)]
  rw [← columnSum, ← columnSum,
    assignmentChoiceItems_clause_column formula assignment clause,
    assignmentSlackItems_clause_column formula assignment hclause hpos hle]
  rw [targetDigit_clause_column]
  omega

theorem columnSum_assignmentItems_eq_target
    {formula : CNF} {assignment : Nat → Bool}
    (hthree : IsThreeCNF formula) (heval : evalCNF assignment formula) :
    ∀ column < reductionWidth formula,
      columnSum formula (assignmentItems formula assignment) column =
        targetDigit formula column := by
  intro column hcolumn
  by_cases hvariable : column < cnfVarCount formula
  · exact columnSum_assignmentItems_variable formula assignment hvariable
  · have hclause : column - cnfVarCount formula < formula.length := by
      simp only [reductionWidth] at hcolumn
      omega
    have hcolumnEq :
        column = cnfVarCount formula + (column - cnfVarCount formula) := by
      omega
    rw [hcolumnEq]
    exact columnSum_assignmentItems_clause hthree heval hclause

theorem sum_assignmentItems_eq_target
    {formula : CNF} {assignment : Nat → Bool}
    (hthree : IsThreeCNF formula) (heval : evalCNF assignment formula) :
    (∑ item ∈ assignmentItems formula assignment, itemValue formula item) =
      reductionTarget formula := by
  rw [sum_itemValue_eq_pack_columnSum]
  exact packColumns_congr
    (columnSum_assignmentItems_eq_target hthree heval)

end CLRS.Chapter34.SubsetSumReduction
