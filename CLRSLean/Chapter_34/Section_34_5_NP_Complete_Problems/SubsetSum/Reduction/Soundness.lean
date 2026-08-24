import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.Extraction.SlackColumns

/-!
# Soundness of the 3-CNF-SAT to SUBSET-SUM reduction
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- A clause column equal to four cannot be filled only by its three slack
items.  Hence a selected variable item names a true literal occurrence. -/
theorem evalClause_getD_of_exact_columns
    {formula : CNF} {chosen : Finset SubsetSumItem}
    (hsubset : chosen ⊆ reductionItems formula)
    (hcolumns : ∀ column < reductionWidth formula,
      columnSum formula chosen column = targetDigit formula column)
    {clause : Nat} (hclause : clause < formula.length) :
    evalClause (assignmentFromItems chosen) (formula.getD clause []) := by
  by_contra hfalse
  have hchoiceZero : ∀ index truth, .choice index truth ∈ chosen →
      itemDigit formula (.choice index truth)
        (cnfVarCount formula + clause) = 0 := by
    intro index truth hselected
    have hgenerated : .choice index truth ∈ reductionItems formula :=
      hsubset hselected
    have hindex : index < cnfVarCount formula := by
      simpa [reductionItems] using hgenerated
    have hvariableColumn : columnSum formula chosen index = 1 := by
      have hexact := hcolumns index (by simp [reductionWidth]; omega)
      simpa [targetDigit, hindex] using hexact
    have htruth : truth = assignmentFromItems chosen index :=
      (choice_mem_iff_assignmentFromItems formula chosen hindex
        hvariableColumn truth).mp hselected
    have hnotMem : itemLiteral index truth ∉ formula.getD clause [] := by
      intro hliteral
      apply hfalse
      refine ⟨itemLiteral index truth, hliteral, ?_⟩
      rw [htruth]
      exact evalLit_itemLiteral_assignmentFromItems chosen index
    rw [itemDigit_variable_clause_column]
    exact List.count_eq_zero.mpr hnotMem
  have heq := clauseColumnSum_eq_slack_of_choice_zero
    formula chosen hsubset clause hchoiceZero
  have hslack := clauseSlackContribution_le_three chosen clause
  have hfour :
      columnSum formula chosen (cnfVarCount formula + clause) = 4 := by
    have hexact := hcolumns (cnfVarCount formula + clause)
      (by simp [reductionWidth]; omega)
    simpa using hexact
  omega

/-- Every exact SUBSET-SUM certificate decodes to a satisfying assignment. -/
theorem cnfToSubsetSum_sound {formula : CNF}
    (hthree : IsThreeCNF formula) :
    (cnfToSubsetSum formula).HasSubsetSum → CnfSatisfiable formula := by
  rintro ⟨chosen, hsubset, hsum⟩
  have hcolumns := columnSum_eq_targetDigit_of_sum_eq hthree hsubset hsum
  refine ⟨assignmentFromItems chosen, ?_⟩
  intro clause hclause
  obtain ⟨index, hindex, rfl⟩ := List.mem_iff_getElem.mp hclause
  have heval := evalClause_getD_of_exact_columns hsubset hcolumns hindex
  rw [List.getD_eq_getElem formula [] hindex] at heval
  exact heval

end CLRS.Chapter34.SubsetSumReduction
