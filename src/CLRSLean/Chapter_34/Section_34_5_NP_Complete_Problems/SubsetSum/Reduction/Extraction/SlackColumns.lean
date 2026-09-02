import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.Extraction.VariableColumns

/-!
# Bounding the contribution of clause slack items
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- At most the three generated slack copies can contribute to one clause. -/
def clauseSlackContribution (chosen : Finset SubsetSumItem)
    (clause : Nat) : Nat :=
  ∑ slot ∈ Finset.range 3,
    if .slack clause slot ∈ chosen then 1 else 0

theorem clauseSlackContribution_le_three
    (chosen : Finset SubsetSumItem) (clause : Nat) :
    clauseSlackContribution chosen clause ≤ 3 := by
  unfold clauseSlackContribution
  have hbound := Finset.sum_le_card_nsmul (Finset.range 3)
    (fun slot => if .slack clause slot ∈ chosen then 1 else 0) 1
    (by intro slot hslot; split <;> omega)
  simpa using hbound

/-- If all selected variable items contribute zero to a clause column, that
column is exactly the contribution of its three possible slack items. -/
theorem clauseColumnSum_eq_slack_of_choice_zero
    (formula : CNF) (chosen : Finset SubsetSumItem)
    (hsubset : chosen ⊆ reductionItems formula) (clause : Nat)
    (hchoiceZero : ∀ index truth, .choice index truth ∈ chosen →
      itemDigit formula (.choice index truth)
        (reductionVariableCount formula + clause) = 0) :
    columnSum formula chosen (reductionVariableCount formula + clause) =
      clauseSlackContribution chosen clause := by
  induction chosen using Finset.induction_on with
  | empty => simp [columnSum, clauseSlackContribution]
  | @insert item chosen hnot ih =>
      have hitem : item ∈ reductionItems formula :=
        hsubset (Finset.mem_insert_self item chosen)
      have hrest : chosen ⊆ reductionItems formula := by
        intro current hcurrent
        exact hsubset (Finset.mem_insert_of_mem hcurrent)
      have hchoiceRest : ∀ index truth, .choice index truth ∈ chosen →
          itemDigit formula (.choice index truth)
            (reductionVariableCount formula + clause) = 0 := by
        intro index truth hmem
        exact hchoiceZero index truth (Finset.mem_insert_of_mem hmem)
      rw [columnSum, Finset.sum_insert hnot, ← columnSum,
        ih hrest hchoiceRest]
      cases item with
      | choice index truth =>
          have hzero := hchoiceZero index truth (Finset.mem_insert_self _ _)
          simp [clauseSlackContribution, hzero]
      | slack source slot =>
          have hslot : slot < 3 := by
            rcases (mem_reductionItems_iff.mp hitem) with hchoice | hslack
            · rcases hchoice with ⟨index, truth, himpossible, hindex⟩
              cases himpossible
            · rcases hslack with ⟨source', slot', heq, hsource, hslot⟩
              injection heq with hsourceEq hslotEq
              omega
          by_cases hsource : source = clause
          · subst source
            rw [itemDigit_slack_clause_column, if_pos rfl]
            unfold clauseSlackContribution
            let oldContribution := fun current : Nat =>
              if .slack clause current ∈ chosen then 1 else 0
            let newContribution := fun current : Nat =>
              if .slack clause current ∈
                  insert (.slack clause slot) chosen then 1 else 0
            have hslotMem : slot ∈ Finset.range 3 := Finset.mem_range.mpr hslot
            have holdAt : oldContribution slot = 0 := by
              simp [oldContribution, hnot]
            have hnewAt : newContribution slot = 1 := by
              simp [newContribution]
            have herase :
                (∑ current ∈ (Finset.range 3).erase slot,
                    oldContribution current) =
                  ∑ current ∈ (Finset.range 3).erase slot,
                    newContribution current := by
              apply Finset.sum_congr rfl
              intro current hcurrent
              have hne : current ≠ slot := Finset.ne_of_mem_erase hcurrent
              simp [oldContribution, newContribution, hne]
            have hold := Finset.sum_erase_add (Finset.range 3)
              oldContribution hslotMem
            have hnew := Finset.sum_erase_add (Finset.range 3)
              newContribution hslotMem
            change 1 + (∑ current ∈ Finset.range 3,
                oldContribution current) =
              ∑ current ∈ Finset.range 3, newContribution current
            rw [holdAt] at hold
            rw [hnewAt] at hnew
            omega
          · simp [itemDigit_slack_clause_column, clauseSlackContribution,
              Ne.symm hsource]

end CLRS.Chapter34.SubsetSumReduction
