import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.OccurrenceCount

/-!
# SUBSET-SUM certificate induced by a satisfying assignment
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- Select exactly the item agreeing with the assignment for every variable. -/
def assignmentChoiceItems (formula : CNF) (assignment : Nat → Bool) :
    Finset SubsetSumItem :=
  (Finset.range (reductionVariableCount formula)).image
    (fun index => .choice index (assignment index))

/-- Select enough of the three unit slack copies to raise each clause's true
occurrence count to four. -/
def assignmentSlackItems (formula : CNF) (assignment : Nat → Bool) :
    Finset SubsetSumItem :=
  (((Finset.range formula.length).product (Finset.range 3)).filter
    (fun pair => pair.2 < 4 - assignmentClauseCount
      (reductionVariableCount formula) assignment
        (formula.getD pair.1 []))).image
    (fun pair => .slack pair.1 pair.2)

/-- Full SUBSET-SUM certificate induced by an assignment. -/
def assignmentItems (formula : CNF) (assignment : Nat → Bool) :
    Finset SubsetSumItem :=
  assignmentChoiceItems formula assignment ∪
    assignmentSlackItems formula assignment

theorem choice_mem_assignmentChoiceItems_iff
    (formula : CNF) (assignment : Nat → Bool) (index : Nat) (truth : Bool) :
    .choice index truth ∈ assignmentChoiceItems formula assignment ↔
      index < reductionVariableCount formula ∧
        truth = assignment index := by
  rw [assignmentChoiceItems, Finset.mem_image]
  constructor
  · rintro ⟨source, hsource, hitem⟩
    injection hitem with hindex htruth
    subst index
    exact ⟨Finset.mem_range.mp hsource, htruth.symm⟩
  · rintro ⟨hindex, rfl⟩
    exact ⟨index, Finset.mem_range.mpr hindex, rfl⟩

@[simp] theorem slack_not_mem_assignmentChoiceItems
    (formula : CNF) (assignment : Nat → Bool) (clause slot : Nat) :
    .slack clause slot ∉ assignmentChoiceItems formula assignment := by
  simp [assignmentChoiceItems]

theorem slack_mem_assignmentSlackItems_iff
    (formula : CNF) (assignment : Nat → Bool) (clause slot : Nat) :
    .slack clause slot ∈ assignmentSlackItems formula assignment ↔
      clause < formula.length ∧ slot < 3 ∧
        slot < 4 - assignmentClauseCount (reductionVariableCount formula)
          assignment (formula.getD clause []) := by
  rw [assignmentSlackItems, Finset.mem_image]
  constructor
  · rintro ⟨pair, hpair, hitem⟩
    rcases Finset.mem_filter.mp hpair with ⟨hproduct, hneeded⟩
    rcases Finset.mem_product.mp hproduct with ⟨hclause, hslot⟩
    injection hitem with hpClause hpSlot
    subst clause
    subst slot
    exact ⟨Finset.mem_range.mp hclause, Finset.mem_range.mp hslot, hneeded⟩
  · rintro ⟨hclause, hslot, hneeded⟩
    refine ⟨(clause, slot), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hclause, Finset.mem_range.mpr hslot⟩, hneeded⟩

@[simp] theorem choice_not_mem_assignmentSlackItems
    (formula : CNF) (assignment : Nat → Bool) (index : Nat) (truth : Bool) :
    .choice index truth ∉ assignmentSlackItems formula assignment := by
  simp [assignmentSlackItems]

theorem assignmentChoiceItems_subset (formula : CNF)
    (assignment : Nat → Bool) :
    assignmentChoiceItems formula assignment ⊆
      variableItems (reductionVariableCount formula) := by
  intro item hitem
  cases item with
  | choice index truth =>
      exact variable_mem_variableItems_iff _ _ _ |>.2
        ((choice_mem_assignmentChoiceItems_iff formula assignment index truth).1 hitem).1
  | slack clause slot =>
      exact (slack_not_mem_assignmentChoiceItems formula assignment clause slot hitem).elim

theorem assignmentSlackItems_subset (formula : CNF)
    (assignment : Nat → Bool) :
    assignmentSlackItems formula assignment ⊆ slackItems formula.length := by
  intro item hitem
  cases item with
  | choice index truth =>
      exact (choice_not_mem_assignmentSlackItems formula assignment index truth hitem).elim
  | slack clause slot =>
      have hmem := (slack_mem_assignmentSlackItems_iff
        formula assignment clause slot).1 hitem
      exact (slack_mem_slackItems_iff _ _ _).2 ⟨hmem.1, hmem.2.1⟩

theorem assignmentItems_subset (formula : CNF) (assignment : Nat → Bool) :
    assignmentItems formula assignment ⊆ reductionItems formula := by
  intro item hitem
  rcases Finset.mem_union.mp hitem with hchoice | hslack
  · exact Finset.mem_union_left _
      (assignmentChoiceItems_subset formula assignment hchoice)
  · exact Finset.mem_union_right _
      (assignmentSlackItems_subset formula assignment hslack)

theorem assignmentChoiceItems_disjoint_assignmentSlackItems
    (formula : CNF) (assignment : Nat → Bool) :
    Disjoint (assignmentChoiceItems formula assignment)
      (assignmentSlackItems formula assignment) := by
  rw [Finset.disjoint_left]
  intro item hchoice hslack
  cases item with
  | choice index truth =>
      exact choice_not_mem_assignmentSlackItems formula assignment index truth hslack
  | slack clause slot =>
      exact slack_not_mem_assignmentChoiceItems formula assignment clause slot hchoice

end CLRS.Chapter34.SubsetSumReduction
