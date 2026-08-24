import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Reduction.Construction
import Mathlib.Tactic

/-! # Computable canonical item order for the SUBSET-SUM reduction -/

namespace CLRS.Chapter34.SubsetSumReduction

/-- Two stable choice labels per variable, grouped by truth value. -/
def variableItemList (variableCount : Nat) : List SubsetSumItem :=
  (List.range variableCount).map (fun index => .choice index false) ++
    (List.range variableCount).map (fun index => .choice index true)

/-- Three stable unit-slack labels per clause, grouped by slot. -/
def slackItemList (clauseCount : Nat) : List SubsetSumItem :=
  (List.range clauseCount).map (fun clause => .slack clause 0) ++
    (List.range clauseCount).map (fun clause => .slack clause 1) ++
    (List.range clauseCount).map (fun clause => .slack clause 2)

/-- Complete computable item enumeration for the textbook construction. -/
def reductionItemList (formula : CNF) : List SubsetSumItem :=
  variableItemList (cnfVarCount formula) ++ slackItemList formula.length

@[simp] theorem choice_mem_variableItemList_iff
    (variableCount index : Nat) (truth : Bool) :
    .choice index truth ∈ variableItemList variableCount ↔
      index < variableCount := by
  cases truth <;> simp [variableItemList]

@[simp] theorem slack_mem_slackItemList_iff
    (clauseCount clause slot : Nat) :
    .slack clause slot ∈ slackItemList clauseCount ↔
      clause < clauseCount ∧ slot < 3 := by
  simp [slackItemList]
  omega

@[simp] theorem choice_not_mem_slackItemList
    (clauseCount index : Nat) (truth : Bool) :
    .choice index truth ∉ slackItemList clauseCount := by
  simp [slackItemList]

@[simp] theorem slack_not_mem_variableItemList
    (variableCount clause slot : Nat) :
    .slack clause slot ∉ variableItemList variableCount := by
  simp [variableItemList]

theorem variableItemList_nodup (variableCount : Nat) :
    (variableItemList variableCount).Nodup := by
  rw [variableItemList, List.nodup_append]
  refine ⟨List.nodup_range.map_on (by simp),
    List.nodup_range.map_on (by simp), ?_⟩
  intro left hleft right hright heq
  simp only [List.mem_map] at hleft hright
  rcases hleft with ⟨leftIndex, _, rfl⟩
  rcases hright with ⟨rightIndex, _, rfl⟩
  cases heq

theorem slackItemList_nodup (clauseCount : Nat) :
    (slackItemList clauseCount).Nodup := by
  have hzero :
      ((List.range clauseCount).map
        (fun clause => SubsetSumItem.slack clause 0)).Nodup :=
    List.nodup_range.map_on (by simp)
  have hone :
      ((List.range clauseCount).map
        (fun clause => SubsetSumItem.slack clause 1)).Nodup :=
    List.nodup_range.map_on (by simp)
  have htwo :
      ((List.range clauseCount).map
        (fun clause => SubsetSumItem.slack clause 2)).Nodup :=
    List.nodup_range.map_on (by simp)
  rw [slackItemList, List.nodup_append]
  refine ⟨?_, htwo, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hzero, hone, ?_⟩
    intro left hleft right hright heq
    simp only [List.mem_map] at hleft hright
    rcases hleft with ⟨leftClause, _, rfl⟩
    rcases hright with ⟨rightClause, _, rfl⟩
    cases heq
  · intro left hleft right hright heq
    simp only [List.mem_append, List.mem_map] at hleft
    simp only [List.mem_map] at hright
    rcases hright with ⟨rightClause, _, rfl⟩
    rcases hleft with hleft | hleft
    · rcases hleft with ⟨leftClause, _, rfl⟩
      cases heq
    · rcases hleft with ⟨leftClause, _, rfl⟩
      cases heq

theorem reductionItemList_nodup (formula : CNF) :
    (reductionItemList formula).Nodup := by
  rw [reductionItemList, List.nodup_append]
  refine ⟨variableItemList_nodup _, slackItemList_nodup _, ?_⟩
  intro left hleft right hright heq
  cases left with
  | choice index truth =>
      cases right with
      | choice rightIndex rightTruth =>
          exact (choice_not_mem_slackItemList _ _ _ hright).elim
      | slack clause slot => cases heq
  | slack clause slot =>
      exact (slack_not_mem_variableItemList _ _ _ hleft).elim

theorem mem_reductionItemList_iff (formula : CNF)
    (item : SubsetSumItem) :
    item ∈ reductionItemList formula ↔ item ∈ reductionItems formula := by
  cases item <;> simp [reductionItemList, reductionItems]

end CLRS.Chapter34.SubsetSumReduction
