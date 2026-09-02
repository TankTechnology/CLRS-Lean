import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Semantics

namespace CLRS.Chapter34

#check hasCliqueOn_iff_occurrenceCliqueInstance
#check cnfSatisfiable_iff_occurrenceCliqueInstance
#check occurrenceCliqueInstance_wellFormed_of_cnfSatisfiable

private def satisfiableFormula : CNF :=
  [[Literal.pos 0], [Literal.pos 1, Literal.neg 0]]

private def contradictoryFormula : CNF :=
  [[Literal.pos 0], [Literal.neg 0]]

private def emptyClauseFormula : CNF :=
  [[]]

example : (occurrenceCliqueInstance satisfiableFormula).HasClique := by
  apply (cnfSatisfiable_iff_occurrenceCliqueInstance satisfiableFormula).mp
  refine ⟨fun _ => true, ?_⟩
  simp [evalCNF, satisfiableFormula, evalClause, evalLit]

example : ¬ (occurrenceCliqueInstance contradictoryFormula).HasClique := by
  intro hclique
  rcases (cnfSatisfiable_iff_occurrenceCliqueInstance
      contradictoryFormula).mpr hclique with ⟨assignment, hassignment⟩
  have hpositive := hassignment [Literal.pos 0] (by simp [contradictoryFormula])
  have hnegative := hassignment [Literal.neg 0] (by simp [contradictoryFormula])
  simp [evalClause, evalLit] at hpositive hnegative
  simp_all

example : ¬ (occurrenceCliqueInstance emptyClauseFormula).HasClique := by
  intro hclique
  rcases (cnfSatisfiable_iff_occurrenceCliqueInstance
      emptyClauseFormula).mpr hclique with ⟨assignment, hassignment⟩
  have hempty := hassignment [] (by simp [emptyClauseFormula])
  simp [evalClause] at hempty

end CLRS.Chapter34
