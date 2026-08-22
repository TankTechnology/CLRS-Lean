import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Instance

namespace CLRS.Chapter34

#check IndexedOccurrence
#check indexedOccurrences
#check indexedOccurrenceAt?
#check occurrenceCliqueInstance_wellFormed
#check occurrenceCliqueInstance_adj_iff

private def repeatedInOneClause : CNF :=
  [[Literal.pos 0, Literal.pos 0]]

private def repeatedAcrossClauses : CNF :=
  [[Literal.pos 0], [Literal.pos 0]]

private def complementaryAcrossClauses : CNF :=
  [[Literal.pos 0], [Literal.neg 0]]

example : (indexedOccurrences repeatedInOneClause).length = 2 := by
  native_decide

example : indexedOccurrenceAt? repeatedInOneClause 0 = some
    { clauseIndex := 0, positionIndex := 0, literal := Literal.pos 0 } := by
  native_decide

example : indexedOccurrenceAt? repeatedInOneClause 1 = some
    { clauseIndex := 0, positionIndex := 1, literal := Literal.pos 0 } := by
  native_decide

example : (occurrenceCliqueInstance repeatedInOneClause).edges = [] := by
  native_decide

example : (occurrenceCliqueInstance repeatedAcrossClauses).edges = [(0, 1)] := by
  native_decide

example : (occurrenceCliqueInstance complementaryAcrossClauses).edges = [] := by
  native_decide

example : (occurrenceCliqueInstance repeatedAcrossClauses).WellFormed := by
  native_decide

end CLRS.Chapter34
