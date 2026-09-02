import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.FlaggedOccurrences

namespace CLRS.Chapter34.Turing.TMClique

#check canonicalFlaggedOccurrenceStream_eq
#check canonicalFlaggedOccurrenceStream_computableInPolyTime

private def validFormula : CNF :=
  [[Literal.pos 0, Literal.neg 1], [Literal.pos 2]]

private def invalidFormula : CNF :=
  [[Literal.pos 0, Literal.pos 1, Literal.pos 2, Literal.pos 3]]

example : (canonicalFlaggedOccurrenceStream (encCNF validFormula)).head? =
    some (.flag true) := by
  native_decide

example : (canonicalFlaggedOccurrenceStream (encCNF invalidFormula)).head? =
    some (.flag false) := by
  native_decide

example : (canonicalFlaggedOccurrenceStream
    [.posMark, .clauseMark, .negMark, .varMark, .endMark]).head? =
      some (.flag true) := by
  native_decide

end CLRS.Chapter34.Turing.TMClique
