import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRows

namespace CLRS.Chapter34.Turing.TMClique

#check canonicalIndexedOccurrenceRows_eq
#check encodeIndexedOccurrenceRows_eq_indexedOccurrences
#check canonicalIndexedOccurrenceRows_computableInPolyTime
#check canonicalIndexedOccurrenceRowsMachine_outputs

private def formula : CNF :=
  [[Literal.pos 0, Literal.neg 2], [Literal.pos 1]]

example : canonicalIndexedOccurrenceRows (encCNF formula) =
    encodeIndexedOccurrenceRows formula := by
  native_decide

end CLRS.Chapter34.Turing.TMClique
