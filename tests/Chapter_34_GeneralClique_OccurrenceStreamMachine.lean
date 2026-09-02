import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Occurrences

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.TMClique

example (input : List CNFSym) :
    canonicalOccurrenceStream input = relabel (encCNF (decodeCNF input)) :=
  canonicalOccurrenceStream_eq input

#check canonicalOccurrenceStream_computableInPolyTime

end CLRS.Chapter34.Turing.TMClique
