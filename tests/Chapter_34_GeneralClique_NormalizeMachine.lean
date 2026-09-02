import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Normalize

open CLRS.Chapter34
open CLRS.Chapter34.Turing.PolyBuilder

namespace CLRS.Chapter34.Turing.TMClique

private def malformedSamples : List (List CNFSym) :=
  [ [],
    [.posMark, .varMark, .endMark],
    [.clauseMark],
    [.clauseMark, .posMark],
    [.clauseMark, .posMark, .varMark],
    [.clauseMark, .posMark, .varMark, .clauseMark],
    [.clauseMark, .negMark, .varMark, .endMark, .endMark,
      .varMark, .clauseMark, .endMark],
    [.varMark, .clauseMark, .posMark, .posMark, .endMark] ]

example :
    malformedSamples.all (fun input =>
      normalizeCNFInput input == encCNF (decodeCNF input)) := by
  native_decide

#check normalizeCNFInput_eq_encCNF_decodeCNF
#check normalizeCNFInput_computableInPolyTime

end CLRS.Chapter34.Turing.TMClique
