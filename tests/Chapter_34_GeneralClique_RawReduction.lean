import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Encoding

namespace CLRS.Chapter34

#check noCliqueInstance
#check noCliqueInstance_wellFormed
#check noCliqueInstance_not_hasClique
#check guardedOccurrenceCliqueInstance
#check guardedOccurrenceCliqueInstance_eq_of_threeCNF
#check guardedOccurrenceCliqueInstance_not_wellFormed_of_not_threeCNF
#check threeCNFToGeneralCliqueMap
#check threeCNFToGeneralCliqueMap_mem_iff
#check threeCNFToGeneralCliqueMap_length

private def oneClause : CNF := [[Literal.pos 0]]

private def tooWide : CNF :=
  [[Literal.pos 0, Literal.pos 1, Literal.pos 2, Literal.pos 3]]

example : threeCNFToGeneralCliqueMap (encCNF oneClause) =
    encodeCliqueInstance (occurrenceCliqueInstance oneClause) := by
  native_decide

example : threeCNFToGeneralCliqueMap (encCNF tooWide) =
    encodeCliqueInstance (guardedOccurrenceCliqueInstance tooWide) := by
  native_decide

end CLRS.Chapter34
