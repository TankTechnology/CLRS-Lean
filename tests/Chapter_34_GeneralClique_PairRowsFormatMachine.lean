import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRowsFormat

namespace CLRS.Chapter34.Turing.TMClique

#check pairRowsFormatMachine_outputs
#check completePairEdgeStream_eq_normalizedPairs
#check canonicalCompletePairEdgeStream_computableInPolyTime

private def formula : CNF :=
  [[Literal.pos 0, Literal.neg 1], [Literal.pos 2]]

example : canonicalCompletePairEdgeStream (encCNF formula) =
    (normalizedPairs 3).flatMap encodeCliqueEdge := by
  native_decide

end CLRS.Chapter34.Turing.TMClique
