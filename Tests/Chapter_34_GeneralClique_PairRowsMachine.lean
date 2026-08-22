import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRows

namespace CLRS.Chapter34.Turing.TMClique

#check canonicalOccurrencePairRowSeed_eq
#check canonicalOccurrencePairRows_eq
#check canonicalOccurrencePairRows_computableInPolyTime

private def formula : CNF :=
  [[Literal.pos 0, Literal.neg 1], [Literal.pos 2]]

example : canonicalOccurrencePairRows (encCNF formula) =
    [.frameEnd,
      .separator, .frameEnd,
      .separator, .tick, .separator, .frameEnd] := by
  native_decide

end CLRS.Chapter34.Turing.TMClique
