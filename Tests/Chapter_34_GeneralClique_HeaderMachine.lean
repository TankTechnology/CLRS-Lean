import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Header

open CLRS.Chapter34

namespace CLRS.Chapter34.Turing.TMClique

private def sampleFormula : CNF :=
  [[Literal.pos 0, Literal.neg 1], [Literal.pos 2]]

example : canonicalCliqueHeader (encCNF sampleFormula) =
    CliqueSym.instanceMark ::
      prependCliqueTicks 3
        (CliqueSym.fieldSep :: prependCliqueTicks 2 [.fieldSep]) := by
  native_decide

#check canonicalCliqueHeader_computableInPolyTime

end CLRS.Chapter34.Turing.TMClique
