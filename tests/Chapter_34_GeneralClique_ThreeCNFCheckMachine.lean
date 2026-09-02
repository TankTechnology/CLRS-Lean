import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.ThreeCNFCheck

namespace CLRS.Chapter34.Turing.TMClique

#check canonicalThreeCNFFlag_eq
#check canonicalThreeCNFFlag_computableInPolyTime

private def validFormula : CNF :=
  [[Literal.pos 0, Literal.neg 1, Literal.pos 2], [Literal.neg 0]]

private def invalidFormula : CNF :=
  [[Literal.pos 0, Literal.pos 1, Literal.pos 2, Literal.pos 3]]

example : canonicalThreeCNFFlag (encCNF validFormula) = [true] := by
  native_decide

example : canonicalThreeCNFFlag (encCNF invalidFormula) = [false] := by
  native_decide

example : canonicalThreeCNFFlag
    [.posMark, .clauseMark, .negMark, .varMark, .endMark] = [true] := by
  native_decide

end CLRS.Chapter34.Turing.TMClique
