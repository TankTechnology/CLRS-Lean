import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.GuardedHeader

namespace CLRS.Chapter34.Turing.TMClique

#check canonicalGuardedCliqueHeader_eq
#check canonicalGuardedCliqueHeader_computableInPolyTime

private def validFormula : CNF :=
  [[Literal.pos 0, Literal.neg 1], [Literal.pos 2]]

private def invalidFormula : CNF :=
  [[Literal.pos 0, Literal.pos 1, Literal.pos 2, Literal.pos 3]]

example : canonicalGuardedCliqueHeader (encCNF validFormula) =
    [.instanceMark, .tick, .tick, .tick, .fieldSep,
      .tick, .tick, .fieldSep] := by
  native_decide

example : canonicalGuardedCliqueHeader (encCNF invalidFormula) =
    [.instanceMark, .tick, .tick, .tick, .tick, .fieldSep,
      .tick, .tick, .tick, .tick, .tick, .fieldSep] := by
  native_decide

end CLRS.Chapter34.Turing.TMClique
