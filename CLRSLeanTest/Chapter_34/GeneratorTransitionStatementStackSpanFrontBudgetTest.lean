import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackSpanFrontBudget

namespace CLRS.Chapter34.Turing.CookLevin

example (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
      TransitionStackAffineRouteSpanBlock.identity []).heightSpan.removalCount =
      0 := by
  rfl

end CLRS.Chapter34.Turing.CookLevin
