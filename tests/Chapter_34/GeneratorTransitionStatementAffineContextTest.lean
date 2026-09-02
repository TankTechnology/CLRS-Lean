import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContext

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

example (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (k : tm.K) :
    (TransitionStmtAffineContext.initial tm).stackRoute tm labelOffset k =
      TransitionStackAffineRouteSpanBlock.identity := by
  simp

example (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) :
    affineUnaryTripleFormValue
        (context.startForm tm labelOffset)
        (transitionTailAffineSeed seed) =
      (seed.start + labelOffset.eval seed.height) +
        context.gateOffset.eval (workHeight tm seed.height) := by
  exact context.startForm_value tm seed labelOffset

end CLRS.Chapter34.Turing.CookLevin
