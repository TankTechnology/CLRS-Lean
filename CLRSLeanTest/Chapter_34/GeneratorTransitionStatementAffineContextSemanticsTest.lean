import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextSemantics

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

example (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (target : Fin (stateCount tm)) :
    affineUnaryTripleFormValue
        (context.stateForm tm labelOffset target)
        (transitionTailAffineSeed seed) =
      (context.wires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)).state
        target := by
  exact context.stateForm_eq_wires tm seed labelOffset target

end CLRS.Chapter34.Turing.CookLevin
