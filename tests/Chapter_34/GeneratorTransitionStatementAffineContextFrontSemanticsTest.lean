import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextFrontSemantics

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

example (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) (k : tm.K)
    (code : Fin ((reachableAlphabet tm k).card + 1))
    (hheight : 1 ≤ seed.height) :
    affineUnaryTripleFormValue
        ((TransitionStmtAffineContext.initial tm).stackCellFrontForm tm
          labelOffset k code)
        (transitionTailAffineSeed seed) =
      arithmeticPeekCfgWires tm (workHeight tm seed.height)
        seed.start (seed.start + 1)
        ((TransitionStmtAffineContext.initial tm).rowWires tm seed labelOffset)
        k code := by
  apply TransitionStmtAffineContext.stackCellFrontForm_value
  simpa [TransitionStmtAffineContext.initial,
    transitionStmtStackActionsFor] using hheight

end CLRS.Chapter34.Turing.CookLevin
