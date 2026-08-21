import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextPopBlock

namespace CLRS.Chapter34.Turing.CookLevin

example (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) (k : tm.K)
    (update : tm.σ → Option (tm.Γ k) → tm.σ)
    (hheight : 1 ≤ seed.height) :
    (transitionStmtContextPopPhaseForms tm labelOffset
        (TransitionStmtAffineContext.initial tm) k update).map
        (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionStmtContextPopPhaseBlock tm seed labelOffset
        (TransitionStmtAffineContext.initial tm) k update := by
  apply transitionStmtContextPopPhaseForms_eval
  simpa [TransitionStmtAffineContext.initial,
    transitionStmtStackActionsFor] using hheight

end CLRS.Chapter34.Turing.CookLevin
