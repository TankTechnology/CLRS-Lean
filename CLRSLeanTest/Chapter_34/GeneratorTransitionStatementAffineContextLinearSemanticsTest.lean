import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearSemantics

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

example (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hpadding : transitionStmtLinearContextPadding tm seed context q hsupport)
    (forms : List TransitionAffineStmtPhaseForm)
    (hforms : transitionStmtLinearContextPhaseForms tm labelOffset context q
      hsupport = some forms) :
    forms.map (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionStmtScript tm (workHeight tm seed.height) seed.start
        (seed.start + 1)
        ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height))
        (context.rowWires tm seed labelOffset) q hsupport := by
  exact transitionStmtLinearContextPhaseForms_eval tm seed labelOffset context
    q hsupport hpadding forms hforms

end CLRS.Chapter34.Turing.CookLevin
