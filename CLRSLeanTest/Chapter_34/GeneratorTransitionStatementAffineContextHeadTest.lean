import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextHead

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2.Stmt

example (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (hsupport : ∀ k, stmtPushSet tm (.halt :
      _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) k ⊆
        reachableAlphabet tm k) :
    transitionStmtContextHeadPhaseForm tm labelOffset context .halt
      hsupport = none := by
  rfl

end CLRS.Chapter34.Turing.CookLevin
