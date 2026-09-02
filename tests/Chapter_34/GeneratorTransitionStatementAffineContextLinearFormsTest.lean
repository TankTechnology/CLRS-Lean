import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearForms

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2.Stmt

example (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (update : tm.σ → tm.σ)
    (hsupport : ∀ k, stmtPushSet tm (.load update .halt) k ⊆
      reachableAlphabet tm k) :
    (transitionStmtLinearContextPhaseForms tm labelOffset context
      (.load update .halt) hsupport).isSome := by
  rw [transitionStmtLinearContextPhaseForms_isSome_iff_terminal]
  simp [transitionStmtTerminalLayout]

example (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (hsupport : ∀ k, stmtPushSet tm (.branch test .halt .halt) k ⊆
      reachableAlphabet tm k) :
    transitionStmtLinearContextPhaseForms tm labelOffset context
      (.branch test .halt .halt) hsupport = none := by
  rfl

end CLRS.Chapter34.Turing.CookLevin
