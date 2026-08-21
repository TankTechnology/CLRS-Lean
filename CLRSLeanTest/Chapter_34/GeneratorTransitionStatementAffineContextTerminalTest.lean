import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminal

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2.Stmt

#check transitionStmtLinearResult
#check transitionStmtLinearResult_isSome_iff_terminal
#check transitionStmtLinearResult_outputWires

example (tm : _root_.Turing.FinTM2)
    (context : TransitionStmtAffineContext tm) (update : tm.σ → tm.σ)
    (hsupport : ∀ k, stmtPushSet tm (.load update .halt) k ⊆
      reachableAlphabet tm k) :
    (transitionStmtLinearResult tm context (.load update .halt)
      hsupport).isSome := by
  rw [transitionStmtLinearResult_isSome_iff_terminal]
  simp [transitionStmtTerminalLayout]

end CLRS.Chapter34.Turing.CookLevin
