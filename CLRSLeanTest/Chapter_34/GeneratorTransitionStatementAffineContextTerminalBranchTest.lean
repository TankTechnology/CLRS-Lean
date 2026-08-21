import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranch

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2.Stmt

#check transitionStmtTerminalBranchPlan
#check transitionStmtTerminalBranchPlan_isSome_iff
#check transitionStmtTerminalBranchPlan_fixedPhaseForms_eval

example (tm : _root_.Turing.FinTM2)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (hsupport : ∀ k, stmtPushSet tm (.branch test .halt .halt) k ⊆
      reachableAlphabet tm k) :
    (transitionStmtTerminalBranchPlan tm labelOffset context test .halt .halt
      hsupport).isSome := by
  rw [transitionStmtTerminalBranchPlan_isSome_iff]
  simp [transitionStmtTerminalLayout]

end CLRS.Chapter34.Turing.CookLevin
