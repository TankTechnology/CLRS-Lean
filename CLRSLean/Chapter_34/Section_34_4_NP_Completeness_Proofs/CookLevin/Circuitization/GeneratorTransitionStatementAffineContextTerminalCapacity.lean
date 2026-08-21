import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextPrefixTerminalBranch

/-!
# Capacity inherited by normalized terminal branch arms

The recursive padding predicate already tracks every context reached by a
branch-free statement.  This file exposes its final consequence directly on
`TransitionStmtLinearResult`, eliminating the local route-capacity hypotheses
from later branch-mux assembly.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A normalized branch-free result retains the terminal capacity guaranteed
by the recursive padding predicate. -/
theorem transitionStmtLinearResult_capacity_of_padding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      transitionStmtLinearContextPadding tm seed context q hsupport →
      ∀ (result : TransitionStmtLinearResult tm),
        transitionStmtLinearResult tm context q hsupport = some result →
        ∀ k,
          2 * (transitionStmtStackActionsFor tm k
            result.context.stackActions).length + 1 ≤ seed.height := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hpadding result hresult
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      exact hpadding
  | goto jump =>
      intro hsupport hpadding result hresult
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      exact hpadding
  | load update continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih (context.afterLoad tm update) _ htail result hresult
  | push selected emit continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih _ _ htail result hresult
  | peek selected update continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih (context.afterPeek tm selected update) _ htail result hresult
  | pop selected update continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih (context.afterPop tm selected update) _ htail result hresult
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hpadding
      exact False.elim hpadding

/-- Both routed rows in a successful terminal branch plan automatically fit
the widened workspace whenever their recursive arm paddings hold. -/
theorem transitionStmtTerminalBranchPlan_capacities_of_padding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (htruePadding : transitionStmtLinearContextPadding tm seed
      (transitionStmtBranchTrueContext tm context test) whenTrue
      (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport))
    (hfalsePadding : transitionStmtLinearContextPadding tm seed
      (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
      (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
        hsupport)) :
    (∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) ∧
      (∀ k,
        2 * (transitionStmtStackActionsFor tm k
          plan.falseResult.context.stackActions).length + 1 ≤
          workHeight tm seed.height) := by
  have hresults := transitionStmtTerminalBranchPlan_results tm labelOffset
    context test whenTrue whenFalse hsupport plan hplan
  have htrue := transitionStmtLinearResult_capacity_of_padding tm seed
    (transitionStmtBranchTrueContext tm context test) whenTrue
    (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport)
    htruePadding plan.trueResult hresults.1
  have hfalse := transitionStmtLinearResult_capacity_of_padding tm seed
    (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
    (transitionStmtBranchFalseSupport tm test whenTrue whenFalse hsupport)
    hfalsePadding plan.falseResult hresults.2
  constructor
  · intro k
    exact (htrue k).trans (by simp [workHeight])
  · intro k
    exact (hfalse k).trans (by simp [workHeight])

end CLRS.Chapter34.Turing.CookLevin
