import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranchComplete

/-!
# Padding predicate for linear prefixes ending in a terminal branch

The predicate mirrors the statement spine.  At its branch leaf it retains
the current-row capacity plus the already established recursive padding of
both branch-free arms.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Capacity invariant required to evaluate a prefix-terminal-branch plan. -/
def transitionStmtPrefixTerminalBranchPadding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) → Prop
  | _, halt, _ => False
  | _, goto _, _ => False
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      (∀ k, 2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtPrefixTerminalBranchPadding tm seed
        (context.afterLoad tm update) continuation hcontinuation
  | context, push k emit continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtPrefixTerminalBranchPadding tm seed
        (context.afterPush tm k table) continuation hcontinuation
  | context, peek k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtPrefixTerminalBranchPadding tm seed
        (context.afterPeek tm k update) continuation hcontinuation
  | context, pop k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtPrefixTerminalBranchPadding tm seed
        (context.afterPop tm k update) continuation hcontinuation
  | context, branch test whenTrue whenFalse, hsupport =>
      (∀ k, 2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtLinearContextPadding tm seed
        (transitionStmtBranchTrueContext tm context test) whenTrue
        (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
          hsupport) ∧
      transitionStmtLinearContextPadding tm seed
        (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
        (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
          hsupport)

end CLRS.Chapter34.Turing.CookLevin
