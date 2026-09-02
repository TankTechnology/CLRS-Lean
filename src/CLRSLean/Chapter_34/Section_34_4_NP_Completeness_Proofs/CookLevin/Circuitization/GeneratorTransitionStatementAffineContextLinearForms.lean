import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextPopBlock

/-!
# Recursive affine forms for branch-free statement spines

The non-branching constructors now form one complete recursive generator.
Each primitive is emitted from the current context and the continuation is
compiled from the exact context update proved in the preceding modules.
Branch arms are deliberately handled by a separate mux module.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Complete affine controller phases for a statement spine ending in `halt`
or `goto`.  A branch returns `none`, leaving its two arms and final mux to the
branch compiler. -/
noncomputable def transitionStmtLinearContextPhaseForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      Option (List TransitionAffineStmtPhaseForm)
  | _, halt, _ => some []
  | context, goto jump, hsupport =>
      some ((transitionStmtContextHeadPhaseForm tm labelOffset context
        (.goto jump) hsupport).toList)
  | context, load update continuation, hsupport =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtLinearContextPhaseForms tm labelOffset
        (context.afterLoad tm update) continuation hcontinuation).map
          ((transitionStmtContextHeadPhaseForm tm labelOffset context
            (.load update continuation) hsupport).toList ++ ·)
  | context, push k emit continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      (transitionStmtLinearContextPhaseForms tm labelOffset
        (context.afterPush tm k table) continuation hcontinuation).map
          ((transitionStmtContextHeadPhaseForm tm labelOffset context
            (.push k emit continuation) hsupport).toList ++ ·)
  | context, peek k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtLinearContextPhaseForms tm labelOffset
        (context.afterPeek tm k update) continuation hcontinuation).map
          ((transitionStmtContextHeadPhaseForm tm labelOffset context
            (.peek k update continuation) hsupport).toList ++ ·)
  | context, pop k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtLinearContextPhaseForms tm labelOffset
        (context.afterPop tm k update) continuation hcontinuation).map
          (transitionStmtContextPopPhaseForms tm labelOffset context k update ++ ·)
  | _, branch _ _ _, _ => none

/-- The recursive affine generator is defined exactly on branch-free terminal
spines, matching the older terminal-layout recognizer. -/
theorem transitionStmtLinearContextPhaseForms_isSome_iff_terminal
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (transitionStmtLinearContextPhaseForms tm labelOffset context q
      hsupport).isSome ↔
      (transitionStmtTerminalLayout tm q).isSome := by
  induction q generalizing context with
  | halt => simp [transitionStmtLinearContextPhaseForms,
      transitionStmtTerminalLayout]
  | goto jump => simp [transitionStmtLinearContextPhaseForms,
      transitionStmtTerminalLayout]
  | load update continuation ih =>
      simp [transitionStmtLinearContextPhaseForms,
        transitionStmtTerminalLayout, ih]
  | push k emit continuation ih =>
      simp [transitionStmtLinearContextPhaseForms,
        transitionStmtTerminalLayout, ih]
  | peek k update continuation ih =>
      simp [transitionStmtLinearContextPhaseForms,
        transitionStmtTerminalLayout, ih]
  | pop k update continuation ih =>
      simp [transitionStmtLinearContextPhaseForms,
        transitionStmtTerminalLayout, ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtLinearContextPhaseForms,
        transitionStmtTerminalLayout]

end CLRS.Chapter34.Turing.CookLevin
