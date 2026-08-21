import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextBranchRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranchMux

/-!
# Recursive affine plans for arbitrary transition statements

The shallow compiler handled branch-free statements and one branch whose two
arms were branch-free.  This module removes that syntactic boundary.  Its plan
tree follows the actual `TM2.Stmt` recursion, preserves every affine prefix,
and recursively stores both arms of every branch.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A proof-oriented decomposition of an arbitrary TM2 statement.

`terminal` retains the normalized final row of a branch-free leaf, `prefix`
records one or more primitive phases before a continuation, and `branch`
stores the exact affine branch context together with recursively compiled
arms. -/
inductive TransitionStmtRecursivePlan (tm : _root_.Turing.FinTM2)
  | terminal
      (forms : List TransitionAffineStmtPhaseForm)
      (result : TransitionStmtLinearResult tm)
  | prefix
      (forms : List TransitionAffineStmtPhaseForm)
      (continuation : TransitionStmtRecursivePlan tm)
  | branch
      (context : TransitionStmtAffineContext tm)
      (test : tm.σ → Bool)
      (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (predicateForms : List TransitionAffineStmtPhaseForm)
      (truePlan falsePlan : TransitionStmtRecursivePlan tm)

/-- Number of whole-row branch muxes represented in a recursive plan. -/
def TransitionStmtRecursivePlan.branchCount
    {tm : _root_.Turing.FinTM2} : TransitionStmtRecursivePlan tm → Nat
  | .terminal _ _ => 0
  | .prefix _ continuation => continuation.branchCount
  | .branch _ _ _ _ _ truePlan falsePlan =>
      1 + truePlan.branchCount + falsePlan.branchCount

/-- Syntactic number of branch nodes in a TM2 statement. -/
def transitionStmtBranchCount (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Nat
  | halt => 0
  | goto _ => 0
  | load _ continuation => transitionStmtBranchCount tm continuation
  | push _ _ continuation => transitionStmtBranchCount tm continuation
  | peek _ _ continuation => transitionStmtBranchCount tm continuation
  | pop _ _ continuation => transitionStmtBranchCount tm continuation
  | branch _ whenTrue whenFalse =>
      1 + transitionStmtBranchCount tm whenTrue +
        transitionStmtBranchCount tm whenFalse

/-- Total recursive compiler for every supported TM2 statement.  Recursive
calls are made only on syntactic continuations or branch arms. -/
noncomputable def transitionStmtRecursivePlan
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      TransitionStmtRecursivePlan tm
  | context, halt, _ =>
      .terminal [] { context, terminal := .halt }
  | context, goto jump, hsupport =>
      .terminal
        ((transitionStmtContextHeadPhaseForm tm labelOffset context
          (.goto jump) hsupport).toList)
        { context, terminal := .goto jump }
  | context, load update continuation, hsupport =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      .prefix
        ((transitionStmtContextHeadPhaseForm tm labelOffset context
          (.load update continuation) hsupport).toList)
        (transitionStmtRecursivePlan tm labelOffset
          (context.afterLoad tm update) continuation hcontinuation)
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
      .prefix
        ((transitionStmtContextHeadPhaseForm tm labelOffset context
          (.push k emit continuation) hsupport).toList)
        (transitionStmtRecursivePlan tm labelOffset
          (context.afterPush tm k table) continuation hcontinuation)
  | context, peek k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      .prefix
        ((transitionStmtContextHeadPhaseForm tm labelOffset context
          (.peek k update continuation) hsupport).toList)
        (transitionStmtRecursivePlan tm labelOffset
          (context.afterPeek tm k update) continuation hcontinuation)
  | context, pop k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      .prefix
        (transitionStmtContextPopPhaseForms tm labelOffset context k update)
        (transitionStmtRecursivePlan tm labelOffset
          (context.afterPop tm k update) continuation hcontinuation)
  | context, branch test whenTrue whenFalse, hsupport =>
      let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
        whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
        whenFalse hsupport
      .branch context test whenTrue whenFalse
        ((transitionStmtContextHeadPhaseForm tm labelOffset context
          (.branch test whenTrue whenFalse) hsupport).toList)
        (transitionStmtRecursivePlan tm labelOffset
          (transitionStmtBranchTrueContext tm context test) whenTrue
          htrueSupport)
        (transitionStmtRecursivePlan tm labelOffset
          (transitionStmtBranchFalseContext tm context test whenTrue)
          whenFalse hfalseSupport)

/-- The total compiler represents every syntactic branch, including nested
branches in either arm. -/
theorem transitionStmtRecursivePlan_branchCount
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (transitionStmtRecursivePlan tm labelOffset context q
      hsupport).branchCount = transitionStmtBranchCount tm q := by
  induction q generalizing context with
  | halt => rfl
  | goto jump => rfl
  | load update continuation ih =>
      simp [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.branchCount,
        transitionStmtBranchCount, ih]
  | push k emit continuation ih =>
      simp [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.branchCount,
        transitionStmtBranchCount, ih]
  | peek k update continuation ih =>
      simp [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.branchCount,
        transitionStmtBranchCount, ih]
  | pop k update continuation ih =>
      simp [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.branchCount,
        transitionStmtBranchCount, ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.branchCount,
        transitionStmtBranchCount, ihTrue, ihFalse]

end CLRS.Chapter34.Turing.CookLevin
