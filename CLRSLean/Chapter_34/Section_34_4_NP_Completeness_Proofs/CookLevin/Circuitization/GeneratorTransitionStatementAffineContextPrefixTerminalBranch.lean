import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranchMuxSegments

/-!
# Linear prefixes ending in a terminal branch

Real TM2 statements need not begin with a branch: state and stack operations
may precede it.  This module walks that fixed linear spine, records its affine
phases and exact continuation context, and then attaches the verified
terminal-arm branch plan at the leaf.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A linear affine prefix together with its final branch whose two arms are
branch-free. -/
structure TransitionStmtPrefixTerminalBranchPlan
    (tm : _root_.Turing.FinTM2) where
  prefixForms : List TransitionAffineStmtPhaseForm
  branchContext : TransitionStmtAffineContext tm
  test : tm.σ → Bool
  whenTrue : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ
  whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ
  branchSupport : ∀ k,
    stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
      reachableAlphabet tm k
  branchPlan : TransitionStmtTerminalBranchPlan tm

/-- All fixed-width phases before the height-dependent final mux. -/
def TransitionStmtPrefixTerminalBranchPlan.fixedPhaseForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    List TransitionAffineStmtPhaseForm :=
  plan.prefixForms ++
    plan.branchPlan.fixedPhaseForms tm labelOffset plan.branchContext
      plan.test plan.whenTrue plan.whenFalse plan.branchSupport

/-- Static shape predicate recognized by this first branch layer. -/
def transitionStmtEndsInTerminalBranch
    (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Prop
  | halt => False
  | goto _ => False
  | load _ continuation => transitionStmtEndsInTerminalBranch tm continuation
  | push _ _ continuation => transitionStmtEndsInTerminalBranch tm continuation
  | peek _ _ continuation => transitionStmtEndsInTerminalBranch tm continuation
  | pop _ _ continuation => transitionStmtEndsInTerminalBranch tm continuation
  | branch _ whenTrue whenFalse =>
      (transitionStmtTerminalLayout tm whenTrue).isSome ∧
        (transitionStmtTerminalLayout tm whenFalse).isSome

/-- Compile a fixed linear prefix and its final branch with branch-free arms. -/
noncomputable def transitionStmtPrefixTerminalBranchPlan
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      Option (TransitionStmtPrefixTerminalBranchPlan tm)
  | _, halt, _ => none
  | _, goto _, _ => none
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtPrefixTerminalBranchPlan tm labelOffset
        (context.afterLoad tm update) continuation hcontinuation).map
          (fun plan => { plan with
            prefixForms :=
              (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.load update continuation) hsupport).toList ++
                plan.prefixForms })
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
      (transitionStmtPrefixTerminalBranchPlan tm labelOffset
        (context.afterPush tm k table) continuation hcontinuation).map
          (fun plan => { plan with
            prefixForms :=
              (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.push k emit continuation) hsupport).toList ++
                plan.prefixForms })
  | context, peek k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtPrefixTerminalBranchPlan tm labelOffset
        (context.afterPeek tm k update) continuation hcontinuation).map
          (fun plan => { plan with
            prefixForms :=
              (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.peek k update continuation) hsupport).toList ++
                plan.prefixForms })
  | context, pop k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtPrefixTerminalBranchPlan tm labelOffset
        (context.afterPop tm k update) continuation hcontinuation).map
          (fun plan => { plan with
            prefixForms := transitionStmtContextPopPhaseForms tm labelOffset
              context k update ++ plan.prefixForms })
  | context, branch test whenTrue whenFalse, hsupport =>
      (transitionStmtTerminalBranchPlan tm labelOffset context test whenTrue
        whenFalse hsupport).map fun branchPlan =>
          { prefixForms := []
            branchContext := context
            test := test
            whenTrue := whenTrue
            whenFalse := whenFalse
            branchSupport := hsupport
            branchPlan := branchPlan }

/-- The prefix compiler succeeds exactly on a linear spine ending in a branch
whose two arms are branch-free. -/
theorem transitionStmtPrefixTerminalBranchPlan_isSome_iff
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (transitionStmtPrefixTerminalBranchPlan tm labelOffset context q
      hsupport).isSome ↔ transitionStmtEndsInTerminalBranch tm q := by
  induction q generalizing context with
  | halt => simp [transitionStmtPrefixTerminalBranchPlan,
      transitionStmtEndsInTerminalBranch]
  | goto jump => simp [transitionStmtPrefixTerminalBranchPlan,
      transitionStmtEndsInTerminalBranch]
  | load update continuation ih =>
      simp [transitionStmtPrefixTerminalBranchPlan,
        transitionStmtEndsInTerminalBranch, ih]
  | push k emit continuation ih =>
      simp [transitionStmtPrefixTerminalBranchPlan,
        transitionStmtEndsInTerminalBranch, ih]
  | peek k update continuation ih =>
      simp [transitionStmtPrefixTerminalBranchPlan,
        transitionStmtEndsInTerminalBranch, ih]
  | pop k update continuation ih =>
      simp [transitionStmtPrefixTerminalBranchPlan,
        transitionStmtEndsInTerminalBranch, ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simpa [transitionStmtPrefixTerminalBranchPlan,
        transitionStmtEndsInTerminalBranch] using
        transitionStmtTerminalBranchPlan_isSome_iff tm labelOffset context
          test whenTrue whenFalse hsupport

end CLRS.Chapter34.Turing.CookLevin
