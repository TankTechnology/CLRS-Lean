import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextOutputRouteSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveLinearRouteSources

/-!
# Recursive-plan closure for complete statement output routes

The recursive plan already carries uniform endpoint bounds at every terminal
leaf.  This module proves that a successful top-level linear normalization
selects exactly one of those leaves.  Consequently the plan invariant is
sufficient to instantiate the unified total-route source for an arbitrary
recursive substatement.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A successful linear normalization selects the terminal result stored at
the end of the corresponding recursive plan spine. -/
theorem transitionStmtRecursivePlan_linearResult_routeBounds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
      (result : TransitionStmtLinearResult tm),
      transitionStmtLinearResult tm context q hsupport = some result →
      (transitionStmtRecursivePlan tm labelOffset context q
        hsupport).LinearRouteBounds tm seed labelOffset →
      result.RouteBounds tm seed labelOffset := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport result hresult hplan
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      simpa only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds] using hplan
  | goto jump =>
      intro hsupport result hresult hplan
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      simpa only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds] using hplan
  | load update continuation ih =>
      intro hsupport result hresult hplan
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearResult] at hresult
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds] at hplan
      exact ih (context.afterLoad tm update) hcontinuation result hresult hplan
  | push selected emit continuation ih =>
      intro hsupport result hresult hplan
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm selected :=
        fun code =>
          ⟨emit ((stateEquivFin tm).symm code), by
            apply hsupport selected
            simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      simp only [transitionStmtLinearResult] at hresult
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds] at hplan
      change transitionStmtLinearResult tm
          (context.afterPush tm selected table) continuation hcontinuation =
        some result at hresult
      change (transitionStmtRecursivePlan tm labelOffset
          (context.afterPush tm selected table) continuation
            hcontinuation).LinearRouteBounds tm seed labelOffset at hplan
      exact ih (context.afterPush tm selected table) hcontinuation result
        hresult hplan
  | peek selected update continuation ih =>
      intro hsupport result hresult hplan
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearResult] at hresult
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds] at hplan
      exact ih (context.afterPeek tm selected update) hcontinuation result
        hresult hplan
  | pop selected update continuation ih =>
      intro hsupport result hresult hplan
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearResult] at hresult
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds] at hplan
      exact ih (context.afterPop tm selected update) hcontinuation result
        hresult hplan
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport result hresult hplan
      simp [transitionStmtLinearResult] at hresult

/-- Uniform recursive-plan bounds specialize back to the pointwise plan
invariant for any raw input and emitted transition seed. -/
theorem TransitionStmtRecursivePlan.linearRouteBounds_of_uniform
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtRecursivePlan W.machine.tm)
    (hbounds : plan.UniformLinearRouteBounds W labelOffset)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    plan.LinearRouteBounds W.machine.tm seed labelOffset := by
  induction plan with
  | terminal forms result => exact hbounds input seed hseed
  | «prefix» forms continuation ih => exact ih hbounds
  | branch context test whenTrue whenFalse predicateForms truePlan
      falsePlan ihTrue ihFalse =>
      exact ⟨ihTrue hbounds.1, ihFalse hbounds.2⟩

/-- Uniform recursive-plan bounds are sufficient to obtain a concrete
raw-input source for the complete semantic output row of the represented
statement. -/
noncomputable def
    verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k)
    (hbounds : (transitionStmtRecursivePlan W.machine.tm labelOffset context q
      hsupport).UniformLinearRouteBounds W labelOffset) :
    _root_.Turing.TM2ComputableInPolyTime id
      PolyBuilder.encodeUnaryFrameMarkedRowFamily
      (verifierTransitionStmtOutputRouteFamily W labelOffset context q
        hsupport) := by
  apply verifierTransitionStmtOutputRouteFamily_computableInPolyTime
  intro input seed hseed result hresult
  apply transitionStmtRecursivePlan_linearResult_routeBounds W.machine.tm
    seed labelOffset context q hsupport result hresult
  exact (transitionStmtRecursivePlan W.machine.tm labelOffset context q
    hsupport).linearRouteBounds_of_uniform W labelOffset hbounds input seed
      hseed

/-- The existing all-leaf theorem now closes the unified complete-route
source of every fixed verifier program label through the recursive plan. -/
noncomputable def
    verifierTransitionLabelOutputRouteFamily_computableInPolyTime_of_recursivePlan
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    _root_.Turing.TM2ComputableInPolyTime id
      PolyBuilder.encodeUnaryFrameMarkedRowFamily
      (verifierTransitionStmtOutputRouteFamily W labelOffset
        (TransitionStmtAffineContext.initial W.machine.tm)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label)) := by
  apply
    verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
  exact verifierTransitionRecursivePlan_uniformLinearRouteBounds W
    labelOffset label

end CLRS.Chapter34.Turing.CookLevin
