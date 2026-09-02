import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearResultBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBudget

/-!
# Route bounds for every leaf of a recursive statement plan

The push budget is preserved by primitive context updates and is split across
both sides of a branch using the `max` in `stmtMaxPushes`.  Together with the
recursive public-row padding theorem this proves that every terminal leaf in
the total plan can use the concrete affine-span source.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Every normalized terminal leaf in a recursive plan satisfies the compact
affine-span endpoint conditions. -/
def TransitionStmtRecursivePlan.LinearRouteBounds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    TransitionStmtRecursivePlan tm → Prop
  | .terminal _ result => result.RouteBounds tm seed labelOffset
  | .prefix _ continuation =>
      continuation.LinearRouteBounds tm seed labelOffset
  | .branch _ _ _ _ _ truePlan falsePlan =>
      truePlan.LinearRouteBounds tm seed labelOffset ∧
        falsePlan.LinearRouteBounds tm seed labelOffset

/-- A suffix-aware push budget and recursive padding establish route bounds
for every terminal leaf of the compiled plan. -/
theorem transitionStmtRecursivePlan_linearRouteBounds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      transitionStmtRecursiveContextPadding tm seed context q hsupport →
      (∀ k,
        transitionStmtStackActionPushCountFor tm k context.stackActions +
          stmtMaxPushes tm k q ≤ maxPushesPerStep tm) →
      (transitionStmtRecursivePlan tm labelOffset context q
        hsupport).LinearRouteBounds tm seed labelOffset := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hpadding hpushBudget
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds]
      exact transitionStmtRecursiveContextPadding_linearResult_routeBounds
        tm seed labelOffset context .halt hsupport hpadding hpushBudget
        { context, terminal := .halt } rfl
  | goto jump =>
      intro hsupport hpadding hpushBudget
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds]
      exact transitionStmtRecursiveContextPadding_linearResult_routeBounds
        tm seed labelOffset context (.goto jump) hsupport hpadding
        hpushBudget { context, terminal := .goto jump } rfl
  | load update continuation ih =>
      intro hsupport hpadding hpushBudget
      rcases hpadding with ⟨_, htailPadding⟩
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds]
      apply ih (context.afterLoad tm update) hcontinuation htailPadding
      intro k
      simpa [TransitionStmtAffineContext.afterLoad,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.replaceStateByMap,
        stmtMaxPushes] using hpushBudget k
  | push selected emit continuation ih =>
      intro hsupport hpadding hpushBudget
      rcases hpadding with ⟨_, htailPadding⟩
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
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds]
      change (transitionStmtRecursivePlan tm labelOffset
        (context.afterPush tm selected table) continuation
          hcontinuation).LinearRouteBounds tm seed labelOffset
      apply ih (context.afterPush tm selected table) hcontinuation
        htailPadding
      intro target
      have htarget := hpushBudget target
      simp only [stmtMaxPushes] at htarget
      simp only [TransitionStmtAffineContext.afterPush,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.recordPush,
        transitionStmtStackActionPushCountFor_append_singleton,
        TransitionStmtStackAction.pushCountFor]
      omega
  | peek selected update continuation ih =>
      intro hsupport hpadding hpushBudget
      rcases hpadding with ⟨_, htailPadding⟩
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds]
      apply ih (context.afterPeek tm selected update) hcontinuation
        htailPadding
      intro k
      simpa [TransitionStmtAffineContext.afterPeek,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.replaceStateByPairMap,
        stmtMaxPushes] using hpushBudget k
  | pop selected update continuation ih =>
      intro hsupport hpadding hpushBudget
      rcases hpadding with ⟨_, htailPadding⟩
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds]
      apply ih (context.afterPop tm selected update) hcontinuation
        htailPadding
      intro target
      have htarget := hpushBudget target
      simpa [TransitionStmtAffineContext.afterPop,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.replaceStateByPairMap,
        TransitionStmtAffineContext.recordPop,
        transitionStmtStackActionPushCountFor_append_singleton,
        TransitionStmtStackAction.pushCountFor,
        stmtMaxPushes] using htarget
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hpadding hpushBudget
      rcases hpadding with ⟨_, htruePadding, hfalsePadding⟩
      let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
        whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
        whenFalse hsupport
      simp only [transitionStmtRecursivePlan,
        TransitionStmtRecursivePlan.LinearRouteBounds]
      constructor
      · apply ihTrue (transitionStmtBranchTrueContext tm context test)
          htrueSupport htruePadding
        intro k
        have hk := hpushBudget k
        simp only [stmtMaxPushes] at hk
        simpa [transitionStmtBranchTrueContext,
          TransitionStmtAffineContext.advance] using
          (show transitionStmtStackActionPushCountFor tm k
                context.stackActions + stmtMaxPushes tm k whenTrue ≤
              maxPushesPerStep tm by omega)
      · apply ihFalse
          (transitionStmtBranchFalseContext tm context test whenTrue)
          hfalseSupport hfalsePadding
        intro k
        have hk := hpushBudget k
        simp only [stmtMaxPushes] at hk
        simpa [transitionStmtBranchFalseContext,
          TransitionStmtAffineContext.advance] using
          (show transitionStmtStackActionPushCountFor tm k
                context.stackActions + stmtMaxPushes tm k whenFalse ≤
              maxPushesPerStep tm by omega)

/-- For every verifier transition row and every program label, every leaf of
the total recursive plan is accepted by the concrete affine-span source. -/
theorem verifierTransitionRecursivePlan_linearRouteBounds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    (transitionStmtRecursivePlan W.machine.tm labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label)).LinearRouteBounds
        W.machine.tm seed labelOffset := by
  have hpadding := transitionStmtRecursiveContextPadding_initial_verifier
    W input seed hseed label
  apply transitionStmtRecursivePlan_linearRouteBounds W.machine.tm seed
    labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    hpadding
  intro k
  simpa [TransitionStmtAffineContext.initial,
    transitionStmtStackActionPushCountFor] using
    stmtMaxPushes_le_maxPushesPerStep W.machine.tm label k

end CLRS.Chapter34.Turing.CookLevin
