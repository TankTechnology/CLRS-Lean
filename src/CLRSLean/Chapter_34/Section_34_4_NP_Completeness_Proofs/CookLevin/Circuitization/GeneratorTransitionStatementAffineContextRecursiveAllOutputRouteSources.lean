import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveOutputRouteSource

/-!
# Complete-route sources at every recursive statement node

The total-route compiler is now lifted through the syntax tree of a fixed
statement.  The resulting proposition records an actual raw-input source at
the current node and at every continuation and branch arm below it.  Thus a
parent mux can consume either arm through one uniform interface, regardless
of the arm's internal branch depth.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A fixed statement/context pair has a concrete complete-route source. -/
def TransitionStmtHasOutputRouteSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k) : Prop :=
  Nonempty (_root_.Turing.TM2ComputableInPolyTime id
    PolyBuilder.encodeUnaryFrameMarkedRowFamily
    (verifierTransitionStmtOutputRouteFamily W labelOffset context q
      hsupport))

/-- Complete-route source availability at every node of a statement's
recursive syntax tree. -/
noncomputable def transitionStmtRecursiveOutputRouteSources
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext W.machine.tm) →
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ) →
    (∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k) → Prop
  | context, halt, hsupport =>
      TransitionStmtHasOutputRouteSource W labelOffset context halt hsupport
  | context, goto jump, hsupport =>
      TransitionStmtHasOutputRouteSource W labelOffset context (.goto jump)
        hsupport
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      TransitionStmtHasOutputRouteSource W labelOffset context
          (.load update continuation) hsupport ∧
        transitionStmtRecursiveOutputRouteSources W labelOffset
          (context.afterLoad W.machine.tm update) continuation hcontinuation
  | context, push selected emit continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount W.machine.tm) →
          SupportedSymbol W.machine.tm selected := fun code =>
        ⟨emit ((stateEquivFin W.machine.tm).symm code), by
          apply hsupport selected
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      TransitionStmtHasOutputRouteSource W labelOffset context
          (.push selected emit continuation) hsupport ∧
        transitionStmtRecursiveOutputRouteSources W labelOffset
          (context.afterPush W.machine.tm selected table) continuation
          hcontinuation
  | context, peek selected update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      TransitionStmtHasOutputRouteSource W labelOffset context
          (.peek selected update continuation) hsupport ∧
        transitionStmtRecursiveOutputRouteSources W labelOffset
          (context.afterPeek W.machine.tm selected update) continuation
          hcontinuation
  | context, pop selected update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      TransitionStmtHasOutputRouteSource W labelOffset context
          (.pop selected update continuation) hsupport ∧
        transitionStmtRecursiveOutputRouteSources W labelOffset
          (context.afterPop W.machine.tm selected update) continuation
          hcontinuation
  | context, branch test whenTrue whenFalse, hsupport =>
      let htrueSupport := transitionStmtBranchTrueSupport W.machine.tm test
        whenTrue whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport W.machine.tm test
        whenTrue whenFalse hsupport
      TransitionStmtHasOutputRouteSource W labelOffset context
          (.branch test whenTrue whenFalse) hsupport ∧
        transitionStmtRecursiveOutputRouteSources W labelOffset
          (transitionStmtBranchTrueContext W.machine.tm context test)
          whenTrue htrueSupport ∧
        transitionStmtRecursiveOutputRouteSources W labelOffset
          (transitionStmtBranchFalseContext W.machine.tm context test
            whenTrue) whenFalse hfalseSupport

/-- Uniform plan bounds instantiate a concrete source at every syntax node,
including both arms below every nested branch. -/
theorem transitionStmtRecursiveOutputRouteSources_of_uniformPlanBounds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext W.machine.tm)
      (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
        W.machine.tm.σ)
      (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
        reachableAlphabet W.machine.tm k),
      (transitionStmtRecursivePlan W.machine.tm labelOffset context q
        hsupport).UniformLinearRouteBounds W labelOffset →
      transitionStmtRecursiveOutputRouteSources W labelOffset context q
        hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hbounds
      exact ⟨
        verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
          W labelOffset context halt hsupport hbounds⟩
  | goto jump =>
      intro hsupport hbounds
      exact ⟨
        verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
          W labelOffset context (.goto jump) hsupport hbounds⟩
  | load update continuation ih =>
      intro hsupport hbounds
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      have hcurrent : TransitionStmtHasOutputRouteSource W labelOffset context
          (.load update continuation) hsupport :=
        ⟨verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
          W labelOffset context (.load update continuation) hsupport hbounds⟩
      have htail := ih (context.afterLoad W.machine.tm update)
        hcontinuation hbounds
      exact ⟨hcurrent, htail⟩
  | push selected emit continuation ih =>
      intro hsupport hbounds
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount W.machine.tm) →
          SupportedSymbol W.machine.tm selected := fun code =>
        ⟨emit ((stateEquivFin W.machine.tm).symm code), by
          apply hsupport selected
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      have hcurrent : TransitionStmtHasOutputRouteSource W labelOffset context
          (.push selected emit continuation) hsupport :=
        ⟨verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
          W labelOffset context (.push selected emit continuation) hsupport
            hbounds⟩
      have htail := ih (context.afterPush W.machine.tm selected table)
        hcontinuation hbounds
      exact ⟨hcurrent, htail⟩
  | peek selected update continuation ih =>
      intro hsupport hbounds
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      have hcurrent : TransitionStmtHasOutputRouteSource W labelOffset context
          (.peek selected update continuation) hsupport :=
        ⟨verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
          W labelOffset context (.peek selected update continuation) hsupport
            hbounds⟩
      have htail := ih (context.afterPeek W.machine.tm selected update)
        hcontinuation hbounds
      exact ⟨hcurrent, htail⟩
  | pop selected update continuation ih =>
      intro hsupport hbounds
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      have hcurrent : TransitionStmtHasOutputRouteSource W labelOffset context
          (.pop selected update continuation) hsupport :=
        ⟨verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
          W labelOffset context (.pop selected update continuation) hsupport
            hbounds⟩
      have htail := ih (context.afterPop W.machine.tm selected update)
        hcontinuation hbounds
      exact ⟨hcurrent, htail⟩
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hbounds
      let htrueSupport := transitionStmtBranchTrueSupport W.machine.tm test
        whenTrue whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport W.machine.tm test
        whenTrue whenFalse hsupport
      have hcurrent : TransitionStmtHasOutputRouteSource W labelOffset context
          (.branch test whenTrue whenFalse) hsupport :=
        ⟨verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
          W labelOffset context (.branch test whenTrue whenFalse) hsupport
            hbounds⟩
      have htrue := ihTrue
        (transitionStmtBranchTrueContext W.machine.tm context test)
        htrueSupport hbounds.1
      have hfalse := ihFalse
        (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
        hfalseSupport hbounds.2
      exact ⟨hcurrent, htrue, hfalse⟩

/-- Every node of every fixed verifier label's recursive statement tree has
an actual polynomial-time complete-route source from the raw input. -/
theorem verifierTransitionLabel_recursiveOutputRouteSources
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    transitionStmtRecursiveOutputRouteSources W labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) := by
  apply transitionStmtRecursiveOutputRouteSources_of_uniformPlanBounds
  exact verifierTransitionRecursivePlan_uniformLinearRouteBounds W
    labelOffset label

end CLRS.Chapter34.Turing.CookLevin
