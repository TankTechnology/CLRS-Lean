import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementDescriptorSeedSources

/-!
# Recursive numeric descriptor sources for complete statements

Every node of an arbitrary verifier statement contributes a fixed affine
head.  Linear nodes continue with one subtree; branch nodes continue with
both subtrees and finally contribute the numeric descriptor consumed by the
already verified mux pipeline.  Uniform seed-row append turns this syntactic
recursion into one concrete polynomial-time source from the raw input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt
open PolyBuilder

/-- The fixed affine phase prefix stored at the root of a recursive plan. -/
def TransitionStmtRecursivePlan.headPhaseForms
    {tm : _root_.Turing.FinTM2} :
    TransitionStmtRecursivePlan tm → List TransitionAffineStmtPhaseForm
  | .terminal forms _ => forms
  | .prefix forms _ => forms
  | .branch _ _ _ _ forms _ _ => forms

/-- The numeric affine fields stored at the root of a recursive plan. -/
def TransitionStmtRecursivePlan.headFieldForms
    {tm : _root_.Turing.FinTM2} (plan : TransitionStmtRecursivePlan tm) :
    List AffineUnaryTripleForm :=
  transitionAffineStmtScriptFieldForms plan.headPhaseForms

/-- A concrete source for the entire recursive numeric descriptor of a fixed
statement.  Its row order mirrors `transitionStmtRecursiveControllerFrames`:
head, recursive continuations/arms, then the current branch mux. -/
noncomputable def verifierTransitionStmtRecursiveDescriptorSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext W.machine.tm) →
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ) →
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k) →
    (hbounds : (transitionStmtRecursivePlan W.machine.tm labelOffset context q
      hsupport).UniformLinearRouteBounds W labelOffset) →
      VerifierTransitionSeedRowSource W
  | context, halt, hsupport, hbounds =>
      verifierTransitionAffineFormSeedRowSource W
        (transitionStmtRecursivePlan W.machine.tm labelOffset context halt
          hsupport).headFieldForms
  | context, goto jump, hsupport, hbounds =>
      verifierTransitionAffineFormSeedRowSource W
        (transitionStmtRecursivePlan W.machine.tm labelOffset context
          (.goto jump) hsupport).headFieldForms
  | context, load update continuation, hsupport, hbounds =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      let tailBounds :
          (transitionStmtRecursivePlan W.machine.tm labelOffset
            (context.afterLoad W.machine.tm update) continuation
            hcontinuation).UniformLinearRouteBounds W labelOffset := by
        simpa [transitionStmtRecursivePlan,
          TransitionStmtRecursivePlan.UniformLinearRouteBounds] using hbounds
      let head := verifierTransitionAffineFormSeedRowSource W
        (transitionStmtRecursivePlan W.machine.tm labelOffset context
          (.load update continuation) hsupport).headFieldForms
      let tail := verifierTransitionStmtRecursiveDescriptorSeedRowSource W
        labelOffset (context.afterLoad W.machine.tm update) continuation
          hcontinuation tailBounds
      head.append tail
  | context, push selected emit continuation, hsupport, hbounds =>
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
      let tailBounds :
          (transitionStmtRecursivePlan W.machine.tm labelOffset
            (context.afterPush W.machine.tm selected table) continuation
            hcontinuation).UniformLinearRouteBounds W labelOffset := by
        simpa [transitionStmtRecursivePlan,
          TransitionStmtRecursivePlan.UniformLinearRouteBounds] using hbounds
      let head := verifierTransitionAffineFormSeedRowSource W
        (transitionStmtRecursivePlan W.machine.tm labelOffset context
          (.push selected emit continuation) hsupport).headFieldForms
      let tail := verifierTransitionStmtRecursiveDescriptorSeedRowSource W
        labelOffset (context.afterPush W.machine.tm selected table)
          continuation hcontinuation tailBounds
      head.append tail
  | context, peek selected update continuation, hsupport, hbounds =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      let tailBounds :
          (transitionStmtRecursivePlan W.machine.tm labelOffset
            (context.afterPeek W.machine.tm selected update) continuation
            hcontinuation).UniformLinearRouteBounds W labelOffset := by
        simpa [transitionStmtRecursivePlan,
          TransitionStmtRecursivePlan.UniformLinearRouteBounds] using hbounds
      let head := verifierTransitionAffineFormSeedRowSource W
        (transitionStmtRecursivePlan W.machine.tm labelOffset context
          (.peek selected update continuation) hsupport).headFieldForms
      let tail := verifierTransitionStmtRecursiveDescriptorSeedRowSource W
        labelOffset (context.afterPeek W.machine.tm selected update)
          continuation hcontinuation tailBounds
      head.append tail
  | context, pop selected update continuation, hsupport, hbounds =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      let tailBounds :
          (transitionStmtRecursivePlan W.machine.tm labelOffset
            (context.afterPop W.machine.tm selected update) continuation
            hcontinuation).UniformLinearRouteBounds W labelOffset := by
        simpa [transitionStmtRecursivePlan,
          TransitionStmtRecursivePlan.UniformLinearRouteBounds] using hbounds
      let head := verifierTransitionAffineFormSeedRowSource W
        (transitionStmtRecursivePlan W.machine.tm labelOffset context
          (.pop selected update continuation) hsupport).headFieldForms
      let tail := verifierTransitionStmtRecursiveDescriptorSeedRowSource W
        labelOffset (context.afterPop W.machine.tm selected update)
          continuation hcontinuation tailBounds
      head.append tail
  | context, branch test whenTrue whenFalse, hsupport, hbounds =>
      let htrueSupport := transitionStmtBranchTrueSupport W.machine.tm test
        whenTrue whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport W.machine.tm test
        whenTrue whenFalse hsupport
      let trueContext := transitionStmtBranchTrueContext W.machine.tm context
        test
      let falseContext := transitionStmtBranchFalseContext W.machine.tm
        context test whenTrue
      let branchBounds :
          (transitionStmtRecursivePlan W.machine.tm labelOffset trueContext
              whenTrue htrueSupport).UniformLinearRouteBounds W labelOffset ∧
            (transitionStmtRecursivePlan W.machine.tm labelOffset falseContext
              whenFalse hfalseSupport).UniformLinearRouteBounds W
                labelOffset := by
        simpa [transitionStmtRecursivePlan,
          TransitionStmtRecursivePlan.UniformLinearRouteBounds, trueContext,
          falseContext, htrueSupport, hfalseSupport] using hbounds
      let head := verifierTransitionAffineFormSeedRowSource W
        (transitionStmtRecursivePlan W.machine.tm labelOffset context
          (.branch test whenTrue whenFalse) hsupport).headFieldForms
      let trueTree := verifierTransitionStmtRecursiveDescriptorSeedRowSource W
        labelOffset trueContext whenTrue htrueSupport branchBounds.1
      let falseTree := verifierTransitionStmtRecursiveDescriptorSeedRowSource W
        labelOffset falseContext whenFalse hfalseSupport branchBounds.2
      let branchDescriptor :=
        verifierTransitionRecursiveBranchSeedRowSource W labelOffset context
          test whenTrue whenFalse hsupport branchBounds.1 branchBounds.2
      ((head.append trueTree).append falseTree).append branchDescriptor

/-- Public marked-row family generated for a complete recursive statement. -/
noncomputable def verifierTransitionStmtRecursiveDescriptorFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k)
    (hbounds : (transitionStmtRecursivePlan W.machine.tm labelOffset context q
      hsupport).UniformLinearRouteBounds W labelOffset)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (verifierTransitionStmtRecursiveDescriptorSeedRowSource W labelOffset
    context q hsupport hbounds).family input

/-- The complete statement descriptor still has exactly one row per verifier
transition seed. -/
theorem verifierTransitionStmtRecursiveDescriptorFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k)
    (hbounds : (transitionStmtRecursivePlan W.machine.tm labelOffset context q
      hsupport).UniformLinearRouteBounds W labelOffset)
    (input : List Γ) :
    (verifierTransitionStmtRecursiveDescriptorFamily W labelOffset context q
      hsupport hbounds input).rows =
      (verifierTransitionRowSeeds W input).map
        (verifierTransitionStmtRecursiveDescriptorSeedRowSource W labelOffset
          context q hsupport hbounds).row := by
  exact (verifierTransitionStmtRecursiveDescriptorSeedRowSource W labelOffset
    context q hsupport hbounds).rows_eq input

/-- The syntax-recursive construction is backed by one fixed polynomial-time
TM2 from the raw verifier input. -/
noncomputable def
    verifierTransitionStmtRecursiveDescriptorFamily_computableInPolyTime
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
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionStmtRecursiveDescriptorFamily W labelOffset context q
        hsupport hbounds) :=
  (verifierTransitionStmtRecursiveDescriptorSeedRowSource W labelOffset
    context q hsupport hbounds).computableInPolyTime

end CLRS.Chapter34.Turing.CookLevin
