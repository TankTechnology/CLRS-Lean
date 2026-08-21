import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementRecursiveDescriptorSource

/-!
# Semantic contract of recursive statement descriptors

This file separates the syntax-directed numeric descriptor from its concrete
source construction.  The main theorem identifies every source row with the
independent depth-first descriptor semantics, node for node.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt
open PolyBuilder

/-- Numeric affine payload contributed by the current statement node. -/
noncomputable def transitionStmtRecursiveHeadNumericDescriptorRow
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMap
      (transitionStmtRecursivePlan tm labelOffset context q
        hsupport).headFieldForms
      (transitionTailAffineSeed seed))

/-- Independent depth-first numeric descriptor semantics of an arbitrary
statement.  Branch descriptors occur after both child descriptors, matching
the controller-frame order. -/
noncomputable def transitionStmtRecursiveNumericDescriptorRow
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      List UnaryFrameSym
  | context, halt, hsupport =>
      transitionStmtRecursiveHeadNumericDescriptorRow tm seed labelOffset
        context halt hsupport
  | context, goto jump, hsupport =>
      transitionStmtRecursiveHeadNumericDescriptorRow tm seed labelOffset
        context (.goto jump) hsupport
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      transitionStmtRecursiveHeadNumericDescriptorRow tm seed labelOffset
          context (.load update continuation) hsupport ++
        transitionStmtRecursiveNumericDescriptorRow tm seed labelOffset
          (context.afterLoad tm update) continuation hcontinuation
  | context, push selected emit continuation, hsupport =>
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
      transitionStmtRecursiveHeadNumericDescriptorRow tm seed labelOffset
          context (.push selected emit continuation) hsupport ++
        transitionStmtRecursiveNumericDescriptorRow tm seed labelOffset
          (context.afterPush tm selected table) continuation hcontinuation
  | context, peek selected update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      transitionStmtRecursiveHeadNumericDescriptorRow tm seed labelOffset
          context (.peek selected update continuation) hsupport ++
        transitionStmtRecursiveNumericDescriptorRow tm seed labelOffset
          (context.afterPeek tm selected update) continuation hcontinuation
  | context, pop selected update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      transitionStmtRecursiveHeadNumericDescriptorRow tm seed labelOffset
          context (.pop selected update continuation) hsupport ++
        transitionStmtRecursiveNumericDescriptorRow tm seed labelOffset
          (context.afterPop tm selected update) continuation hcontinuation
  | context, branch test whenTrue whenFalse, hsupport =>
      let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
        whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
        whenFalse hsupport
      transitionStmtRecursiveHeadNumericDescriptorRow tm seed labelOffset
          context (.branch test whenTrue whenFalse) hsupport ++
        transitionStmtRecursiveNumericDescriptorRow tm seed labelOffset
          (transitionStmtBranchTrueContext tm context test) whenTrue
            htrueSupport ++
        transitionStmtRecursiveNumericDescriptorRow tm seed labelOffset
          (transitionStmtBranchFalseContext tm context test whenTrue)
            whenFalse hfalseSupport ++
        transitionStmtRecursiveBranchLengthPrefixedNumericDescriptorRow tm
          seed
          (transitionStmtRecursiveBranchMuxInvocationView tm seed labelOffset
            context test whenTrue whenFalse hsupport)

/-- The recursively assembled concrete source implements the independent
numeric descriptor semantics exactly for every transition seed. -/
theorem verifierTransitionStmtRecursiveDescriptorSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (seed : TransitionRowSeed) (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext W.machine.tm)
      (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
        W.machine.tm.σ)
      (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
        reachableAlphabet W.machine.tm k)
      (hbounds : (transitionStmtRecursivePlan W.machine.tm labelOffset
        context q hsupport).UniformLinearRouteBounds W labelOffset),
      (verifierTransitionStmtRecursiveDescriptorSeedRowSource W labelOffset
          context q hsupport hbounds).row seed =
        transitionStmtRecursiveNumericDescriptorRow W.machine.tm seed
          labelOffset context q hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hbounds
      rfl
  | goto jump =>
      intro hsupport hbounds
      rfl
  | load update continuation ih =>
      intro hsupport hbounds
      simp only [verifierTransitionStmtRecursiveDescriptorSeedRowSource,
        transitionStmtRecursiveNumericDescriptorRow,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      rfl
  | push selected emit continuation ih =>
      intro hsupport hbounds
      simp only [verifierTransitionStmtRecursiveDescriptorSeedRowSource,
        transitionStmtRecursiveNumericDescriptorRow,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      rfl
  | peek selected update continuation ih =>
      intro hsupport hbounds
      simp only [verifierTransitionStmtRecursiveDescriptorSeedRowSource,
        transitionStmtRecursiveNumericDescriptorRow,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      rfl
  | pop selected update continuation ih =>
      intro hsupport hbounds
      simp only [verifierTransitionStmtRecursiveDescriptorSeedRowSource,
        transitionStmtRecursiveNumericDescriptorRow,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      rfl
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hbounds
      simp only [verifierTransitionStmtRecursiveDescriptorSeedRowSource,
        transitionStmtRecursiveNumericDescriptorRow,
        VerifierTransitionSeedRowSource.append_row]
      rw [ihTrue, ihFalse,
        verifierTransitionRecursiveBranchSeedRowSource_row]
      simp only [List.append_assoc]
      rfl

/-- Row-major semantics of the concrete recursive descriptor family. -/
theorem verifierTransitionStmtRecursiveDescriptorFamily_rows_eq_semantics
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
      (verifierTransitionRowSeeds W input).map fun seed =>
        transitionStmtRecursiveNumericDescriptorRow W.machine.tm seed
          labelOffset context q hsupport := by
  rw [verifierTransitionStmtRecursiveDescriptorFamily_rows]
  apply List.map_congr_left
  intro seed hseed
  exact verifierTransitionStmtRecursiveDescriptorSeedRowSource_row_eq W seed
    labelOffset context q hsupport hbounds

end CLRS.Chapter34.Turing.CookLevin
