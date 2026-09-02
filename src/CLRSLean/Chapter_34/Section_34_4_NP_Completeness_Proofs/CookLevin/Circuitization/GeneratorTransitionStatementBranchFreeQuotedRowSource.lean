import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineHeadQuotedRowSource

/-!
# Complete quoted row sources for branch-free statements

This file closes the recursive physical source construction for every linear
statement tree.  It isolates the remaining hard case precisely: only a
`branch` node still needs a row-preserving quoted mux source.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt
open PolyBuilder

/-- Syntactic fragment whose control tree contains no branch node. -/
def transitionStmtBranchFree {K : Type} {Γ : K → Type} {Λ σ : Type} :
    _root_.Turing.TM2.Stmt Γ Λ σ → Prop
  | .halt => True
  | .goto _ => True
  | .load _ continuation => transitionStmtBranchFree continuation
  | .push _ _ continuation => transitionStmtBranchFree continuation
  | .peek _ _ continuation => transitionStmtBranchFree continuation
  | .pop _ _ continuation => transitionStmtBranchFree continuation
  | .branch _ _ _ => False

/-- Pointwise-quoted controller source for a fixed branch-free statement.
Linear continuations are joined with the verified row-wise concatenator. -/
noncomputable def verifierTransitionStmtBranchFreeQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext W.machine.tm) →
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ) →
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k) →
    transitionStmtBranchFree q → VerifierTransitionSeedRowSource W
  | context, halt, hsupport, hfree =>
      verifierTransitionAffineHeadQuotedSeedRowSource W []
  | context, goto jump, hsupport, hfree =>
      verifierTransitionAffineHeadQuotedSeedRowSource W
        (transitionStmtContextHeadPhaseForm W.machine.tm labelOffset context
          (.goto jump) hsupport).toList
  | context, load update continuation, hsupport, hfree =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      let head := verifierTransitionAffineHeadQuotedSeedRowSource W
        (transitionStmtContextHeadPhaseForm W.machine.tm labelOffset context
          (.load update continuation) hsupport).toList
      let tail := verifierTransitionStmtBranchFreeQuotedSeedRowSource W
        labelOffset (context.afterLoad W.machine.tm update) continuation
          hcontinuation hfree
      head.append tail
  | context, push selected emit continuation, hsupport, hfree =>
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
      let head := verifierTransitionAffineHeadQuotedSeedRowSource W
        (transitionStmtContextHeadPhaseForm W.machine.tm labelOffset context
          (.push selected emit continuation) hsupport).toList
      let tail := verifierTransitionStmtBranchFreeQuotedSeedRowSource W
        labelOffset (context.afterPush W.machine.tm selected table)
          continuation hcontinuation hfree
      head.append tail
  | context, peek selected update continuation, hsupport, hfree =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      let head := verifierTransitionAffineHeadQuotedSeedRowSource W
        (transitionStmtContextHeadPhaseForm W.machine.tm labelOffset context
          (.peek selected update continuation) hsupport).toList
      let tail := verifierTransitionStmtBranchFreeQuotedSeedRowSource W
        labelOffset (context.afterPeek W.machine.tm selected update)
          continuation hcontinuation hfree
      head.append tail
  | context, pop selected update continuation, hsupport, hfree =>
      let hcontinuation : ∀ k,
          stmtPushSet W.machine.tm continuation k ⊆
            reachableAlphabet W.machine.tm k := by
        simpa [stmtPushSet] using hsupport
      let head := verifierTransitionAffineHeadQuotedSeedRowSource W
        (transitionStmtContextPopPhaseForms W.machine.tm labelOffset context
          selected update)
      let tail := verifierTransitionStmtBranchFreeQuotedSeedRowSource W
        labelOffset (context.afterPop W.machine.tm selected update)
          continuation hcontinuation hfree
      head.append tail
  | context, branch test whenTrue whenFalse, hsupport, hfree =>
      False.elim hfree

/-- The recursive physical source has exactly the quotation of the semantic
controller stream in every transition-seed row. -/
theorem verifierTransitionStmtBranchFreeQuotedSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext W.machine.tm)
      (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
        W.machine.tm.σ)
      (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
        reachableAlphabet W.machine.tm k)
      (hfree : transitionStmtBranchFree q)
      (seed : TransitionRowSeed),
      (verifierTransitionStmtBranchFreeQuotedSeedRowSource W labelOffset
          context q hsupport hfree).row seed =
        quoteUnaryFrameStream
          (transitionStmtRecursiveControllerFrames W.machine.tm seed
            labelOffset context q hsupport) := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hfree seed
      rfl
  | goto jump =>
      intro hsupport hfree seed
      rfl
  | load update continuation ih =>
      intro hsupport hfree seed
      simp only [verifierTransitionStmtBranchFreeQuotedSeedRowSource,
        transitionStmtRecursiveControllerFrames,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      simp [verifierTransitionAffineHeadQuotedSeedRowSource,
        quoteUnaryFrameStream, List.flatMap_append]
  | push selected emit continuation ih =>
      intro hsupport hfree seed
      simp only [verifierTransitionStmtBranchFreeQuotedSeedRowSource,
        transitionStmtRecursiveControllerFrames,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      simp [verifierTransitionAffineHeadQuotedSeedRowSource,
        quoteUnaryFrameStream, List.flatMap_append]
  | peek selected update continuation ih =>
      intro hsupport hfree seed
      simp only [verifierTransitionStmtBranchFreeQuotedSeedRowSource,
        transitionStmtRecursiveControllerFrames,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      simp [verifierTransitionAffineHeadQuotedSeedRowSource,
        quoteUnaryFrameStream, List.flatMap_append]
  | pop selected update continuation ih =>
      intro hsupport hfree seed
      simp only [verifierTransitionStmtBranchFreeQuotedSeedRowSource,
        transitionStmtRecursiveControllerFrames,
        VerifierTransitionSeedRowSource.append_row]
      rw [ih]
      simp [verifierTransitionAffineHeadQuotedSeedRowSource,
        quoteUnaryFrameStream, List.flatMap_append]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hfree seed
      exact False.elim hfree

end CLRS.Chapter34.Turing.CookLevin
