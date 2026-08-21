import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveSegments

/-!
# Interleaved fixed-controller output for recursive statements

Fixed affine-form blocks and variable-width mux segment blocks occur in a
depth-first interleaving for nested statements.  This module exposes that
interleaving explicitly and proves that the joined outputs are exactly the
official continuous statement-controller encoding of the recursive semantic
phase list.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Controller output for one verifier-fixed list of affine phase forms. -/
def transitionStmtAffineFormsControllerFrames
    (seed : TransitionRowSeed)
    (forms : List TransitionAffineStmtPhaseForm) : List UnaryFrameSym :=
  encodeAffineStmtControllerScript
    (forms.map fun phase => phase.eval (transitionTailAffineSeed seed))

/-- Depth-first concatenation of fixed affine-form controller output and
generic mux-progression controller output. -/
noncomputable def transitionStmtRecursiveControllerFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      List UnaryFrameSym
  | _, halt, _ => []
  | context, goto jump, hsupport =>
      transitionStmtAffineFormsControllerFrames seed
        (transitionStmtContextHeadPhaseForm tm labelOffset context
          (.goto jump) hsupport).toList
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      transitionStmtAffineFormsControllerFrames seed
          (transitionStmtContextHeadPhaseForm tm labelOffset context
            (.load update continuation) hsupport).toList ++
        transitionStmtRecursiveControllerFrames tm seed labelOffset
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
      transitionStmtAffineFormsControllerFrames seed
          (transitionStmtContextHeadPhaseForm tm labelOffset context
            (.push k emit continuation) hsupport).toList ++
        transitionStmtRecursiveControllerFrames tm seed labelOffset
          (context.afterPush tm k table) continuation hcontinuation
  | context, peek k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      transitionStmtAffineFormsControllerFrames seed
          (transitionStmtContextHeadPhaseForm tm labelOffset context
            (.peek k update continuation) hsupport).toList ++
        transitionStmtRecursiveControllerFrames tm seed labelOffset
          (context.afterPeek tm k update) continuation hcontinuation
  | context, pop k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      transitionStmtAffineFormsControllerFrames seed
          (transitionStmtContextPopPhaseForms tm labelOffset context k
            update) ++
        transitionStmtRecursiveControllerFrames tm seed labelOffset
          (context.afterPop tm k update) continuation hcontinuation
  | context, branch test whenTrue whenFalse, hsupport =>
      let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
        whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
        whenFalse hsupport
      let view := transitionStmtRecursiveBranchMuxInvocationView tm seed
        labelOffset context test whenTrue whenFalse hsupport
      transitionStmtAffineFormsControllerFrames seed
          (transitionStmtContextHeadPhaseForm tm labelOffset context
            (.branch test whenTrue whenFalse) hsupport).toList ++
        transitionStmtRecursiveControllerFrames tm seed labelOffset
          (transitionStmtBranchTrueContext tm context test) whenTrue
          htrueSupport ++
        transitionStmtRecursiveControllerFrames tm seed labelOffset
          (transitionStmtBranchFalseContext tm context test whenTrue)
          whenFalse hfalseSupport ++
        affineStmtPhaseTagCode (.mux view.selector view.frames) ++
        affineMuxInvocationProgressionFamilyFrames
          (transitionStmtRecursiveBranchMuxInvocationSegments tm seed
            labelOffset context test whenTrue whenFalse hsupport)

/-- The interleaved component outputs are exactly the continuous statement
controller encoding of the recursive phase list. -/
theorem transitionStmtRecursiveControllerFrames_eq_phases
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      transitionStmtRecursiveContextPadding tm seed context q hsupport →
      transitionStmtRecursiveControllerFrames tm seed labelOffset context q
          hsupport =
        encodeAffineStmtControllerScript
          (transitionStmtRecursivePhases tm seed labelOffset context q
            hsupport) := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hpadding
      rfl
  | goto jump =>
      intro hsupport hpadding
      rfl
  | load update continuation ih =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ k, stmtPushSet tm continuation k ⊆
          reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      have htail := ih (context.afterLoad tm update) hcontinuation
        htailPadding
      simp only [transitionStmtRecursiveControllerFrames,
        transitionStmtRecursivePhases]
      rw [htail]
      simp [transitionStmtAffineFormsControllerFrames,
        encodeAffineStmtControllerScript, List.flatMap_append]
  | push k emit continuation ih =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      have htail := ih (context.afterPush tm k table) hcontinuation
        htailPadding
      simp only [transitionStmtRecursiveControllerFrames,
        transitionStmtRecursivePhases]
      change _ ++ transitionStmtRecursiveControllerFrames tm seed labelOffset
          (context.afterPush tm k table) continuation hcontinuation = _
      rw [htail]
      simp [transitionStmtAffineFormsControllerFrames,
        encodeAffineStmtControllerScript, List.flatMap_append]
      congr 1
  | peek k update continuation ih =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      have htail := ih (context.afterPeek tm k update) hcontinuation
        htailPadding
      simp only [transitionStmtRecursiveControllerFrames,
        transitionStmtRecursivePhases]
      rw [htail]
      simp [transitionStmtAffineFormsControllerFrames,
        encodeAffineStmtControllerScript, List.flatMap_append]
  | pop k update continuation ih =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      have htail := ih (context.afterPop tm k update) hcontinuation
        htailPadding
      simp only [transitionStmtRecursiveControllerFrames,
        transitionStmtRecursivePhases]
      rw [htail]
      simp [transitionStmtAffineFormsControllerFrames,
        encodeAffineStmtControllerScript, List.flatMap_append]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htruePadding, hfalsePadding⟩
      let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
        whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
        whenFalse hsupport
      let trueContext := transitionStmtBranchTrueContext tm context test
      let falseContext :=
        transitionStmtBranchFalseContext tm context test whenTrue
      have htrue := ihTrue trueContext htrueSupport htruePadding
      have hfalse := ihFalse falseContext hfalseSupport hfalsePadding
      have hsegments :=
        transitionStmtRecursiveBranchMuxInvocationSegments_frames tm seed
          hwork labelOffset context test whenTrue whenFalse hsupport
          htruePadding hfalsePadding
      simp only [transitionStmtRecursiveControllerFrames,
        transitionStmtRecursivePhases]
      change _ ++ transitionStmtRecursiveControllerFrames tm seed labelOffset
          trueContext whenTrue htrueSupport ++
        transitionStmtRecursiveControllerFrames tm seed labelOffset
          falseContext whenFalse hfalseSupport ++ _ ++ _ = _
      rw [htrue, hfalse, hsegments]
      unfold TransitionDispatchMuxInvocationView.encode
      simp [transitionStmtAffineFormsControllerFrames,
        encodeAffineStmtControllerScript, encodeAffineStmtControllerPhase,
        affineStmtPhasePayload, List.flatMap_append, List.append_assoc]
      congr 1

/-- At a verifier label, the interleaved fixed-controller outputs encode the
full semantic statement script directly. -/
theorem transitionStmtRecursiveInitialControllerFrames_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    transitionStmtRecursiveControllerFrames W.machine.tm seed labelOffset
        (TransitionStmtAffineContext.initial W.machine.tm)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label) =
      encodeAffineStmtControllerScript
        (transitionStmtScript W.machine.tm
          (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
          (seed.start + labelOffset.eval seed.height)
          (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
            seed.rowBase)
          (W.machine.tm.m label)
          (stmtPushSet_program_subset W.machine.tm label)) := by
  have hpadding := transitionStmtRecursiveContextPadding_initial_verifier
    W input seed hseed label
  have hheight := verifierHeight_actionPadding_le W input.length
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    rw [hseed]
    unfold workHeight
    omega
  rw [transitionStmtRecursiveControllerFrames_eq_phases W.machine.tm seed
    hwork labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    hpadding]
  rw [transitionStmtRecursiveInitial_phases_eq_script W input seed hseed
    labelOffset label]

end CLRS.Chapter34.Turing.CookLevin
