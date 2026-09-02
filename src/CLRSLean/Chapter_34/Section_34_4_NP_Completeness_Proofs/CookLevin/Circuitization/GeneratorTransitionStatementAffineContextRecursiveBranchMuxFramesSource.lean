import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchAlignedPacketSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveSegments

/-!
# End-to-end recursive-branch mux frame sources

This file connects an aligned recursive-branch packet source to the already
verified periodic preparation, packet assembler, output reversal, and affine
mux progression controller.  Its final equality identifies the physical TM2
output with the recursive statement semantics at every verifier transition
seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact physical mux-controller output for one fixed recursive branch over
all verifier transition seeds. -/
noncomputable def verifierTransitionRecursiveBranchMuxFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (htruePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport))
    (hfalsePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport))
    (input : List Γ) : List UnaryFrameSym :=
  affineMuxInvocationProgressionFamilyFrames
    (verifierTransitionRecursiveBranchAlignedViewFamily W labelOffset context
      test whenTrue whenFalse hsupport htruePadding hfalsePadding input
      ).segments

/-- The physical assembler/controller output is exactly the recursive mux
encoding contributed by the branch at every verifier transition seed. -/
theorem verifierTransitionRecursiveBranchMuxFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (htruePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport))
    (hfalsePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport)) :
    verifierTransitionRecursiveBranchMuxFrames W labelOffset context test
        whenTrue whenFalse hsupport htruePadding hfalsePadding input =
      (verifierTransitionRecursiveBranchViews W labelOffset context test
        whenTrue whenFalse hsupport input).flatMap
          TransitionDispatchMuxInvocationView.encode := by
  unfold verifierTransitionRecursiveBranchMuxFrames
    AlignedTransitionDispatchMuxInvocationViewFamily.segments
    verifierTransitionRecursiveBranchAlignedViewFamily
    verifierTransitionRecursiveBranchViews
    affineMuxInvocationProgressionFamilyFrames
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  change
    affineMuxInvocationProgressionFamilyFrames
        (transitionStmtRecursiveBranchMuxInvocationSegments W.machine.tm seed
          labelOffset context test whenTrue whenFalse hsupport) =
      (transitionStmtRecursiveBranchMuxInvocationView W.machine.tm seed
        labelOffset context test whenTrue whenFalse hsupport).encode
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    rw [hheight]
    unfold workHeight
    exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _
  exact transitionStmtRecursiveBranchMuxInvocationSegments_frames
    W.machine.tm seed hwork labelOffset context test whenTrue whenFalse
    hsupport (htruePadding input seed hseed)
      (hfalsePadding input seed hseed)

/-- Concrete end-to-end polynomial-time TM2 from the raw verifier input to
all mux frames of one fixed recursive branch. -/
noncomputable def
    verifierTransitionRecursiveBranchMuxFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (htrueBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
        (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset)
    (hfalseBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
        whenFalse
        (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset)
    (htruePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport))
    (hfalsePadding : VerifierTransitionRecursiveStmtPadding W
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionRecursiveBranchMuxFrames W labelOffset context test
        whenTrue whenFalse hsupport htruePadding hfalsePadding) := by
  let packetSource :=
    verifierTransitionRecursiveBranchAlignedLabelPacketFrames_computableInPolyTime
      W labelOffset context test whenTrue whenFalse hsupport htrueBounds
      hfalseBounds htruePadding hfalsePadding
  let preparedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch packetSource
      transitionDispatchMuxInvocationLabelPacketPrepareAligned_computableInPolyTime
  let prepared := Classical.choice preparedExists
  let framesExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch prepared
      transitionDispatchMuxInvocationFrames_fromAlignedViews_computableInPolyTime
  let result := Classical.choice framesExists
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        simpa only [Function.comp_def, id_eq,
          verifierTransitionRecursiveBranchMuxFrames] using
            result.outputsFun input }

end CLRS.Chapter34.Turing.CookLevin
