import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionRecursiveBranchDescriptorInterpreter
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchMuxFramesSource

/-!
# End-to-end recursive-branch descriptor pipeline

The raw descriptor generator, fixed length-prefixed interpreter, periodic
packet preparation, packet assembler, and mux progression expander are
composed here.  This validates the descriptor-driven route independently of
the older four-source branch packet construction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw verifier input to unprepared four-row recursive-branch packets,
factored through the concrete length-prefixed descriptor interpreter. -/
noncomputable def
    verifierTransitionRecursiveBranchDescriptorLabelPacketFrames_computableInPolyTime
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
    _root_.Turing.TM2ComputableInPolyTime id
      AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
      (verifierTransitionRecursiveBranchAlignedViewFamily W labelOffset context
        test whenTrue whenFalse hsupport htruePadding hfalsePadding) := by
  let descriptorSource :=
    verifierTransitionRecursiveBranchLengthPrefixedDescriptorFrames_computableInPolyTime
      W labelOffset context test whenTrue whenFalse hsupport htrueBounds
      hfalseBounds htruePadding hfalsePadding
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      descriptorSource
      transitionDispatchMuxInvocationLengthPrefixedDescriptorInterpreter_computableInPolyTime
  simpa only [Function.comp_def, id_eq] using Classical.choice composed

/-- The descriptor-driven physical route computes the complete recursive
branch mux frames in polynomial time from the original verifier input. -/
noncomputable def
    verifierTransitionRecursiveBranchMuxFrames_viaDescriptor_computableInPolyTime
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
    verifierTransitionRecursiveBranchDescriptorLabelPacketFrames_computableInPolyTime
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
