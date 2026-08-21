import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionLengthPrefixedDescriptorInterpreter
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchAlignedPacketSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementDescriptorSeedSources

/-!
# Executing recursive-branch descriptors with the fixed interpreter

The width written by the raw-input descriptor source is proved equal to the
actual recursive mux-view width.  This identifies its marked output stream
with the generic length-prefixed interpreter input, enabling physical
composition rather than a second branch-specific packet generator.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

@[simp] theorem transitionStmtRecursiveBranchMuxInvocationView_coordinates_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) :
    (transitionStmtRecursiveBranchMuxInvocationView tm seed labelOffset
      context test whenTrue whenFalse hsupport).coordinates.length =
      cfgBitCount tm (workHeight tm seed.height) := by
  simp [transitionStmtRecursiveBranchMuxInvocationView,
    transitionStmtBranchMuxCoordinates]

/-- The generic self-described input for the aligned recursive view family is
the marked family of the existing concrete recursive-branch descriptor
source, byte for byte. -/
theorem verifierTransitionRecursiveBranchAlignedViewFamily_lengthPrefixedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
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
    (verifierTransitionRecursiveBranchAlignedViewFamily W labelOffset context
      test whenTrue whenFalse hsupport htruePadding hfalsePadding input
      ).lengthPrefixedDescriptorFrames =
      encodeUnaryFrameMarkedRowFamily
        ((verifierTransitionRecursiveBranchSeedRowSource W labelOffset context
          test whenTrue whenFalse hsupport htrueBounds hfalseBounds).family
            input) := by
  rw [AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedDescriptorFrames_eq]
  unfold verifierTransitionRecursiveBranchAlignedViewFamily
    encodeUnaryFrameMarkedRowFamily
  rw [(verifierTransitionRecursiveBranchSeedRowSource W labelOffset context
    test whenTrue whenFalse hsupport htrueBounds hfalseBounds).rows_eq]
  unfold verifierTransitionRecursiveBranchViews
  rw [List.flatMap_map]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [verifierTransitionRecursiveBranchSeedRowSource_row]
  simp [transitionStmtRecursiveBranchLengthPrefixedNumericDescriptorRow,
    List.append_assoc]

/-- Retarget the existing raw-input descriptor source to the typed input of
the generic fixed interpreter. -/
noncomputable def
    verifierTransitionRecursiveBranchLengthPrefixedDescriptorFrames_computableInPolyTime
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
      AlignedTransitionDispatchMuxInvocationViewFamily.lengthPrefixedDescriptorFrames
      (verifierTransitionRecursiveBranchAlignedViewFamily W labelOffset context
        test whenTrue whenFalse hsupport htruePadding hfalsePadding) := by
  let source :=
    (verifierTransitionRecursiveBranchSeedRowSource W labelOffset context
      test whenTrue whenFalse hsupport htrueBounds hfalseBounds
      ).computableInPolyTime
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        rw [verifierTransitionRecursiveBranchAlignedViewFamily_lengthPrefixedDescriptorFrames
          W input labelOffset context test whenTrue whenFalse hsupport
          htrueBounds hfalseBounds htruePadding hfalsePadding]
        simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin
