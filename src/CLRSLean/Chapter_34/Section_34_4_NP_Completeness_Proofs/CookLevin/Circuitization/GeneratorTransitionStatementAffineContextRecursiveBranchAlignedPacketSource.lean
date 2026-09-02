import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchPacketSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketPipeline

/-!
# Aligned recursive-branch packet sources

The four-channel packet compiler is useful to the existing mux assembler only
after its semantic views carry the common-width invariant.  This file derives
that invariant from the recursive statement padding already available at every
verifier transition seed and retargets the concrete packet TM2 to the aligned
family interface.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One fixed recursive statement has public-row padding at every verifier
transition seed. -/
def VerifierTransitionRecursiveStmtPadding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm q k ⊆ reachableAlphabet W.machine.tm k) :
    Prop :=
  ∀ input seed, seed ∈ verifierTransitionRowSeeds W input →
    transitionStmtRecursiveContextPadding W.machine.tm seed context q
      hsupport

/-- The semantic recursive-branch views, equipped with the exact row-width
invariant required by the physical packet assembler. -/
noncomputable def verifierTransitionRecursiveBranchAlignedViewFamily
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
    (input : List Γ) : AlignedTransitionDispatchMuxInvocationViewFamily :=
  { views := verifierTransitionRecursiveBranchViews W labelOffset context test
      whenTrue whenFalse hsupport input
    rowAligned := by
      intro view hview
      rw [verifierTransitionRecursiveBranchViews, List.mem_map] at hview
      rcases hview with ⟨seed, hseed, rfl⟩
      have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
      have hwork : 0 < workHeight W.machine.tm seed.height := by
        rw [hheight]
        unfold workHeight
        exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _
      apply transitionStmtRecursiveBranchMuxInvocationView_rowAligned
        W.machine.tm seed hwork labelOffset context test whenTrue whenFalse
          hsupport
      · exact transitionStmtRecursiveContextPadding_linearResult_capacity
          W.machine.tm seed
          (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
          (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
            hsupport) (htruePadding input seed hseed)
      · exact transitionStmtRecursiveContextPadding_linearResult_capacity
          W.machine.tm seed
          (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
          whenFalse
          (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
            hsupport) (hfalsePadding input seed hseed) }

/-- The aligned-family packet encoding is literally the four-channel packet
encoding constructed from the raw verifier input. -/
theorem verifierTransitionRecursiveBranchAlignedViewFamily_labelPacketFrames
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
    (verifierTransitionRecursiveBranchAlignedViewFamily W labelOffset context
        test whenTrue whenFalse hsupport htruePadding hfalsePadding input
      ).labelPacketFrames =
      encodeUnaryFrameMarkedRowFamily
        (verifierTransitionRecursiveBranchPacketFamily W labelOffset context
          test whenTrue whenFalse hsupport input) := by
  rw [verifierTransitionRecursiveBranchPacketFamily_encoding_eq]
  unfold AlignedTransitionDispatchMuxInvocationViewFamily.labelPacketFrames
    verifierTransitionRecursiveBranchAlignedViewFamily
  rw [encode_transitionDispatchMuxInvocationLabelPacketFamily]

/-- Concrete raw-input compiler for the aligned recursive-branch packet
interface consumed by the downstream mux pipeline. -/
noncomputable def
    verifierTransitionRecursiveBranchAlignedLabelPacketFrames_computableInPolyTime
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
  let source :=
    verifierTransitionRecursiveBranchPacketFamily_computableInPolyTime W
      labelOffset context test whenTrue whenFalse hsupport htrueBounds
      hfalseBounds
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        rw [verifierTransitionRecursiveBranchAlignedViewFamily_labelPacketFrames
          W input labelOffset context test whenTrue whenFalse hsupport
          htruePadding hfalsePadding]
        simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin
