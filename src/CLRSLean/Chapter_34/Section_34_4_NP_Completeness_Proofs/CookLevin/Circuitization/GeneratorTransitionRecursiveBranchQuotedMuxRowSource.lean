import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionRecursiveBranchDescriptorPipeline
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionMuxQuotedRowParserRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeedRowSource

/-!
# Row-preserving quoted mux source for recursive branches

The descriptor pipeline already computes the exact concatenated mux byte
stream from the original verifier input.  Here that physical machine is
retargeted to the typed mux-view interface and composed with the fixed parser,
closing the missing one-row-per-transition-seed contract for branch muxes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The descriptor-driven mux machine, exposed through the semantic typed
view family expected by the delimiter-safe parser. -/
noncomputable def
    verifierTransitionRecursiveBranchMuxViews_computableInPolyTime
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
      transitionMuxInvocationViewFamilyFrames
      (verifierTransitionRecursiveBranchViews W labelOffset context test
        whenTrue whenFalse hsupport) := by
  let raw :=
    verifierTransitionRecursiveBranchMuxFrames_viaDescriptor_computableInPolyTime
      W labelOffset context test whenTrue whenFalse hsupport htrueBounds
        hfalseBounds htruePadding hfalsePadding
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierTransitionRecursiveBranchMuxFrames_eq W input labelOffset
          context test whenTrue whenFalse hsupport htruePadding hfalsePadding]
          at run
        simpa only [transitionMuxInvocationViewFamilyFrames, id_eq] using run }

/-- One quoted mux invocation row for each canonical verifier transition
seed, computed from the original input by fixed polynomial-time TM2s. -/
noncomputable def verifierTransitionRecursiveBranchQuotedMuxSeedRowSource
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
        hsupport)) : VerifierTransitionSeedRowSource W := by
  let views := verifierTransitionRecursiveBranchViews W labelOffset context
    test whenTrue whenFalse hsupport
  let viewAt := fun seed =>
    transitionStmtRecursiveBranchMuxInvocationView W.machine.tm seed
      labelOffset context test whenTrue whenFalse hsupport
  let typed :=
    verifierTransitionRecursiveBranchMuxViews_computableInPolyTime W
      labelOffset context test whenTrue whenFalse hsupport htrueBounds
        hfalseBounds htruePadding hfalsePadding
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch typed
      transitionMuxQuotedRowParser_computableInPolyTime
  exact
    { row := fun seed => quoteUnaryFrameStream (viewAt seed).encode
      family := fun input => transitionMuxInvocationQuotedRowFamily
        (views input)
      rows_eq := fun input => by
        simp [views, viewAt, verifierTransitionRecursiveBranchViews,
          transitionMuxInvocationQuotedRowFamily, List.map_map]
      computableInPolyTime := by
        simpa only [Function.comp_def] using Classical.choice composed }

/-- Public row theorem for the recursive branch mux source. -/
@[simp] theorem verifierTransitionRecursiveBranchQuotedMuxSeedRowSource_row
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (htrueBounds hfalseBounds htruePadding hfalsePadding)
    (seed : TransitionRowSeed) :
    (verifierTransitionRecursiveBranchQuotedMuxSeedRowSource W labelOffset
      context test whenTrue whenFalse hsupport htrueBounds hfalseBounds
        htruePadding hfalsePadding).row seed =
      quoteUnaryFrameStream
        (transitionStmtRecursiveBranchMuxInvocationView W.machine.tm seed
          labelOffset context test whenTrue whenFalse hsupport).encode := rfl

end CLRS.Chapter34.Turing.CookLevin
