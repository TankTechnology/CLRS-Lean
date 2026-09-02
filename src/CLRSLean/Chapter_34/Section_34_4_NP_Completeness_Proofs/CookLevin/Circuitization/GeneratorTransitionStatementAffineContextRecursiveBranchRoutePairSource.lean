import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveOutputRouteSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveRuntime

/-!
# Physical true/false route pairs for recursive branch muxes

Both arm routes of a recursive branch are now independent typed raw-input
sources with one row per transition seed.  The reusable same-input parallel
interleaver combines them physically into the alternating
`true₀ / false₀ / true₁ / false₁ / ...` stream needed by the later four-row
mux-packet assembler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Every total statement-route family has exactly one marked row per
transition seed. -/
@[simp] theorem verifierTransitionStmtOutputRouteFamily_rows_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (q : _root_.Turing.TM2.Stmt W.machine.tm.Γ W.machine.tm.Λ
      W.machine.tm.σ)
    (hsupport : ∀ k, stmtPushSet W.machine.tm q k ⊆
      reachableAlphabet W.machine.tm k) :
    (verifierTransitionStmtOutputRouteFamily W labelOffset context q
      hsupport input).rows.length =
      (verifierTransitionRowSeeds W input).length := by
  simp [verifierTransitionStmtOutputRouteFamily]

private theorem verifierTransitionRecursiveBranchRoutes_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (input : List Γ) :
    (verifierTransitionStmtOutputRouteFamily W labelOffset
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport) input).rows.length =
    (verifierTransitionStmtOutputRouteFamily W labelOffset
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport) input).rows.length := by
  simp

/-- Alternating true/false semantic route rows of one fixed recursive branch
for every verifier transition seed. -/
noncomputable def verifierTransitionRecursiveBranchRoutePairFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  UnaryFrameMarkedRowParallelInterleave.interleavedFamily
    (verifierTransitionRecursiveBranchRoutes_aligned W labelOffset context
      test whenTrue whenFalse hsupport) input

/-- The paired family has the literal alternating true/false row order. -/
theorem verifierTransitionRecursiveBranchRoutePairFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k) :
    (verifierTransitionRecursiveBranchRoutePairFamily W labelOffset context
      test whenTrue whenFalse hsupport input).rows =
      interleaveUnaryFrameMarkedRows
        (verifierTransitionStmtOutputRouteFamily W labelOffset
          (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
          (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
            hsupport) input).rows
        (verifierTransitionStmtOutputRouteFamily W labelOffset
          (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
          whenFalse
          (transitionStmtBranchFalseSupport W.machine.tm test whenTrue
            whenFalse hsupport) input).rows := by
  rfl

/-- Two uniform arm-plan invariants instantiate both physical source
machines and the verified same-input interleaver. -/
noncomputable def
    verifierTransitionRecursiveBranchRoutePairFamily_computableInPolyTime
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
          hsupport)).UniformLinearRouteBounds W labelOffset) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionRecursiveBranchRoutePairFamily W labelOffset context
        test whenTrue whenFalse hsupport) := by
  letI : Fintype Γ := W.alphabetFintype
  let trueSource :=
    verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
      W labelOffset
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport) htrueBounds
  let falseSource :=
    verifierTransitionStmtOutputRouteFamily_computableInPolyTime_of_uniformPlanBounds
      W labelOffset
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport) hfalseBounds
  exact UnaryFrameMarkedRowParallelInterleave.computableInPolyTime
    trueSource falseSource
    (verifierTransitionRecursiveBranchRoutes_aligned W labelOffset context
      test whenTrue whenFalse hsupport)

end CLRS.Chapter34.Turing.CookLevin
