import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchCoordinateSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchRoutePairSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketReverse

/-!
# Complete four-row packets for one recursive branch

The selector, coordinate, true-route, and false-route channels are now four
independent typed sources.  Three applications of the verified same-input
interleaver reconstruct the canonical
`selector / coordinates / true / false` packet for every transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem recursiveBranchSelector_true_aligned
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
    (verifierTransitionRecursiveBranchSelectorFamily W labelOffset context
      test input).rows.length =
    (verifierTransitionStmtOutputRouteFamily W labelOffset
      (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
      (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
        hsupport) input).rows.length := by
  simp [verifierTransitionRecursiveBranchSelectorFamily]

private theorem recursiveBranchCoordinate_false_aligned
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
    (verifierTransitionRecursiveBranchCoordinateFamily W labelOffset context
      test whenTrue whenFalse input).rows.length =
    (verifierTransitionStmtOutputRouteFamily W labelOffset
      (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
      whenFalse
      (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
        hsupport) input).rows.length := by
  simp [verifierTransitionRecursiveBranchCoordinateFamily]

private noncomputable def recursiveBranchSelectorTrueFamily
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
    (recursiveBranchSelector_true_aligned W labelOffset context test whenTrue
      whenFalse hsupport) input

private noncomputable def recursiveBranchCoordinateFalseFamily
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
    (recursiveBranchCoordinate_false_aligned W labelOffset context test
      whenTrue whenFalse hsupport) input

private theorem recursiveBranchPairFamilies_aligned
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
    (recursiveBranchSelectorTrueFamily W labelOffset context test whenTrue
      whenFalse hsupport input).rows.length =
    (recursiveBranchCoordinateFalseFamily W labelOffset context test whenTrue
      whenFalse hsupport input).rows.length := by
  change
    (interleaveUnaryFrameMarkedRows
      (verifierTransitionRecursiveBranchSelectorFamily W labelOffset context
        test input).rows
      (verifierTransitionStmtOutputRouteFamily W labelOffset
        (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
        (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
          hsupport) input).rows).length =
    (interleaveUnaryFrameMarkedRows
      (verifierTransitionRecursiveBranchCoordinateFamily W labelOffset context
        test whenTrue whenFalse input).rows
      (verifierTransitionStmtOutputRouteFamily W labelOffset
        (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
        whenFalse
        (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
          hsupport) input).rows).length
  rw [interleaveUnaryFrameMarkedRows_length_of_aligned _ _
    (recursiveBranchSelector_true_aligned W labelOffset context test whenTrue
      whenFalse hsupport input)]
  rw [interleaveUnaryFrameMarkedRows_length_of_aligned _ _
    (recursiveBranchCoordinate_false_aligned W labelOffset context test
      whenTrue whenFalse hsupport input)]
  simp [verifierTransitionRecursiveBranchSelectorFamily,
    verifierTransitionRecursiveBranchCoordinateFamily]

/-- Concrete three-interleaver output family for one fixed recursive branch. -/
noncomputable def verifierTransitionRecursiveBranchPacketFamily
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
    (recursiveBranchPairFamilies_aligned W labelOffset context test whenTrue
      whenFalse hsupport) input

/-- Semantic recursive branch view at every verifier transition seed. -/
noncomputable def verifierTransitionRecursiveBranchViews
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (input : List Γ) : List TransitionDispatchMuxInvocationView :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    transitionStmtRecursiveBranchMuxInvocationView W.machine.tm seed
      labelOffset context test whenTrue whenFalse hsupport

private theorem nested_interleave_maps_eq_four_rows
    {α : Type} (seeds : List α)
    (selector coordinate whenTrue whenFalse : α → List UnaryFrameSym) :
    interleaveUnaryFrameMarkedRows
        (interleaveUnaryFrameMarkedRows (seeds.map selector)
          (seeds.map whenTrue))
        (interleaveUnaryFrameMarkedRows (seeds.map coordinate)
          (seeds.map whenFalse)) =
      seeds.flatMap fun seed =>
        [selector seed, coordinate seed, whenTrue seed, whenFalse seed] := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, interleaveUnaryFrameMarkedRows,
        List.flatMap_cons]
      rw [ih]
      rfl

/-- The nested physical interleavers produce the literal canonical four rows
of every recursive branch view. -/
theorem verifierTransitionRecursiveBranchPacketFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k) :
    (verifierTransitionRecursiveBranchPacketFamily W labelOffset context test
      whenTrue whenFalse hsupport input).rows =
      (verifierTransitionRecursiveBranchViews W labelOffset context test
        whenTrue whenFalse hsupport input).flatMap
          TransitionDispatchMuxInvocationView.labelPacketRows := by
  let seeds := verifierTransitionRowSeeds W input
  let view := fun seed =>
    transitionStmtRecursiveBranchMuxInvocationView W.machine.tm seed
      labelOffset context test whenTrue whenFalse hsupport
  change
    interleaveUnaryFrameMarkedRows
        (interleaveUnaryFrameMarkedRows
          (seeds.map fun seed => encodeUnaryFrame [(view seed).selector])
          (seeds.map fun seed => encodeUnaryFrame (view seed).whenTrue))
        (interleaveUnaryFrameMarkedRows
          (seeds.map fun seed =>
            transitionDispatchMuxCoordinateRowFrames
              (view seed).coordinates)
          (seeds.map fun seed => encodeUnaryFrame (view seed).whenFalse)) =
      (seeds.map view).flatMap
        TransitionDispatchMuxInvocationView.labelPacketRows
  rw [nested_interleave_maps_eq_four_rows]
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rfl

/-- Packet-family encoding agrees byte-for-byte with the established
four-row label-packet representation. -/
theorem verifierTransitionRecursiveBranchPacketFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionRecursiveBranchPacketFamily W labelOffset context
          test whenTrue whenFalse hsupport input) =
      (verifierTransitionRecursiveBranchViews W labelOffset context test
        whenTrue whenFalse hsupport input).flatMap
          TransitionDispatchMuxInvocationView.labelPacketFrames := by
  rw [← encode_transitionDispatchMuxInvocationLabelPacketFamily]
  unfold encodeUnaryFrameMarkedRowFamily
    transitionDispatchMuxInvocationLabelPacketFamily
  rw [verifierTransitionRecursiveBranchPacketFamily_rows]

/-- Uniform arm-plan bounds instantiate all four sources and all three
physical interleavers, yielding a concrete raw-input packet compiler. -/
noncomputable def
    verifierTransitionRecursiveBranchPacketFamily_computableInPolyTime
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
      (verifierTransitionRecursiveBranchPacketFamily W labelOffset context
        test whenTrue whenFalse hsupport) := by
  letI : Fintype Γ := W.alphabetFintype
  let selectorSource :=
    verifierTransitionRecursiveBranchSelectorFamily_computableInPolyTime W
      labelOffset context test
  let coordinateSource :=
    verifierTransitionRecursiveBranchCoordinateFamily_computableInPolyTime W
      labelOffset context test whenTrue whenFalse
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
  let selectorTrue :=
    UnaryFrameMarkedRowParallelInterleave.computableInPolyTime
      selectorSource trueSource
      (recursiveBranchSelector_true_aligned W labelOffset context test whenTrue
        whenFalse hsupport)
  let coordinateFalse :=
    UnaryFrameMarkedRowParallelInterleave.computableInPolyTime
      coordinateSource falseSource
      (recursiveBranchCoordinate_false_aligned W labelOffset context test
        whenTrue whenFalse hsupport)
  exact UnaryFrameMarkedRowParallelInterleave.computableInPolyTime
    selectorTrue coordinateFalse
    (recursiveBranchPairFamilies_aligned W labelOffset context test whenTrue
      whenFalse hsupport)

end CLRS.Chapter34.Turing.CookLevin
