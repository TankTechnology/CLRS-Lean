import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchPacketSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelConcat

/-!
# One-row numeric descriptors for recursive branch muxes

The packet pipeline executes a recursive branch immediately.  Whole-statement
assembly also needs a seed-local representation that can be concatenated with
the descriptors of surrounding syntax nodes.  This file reuses the four
already verified sources and the physical row-wise concatenator to produce
one delimiter-free numeric descriptor row per transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Numeric payload of one recursive mux before phase delimiters and gates are
materialized. -/
def TransitionDispatchMuxInvocationView.numericDescriptorRow
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  encodeUnaryFrame [view.selector] ++
    transitionDispatchMuxCoordinateRowFrames view.coordinates ++
    encodeUnaryFrame view.whenTrue ++ encodeUnaryFrame view.whenFalse

private theorem recursiveBranchSelector_coordinate_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (input : List Γ) :
    (verifierTransitionRecursiveBranchSelectorFamily W labelOffset context
      test input).rows.length =
    (verifierTransitionRecursiveBranchCoordinateFamily W labelOffset context
      test whenTrue whenFalse input).rows.length := by
  simp [verifierTransitionRecursiveBranchSelectorFamily,
    verifierTransitionRecursiveBranchCoordinateFamily]

private theorem recursiveBranchTrue_false_aligned
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
  simp [verifierTransitionStmtOutputRouteFamily]

private noncomputable def recursiveBranchSelectorCoordinateFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  UnaryFrameMarkedRowParallelConcat.concatenatedFamily
    (recursiveBranchSelector_coordinate_aligned W labelOffset context test
      whenTrue whenFalse) input

private noncomputable def recursiveBranchTrueFalseFamily
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
  UnaryFrameMarkedRowParallelConcat.concatenatedFamily
    (recursiveBranchTrue_false_aligned W labelOffset context test whenTrue
      whenFalse hsupport) input

private theorem recursiveBranchDescriptor_pairs_aligned
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
    (recursiveBranchSelectorCoordinateFamily W labelOffset context test
      whenTrue whenFalse input).rows.length =
    (recursiveBranchTrueFalseFamily W labelOffset context test whenTrue
      whenFalse hsupport input).rows.length := by
  change
    (concatUnaryFrameMarkedRows
      (verifierTransitionRecursiveBranchSelectorFamily W labelOffset context
        test input).rows
      (verifierTransitionRecursiveBranchCoordinateFamily W labelOffset context
        test whenTrue whenFalse input).rows).length =
    (concatUnaryFrameMarkedRows
      (verifierTransitionStmtOutputRouteFamily W labelOffset
        (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
        (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
          hsupport) input).rows
      (verifierTransitionStmtOutputRouteFamily W labelOffset
        (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
        whenFalse
        (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
          hsupport) input).rows).length
  rw [concatUnaryFrameMarkedRows_length_of_aligned _ _
    (recursiveBranchSelector_coordinate_aligned W labelOffset context test
      whenTrue whenFalse input)]
  rw [concatUnaryFrameMarkedRows_length_of_aligned _ _
    (recursiveBranchTrue_false_aligned W labelOffset context test whenTrue
      whenFalse hsupport input)]
  simp [verifierTransitionRecursiveBranchSelectorFamily,
    verifierTransitionStmtOutputRouteFamily]

/-- One numeric mux descriptor row per verifier transition seed. -/
noncomputable def verifierTransitionRecursiveBranchDescriptorFamily
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
  UnaryFrameMarkedRowParallelConcat.concatenatedFamily
    (recursiveBranchDescriptor_pairs_aligned W labelOffset context test
      whenTrue whenFalse hsupport) input

private theorem nested_concat_maps_eq_four
    {α : Type} (items : List α)
    (first second third fourth : α → List UnaryFrameSym) :
    concatUnaryFrameMarkedRows
        (concatUnaryFrameMarkedRows (items.map first) (items.map second))
        (concatUnaryFrameMarkedRows (items.map third) (items.map fourth)) =
      items.map fun item =>
        first item ++ second item ++ third item ++ fourth item := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.map_cons, concatUnaryFrameMarkedRows]
      rw [ih]
      simp [List.append_assoc]

/-- The one-row family contains exactly the four numeric fields of the
canonical recursive mux view in their execution order. -/
theorem verifierTransitionRecursiveBranchDescriptorFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k) :
    (verifierTransitionRecursiveBranchDescriptorFamily W labelOffset context
      test whenTrue whenFalse hsupport input).rows =
      (verifierTransitionRecursiveBranchViews W labelOffset context test
        whenTrue whenFalse hsupport input).map
          TransitionDispatchMuxInvocationView.numericDescriptorRow := by
  let seeds := verifierTransitionRowSeeds W input
  let view := fun seed =>
    transitionStmtRecursiveBranchMuxInvocationView W.machine.tm seed
      labelOffset context test whenTrue whenFalse hsupport
  change
    concatUnaryFrameMarkedRows
        (concatUnaryFrameMarkedRows
          (seeds.map fun seed => encodeUnaryFrame [(view seed).selector])
          (seeds.map fun seed =>
            transitionDispatchMuxCoordinateRowFrames
              (view seed).coordinates))
        (concatUnaryFrameMarkedRows
          (seeds.map fun seed => encodeUnaryFrame (view seed).whenTrue)
          (seeds.map fun seed => encodeUnaryFrame (view seed).whenFalse)) =
      (seeds.map view).map
        TransitionDispatchMuxInvocationView.numericDescriptorRow
  rw [nested_concat_maps_eq_four]
  rw [List.map_map]
  apply List.map_congr_left
  intro seed hseed
  rfl

/-- The complete numeric descriptor row is generated by one fixed
polynomial-time TM2 from the raw verifier input. -/
noncomputable def
    verifierTransitionRecursiveBranchDescriptorFamily_computableInPolyTime
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
      (verifierTransitionRecursiveBranchDescriptorFamily W labelOffset context
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
  let selectorCoordinate :=
    UnaryFrameMarkedRowParallelConcat.computableInPolyTime selectorSource
      coordinateSource
      (recursiveBranchSelector_coordinate_aligned W labelOffset context test
        whenTrue whenFalse)
  let trueFalse :=
    UnaryFrameMarkedRowParallelConcat.computableInPolyTime trueSource
      falseSource
      (recursiveBranchTrue_false_aligned W labelOffset context test whenTrue
        whenFalse hsupport)
  exact UnaryFrameMarkedRowParallelConcat.computableInPolyTime
    selectorCoordinate trueFalse
    (recursiveBranchDescriptor_pairs_aligned W labelOffset context test
      whenTrue whenFalse hsupport)

end CLRS.Chapter34.Turing.CookLevin
