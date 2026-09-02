import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorLabelReassembly

/-!
# Concrete channel projections of dispatch-mux label packets

The label-packet contract is useful to a concrete controller only if its four
projections are the streams already produced by the four verified descriptor
pipelines.  This module proves those four equalities independently, keeping
the final controller file free of artifact-level semantic reasoning.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Selector-row projection of the structured label-packet family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed).flatMap
      fun view => encodeUnaryFrame [view.selector] ++ [.frameEnd]

/-- Coordinate-row projection of the structured label-packet family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed).flatMap
      fun view =>
        transitionDispatchMuxCoordinateRowFrames view.coordinates ++
          [.frameEnd]

/-- True-arm-row projection of the structured label-packet family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed).flatMap
      fun view => encodeUnaryFrame view.whenTrue ++ [.frameEnd]

/-- False-arm-row projection of the structured label-packet family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed).flatMap
      fun view => encodeUnaryFrame view.whenFalse ++ [.frameEnd]

/-- The selector projection is exactly the output of the concrete routed
selector-label pipeline. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames_eq_semantic]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  rw [List.flatMap_map]
  have hselectors := transitionDispatchArtifactsFromSeed_selectors
    W.machine.tm seed
  have hframes := congrArg
    (List.flatMap fun selector =>
      encodeUnaryFrame [selector] ++ [.frameEnd]) hselectors
  rw [List.flatMap_map] at hframes
  simpa [TransitionDispatchLabelArtifact.muxInvocationView,
    Function.comp_def] using hframes

/-- The coordinate projection is exactly the output of the concrete routed
coordinate-label pipeline. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq_layouts]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  rw [List.flatMap_map]
  have hcoordinates := transitionDispatchArtifactsFromSeed_muxCoordinateRows
    W.machine.tm seed
  have hframes := congrArg
    (List.flatMap fun coordinates =>
      transitionDispatchMuxCoordinateRowFrames coordinates ++ [.frameEnd])
    hcoordinates
  simpa [TransitionDispatchLabelArtifact.muxInvocationView,
    Function.comp_def, List.flatMap_map] using hframes

/-- The true-arm projection is exactly the output of the concrete routed and
executed true-label pipeline. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames_eq_semantic]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  rw [List.flatMap_map]
  have hrows := transitionDispatchArtifactsFromSeed_trueArmRows
    W.machine.tm seed
  have hframes := congrArg
    (List.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) hrows
  rw [List.flatMap_map] at hframes
  simpa [TransitionDispatchLabelArtifact.muxInvocationView,
    Function.comp_def] using hframes

/-- The false-arm projection is exactly the output of the concrete routed and
executed false-label pipeline. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames_eq_semantic]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  rw [List.flatMap_map]
  have hrows := transitionDispatchArtifactsFromSeed_falseArmRows
    W.machine.tm seed
  have hframes := congrArg
    (List.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) hrows
  rw [List.flatMap_map] at hframes
  simpa [TransitionDispatchLabelArtifact.muxInvocationView,
    Function.comp_def] using hframes

end CLRS.Chapter34.Turing.CookLevin
