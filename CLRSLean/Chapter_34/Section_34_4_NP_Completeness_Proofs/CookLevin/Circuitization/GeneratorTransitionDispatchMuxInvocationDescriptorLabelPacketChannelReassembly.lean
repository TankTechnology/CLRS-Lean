import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketReverse

/-!
# Reassembling the four dispatch-mux label channels

The four concrete descriptor interpreters emit selector, coordinate, true-arm,
and false-arm rows independently.  This module fixes their exact common row
interface and proves the missing semantic transpose: zipping the four rows of
each label recovers the canonical label-packet stream byte for byte.

No machine-level fan-out is claimed here.  The result isolates the remaining
implementation obligation as one physical four-channel row reassembler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Row payloads of the four descriptor-derived label channels. -/
structure TransitionDispatchMuxInvocationLabelPacketChannelFamily where
  selectorRows : List (List UnaryFrameSym)
  coordinateRows : List (List UnaryFrameSym)
  trueRows : List (List UnaryFrameSym)
  falseRows : List (List UnaryFrameSym)

/-- Encode delimiter-free payload rows with one physical marker per row. -/
def encodeTransitionDispatchMuxInvocationLabelPacketChannelRows
    (rows : List (List UnaryFrameSym)) : List UnaryFrameSym :=
  rows.flatMap fun row => row ++ [.frameEnd]

/-- Total four-way row zipper.  Malformed channel families stop at the
shortest channel; verifier families are proved to have equal lengths. -/
def transitionDispatchMuxInvocationLabelPacketRowsFromChannels :
    List (List UnaryFrameSym) → List (List UnaryFrameSym) →
      List (List UnaryFrameSym) → List (List UnaryFrameSym) →
        List (List UnaryFrameSym)
  | selector :: selectors, coordinates :: coordinateRows,
      whenTrue :: trueRows, whenFalse :: falseRows =>
      selector :: coordinates :: whenTrue :: whenFalse ::
        transitionDispatchMuxInvocationLabelPacketRowsFromChannels
          selectors coordinateRows trueRows falseRows
  | _, _, _, _ => []

/-- Zipping the four row projections of a view family reconstructs exactly
the canonical four-row packet family. -/
theorem transitionDispatchMuxInvocationLabelPacketRowsFromChannels_maps
    (views : List TransitionDispatchMuxInvocationView) :
    transitionDispatchMuxInvocationLabelPacketRowsFromChannels
        (views.map fun view => encodeUnaryFrame [view.selector])
        (views.map fun view =>
          transitionDispatchMuxCoordinateRowFrames view.coordinates)
        (views.map fun view => encodeUnaryFrame view.whenTrue)
        (views.map fun view => encodeUnaryFrame view.whenFalse) =
      views.flatMap TransitionDispatchMuxInvocationView.labelPacketRows := by
  induction views with
  | nil => rfl
  | cons view views ih =>
      simp only [List.map_cons, List.flatMap_cons,
        transitionDispatchMuxInvocationLabelPacketRowsFromChannels,
        TransitionDispatchMuxInvocationView.labelPacketRows]
      rw [ih]
      rfl

/-- Canonical four-channel family reconstructed from all verifier transition
views in seed-major, label-major order. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    TransitionDispatchMuxInvocationLabelPacketChannelFamily :=
  let views := (verifierTransitionRowSeeds W input).flatMap fun seed =>
    transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed
  { selectorRows := views.map fun view => encodeUnaryFrame [view.selector]
    coordinateRows := views.map fun view =>
      transitionDispatchMuxCoordinateRowFrames view.coordinates
    trueRows := views.map fun view => encodeUnaryFrame view.whenTrue
    falseRows := views.map fun view => encodeUnaryFrame view.whenFalse }

/-- The four typed row encodings are precisely the four concrete label-channel
streams already produced by the descriptor pipelines. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily_encodings
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    let family :=
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
        W input
    encodeTransitionDispatchMuxInvocationLabelPacketChannelRows
          family.selectorRows =
        verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
          W input ∧
      encodeTransitionDispatchMuxInvocationLabelPacketChannelRows
          family.coordinateRows =
        verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
          W input ∧
      encodeTransitionDispatchMuxInvocationLabelPacketChannelRows
          family.trueRows =
        verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
          W input ∧
      encodeTransitionDispatchMuxInvocationLabelPacketChannelRows
          family.falseRows =
        verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
          W input := by
  dsimp only [
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily]
  unfold encodeTransitionDispatchMuxInvocationLabelPacketChannelRows
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
  repeat' constructor
  all_goals
    simp [List.flatMap_assoc, List.flatMap_map]

/-- Reassembling the canonical four channel rows yields the exact unprepared
label-packet byte stream consumed by the verified downstream pipeline. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames_eq_channelReassembly
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    let family :=
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily
        W input
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames W input =
      encodeTransitionDispatchMuxInvocationLabelPacketChannelRows
        (transitionDispatchMuxInvocationLabelPacketRowsFromChannels
          family.selectorRows family.coordinateRows family.trueRows
          family.falseRows) := by
  dsimp only [
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketChannelFamily]
  rw [transitionDispatchMuxInvocationLabelPacketRowsFromChannels_maps]
  let views := (verifierTransitionRowSeeds W input).flatMap fun seed =>
    transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed
  have hpacket :=
    encode_transitionDispatchMuxInvocationLabelPacketFamily views
  unfold encodeUnaryFrameMarkedRowFamily
    transitionDispatchMuxInvocationLabelPacketFamily at hpacket
  change verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
      W input =
    (views.flatMap
      TransitionDispatchMuxInvocationView.labelPacketRows).flatMap
        (fun row => row ++ [.frameEnd])
  rw [hpacket]
  unfold verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
    views
  exact List.flatMap_assoc.symm

end CLRS.Chapter34.Turing.CookLevin
