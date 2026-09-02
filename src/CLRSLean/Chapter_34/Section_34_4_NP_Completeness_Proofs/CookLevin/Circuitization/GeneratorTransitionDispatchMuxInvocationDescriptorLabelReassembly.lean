import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueLabelSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFalseLabelSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorViews

/-!
# Exact label-packet contract for dispatch-mux reassembly

The four descriptor interpreters now recover one selector, coordinate, true-
arm, and false-arm row per fixed program label.  This module fixes the exact
seed-major physical packet expected by the final streaming reassembler and
proves that the corresponding structured views expand byte-for-byte to the
already verified affine mux-invocation source.

No machine is hidden in this layer: the input packet and output source are
both explicit lists of `UnaryFrameSym`.  The later controller proof can
therefore concentrate solely on realizing this exact relation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Four canonical marked rows carrying one dispatch label.  The order is
chosen to match the data dependencies of the final assembler: selector,
fresh coordinates, true arm, then false arm. -/
def TransitionDispatchMuxInvocationView.labelPacketFrames
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  encodeUnaryFrame [view.selector] ++ [.frameEnd] ++
    transitionDispatchMuxCoordinateRowFrames view.coordinates ++
    [.frameEnd] ++
    encodeUnaryFrame view.whenTrue ++ [.frameEnd] ++
    encodeUnaryFrame view.whenFalse ++ [.frameEnd]

/-- Exact affine-progression source contributed by one reconstructed label
view. -/
def TransitionDispatchMuxInvocationView.sourceFrames
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  view.invocationSegments.flatMap
    AffineMuxInvocationProgression.sourceFrames

/-- Source frames obtained by reassembling a list of aligned label views. -/
def transitionDispatchMuxInvocationViewsSourceFrames
    (views : List TransitionDispatchMuxInvocationView) :
    List UnaryFrameSym :=
  affineMuxInvocationProgressionFamilySourceFrames
    (views.flatMap TransitionDispatchMuxInvocationView.invocationSegments)

/-- Reassembly is compatible with label boundaries: the generic affine
source of the concatenated segment family is exactly the concatenation of
the source contributed by each label view. -/
theorem transitionDispatchMuxInvocationViewsSourceFrames_eq
    (views : List TransitionDispatchMuxInvocationView) :
    transitionDispatchMuxInvocationViewsSourceFrames views =
      views.flatMap TransitionDispatchMuxInvocationView.sourceFrames := by
  unfold transitionDispatchMuxInvocationViewsSourceFrames
    TransitionDispatchMuxInvocationView.sourceFrames
  rw [affineMuxInvocationProgressionFamilySourceFrames_eq]
  exact List.flatMap_assoc

/-- Seed-major physical input contract for the final label reassembler. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed).flatMap
      TransitionDispatchMuxInvocationView.labelPacketFrames

/-- Every field of the physical reassembly contract is the corresponding
field of the actual proof-carrying dispatch artifact. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames_eq_artifacts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchArtifactsFromSeed W.machine.tm seed).flatMap
          fun artifact => artifact.muxInvocationView.labelPacketFrames := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFrames
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  rw [List.flatMap_map]

/-- The output side of the label-packet contract is literally the canonical
source already consumed by the verified affine mux controller. -/
theorem
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq_reassembledViews
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxDescriptorInvocationViews W.machine.tm
          seed).flatMap
            TransitionDispatchMuxInvocationView.sourceFrames := by
  unfold verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
    verifierTransitionDispatchMuxDescriptorInvocationSegments
  rw [affineMuxInvocationProgressionFamilySourceFrames_eq]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  unfold transitionDispatchMuxDescriptorInvocationSegments
    TransitionDispatchMuxInvocationView.sourceFrames
  exact List.flatMap_assoc

end CLRS.Chapter34.Turing.CookLevin
