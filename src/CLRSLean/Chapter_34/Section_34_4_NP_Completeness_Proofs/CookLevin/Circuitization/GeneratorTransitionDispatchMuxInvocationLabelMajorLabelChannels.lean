import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorLabelChannels

/-!
# Closed label-major channel interface

All four final row channels now arise by concrete polynomial-time continuations
of the same label-major descriptor source.  This module pins those outputs to
the four projections of the canonical label-packet family and bundles their
machine witnesses.  It deliberately does not claim a four-way fan-out or row
zipper; that is the next physical construction boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_existing,
    ←
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketSelectorFrames_eq]

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_existing,
    ←
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketCoordinateFrames_eq]

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_eq_existing,
    ← verifierTransitionDispatchMuxInvocationDescriptorLabelPacketTrueFrames_eq]

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_channel
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_eq_existing,
    ← verifierTransitionDispatchMuxInvocationDescriptorLabelPacketFalseFrames_eq]

/-- Machine-level evidence for the four independently executed label-major
channels.  A consumer must still provide a physical same-input fan-out and
row zipper before treating these witnesses as one packet compiler. -/
structure TransitionDispatchMuxInvocationLabelMajorChannelCompilers
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) where
  selector : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames W)
  coordinates : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames W)
  whenTrue : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames W)
  whenFalse : _root_.Turing.TM2ComputableInPolyTime id id
    (verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames W)

/-- The four concrete label-major pipelines satisfy the common compiler
interface. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorChannelCompilers
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TransitionDispatchMuxInvocationLabelMajorChannelCompilers W :=
  { selector :=
      verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_computableInPolyTime
        W
    coordinates :=
      verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_computableInPolyTime
        W
    whenTrue :=
      verifierTransitionDispatchMuxInvocationLabelMajorTrueLabelFrames_computableInPolyTime
        W
    whenFalse :=
      verifierTransitionDispatchMuxInvocationLabelMajorFalseLabelFrames_computableInPolyTime
        W }

end CLRS.Chapter34.Turing.CookLevin
