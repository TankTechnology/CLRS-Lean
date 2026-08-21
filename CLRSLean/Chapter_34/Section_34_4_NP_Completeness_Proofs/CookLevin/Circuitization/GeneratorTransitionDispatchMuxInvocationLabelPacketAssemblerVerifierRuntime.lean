import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerRuntime

/-!
# Verifier specialization of polynomial-time mux packet assembly

This module instantiates the typed aligned-family transducer with the actual
label views reconstructed from every verifier transition row.  It identifies
both sides with the existing canonical verifier streams, leaving only the
upstream production of the prepared packet encoding as a separate obligation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The actual verifier label family packaged with its established alignment
invariant. -/
noncomputable def verifierTransitionDispatchMuxInvocationAlignedViewFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    AlignedTransitionDispatchMuxInvocationViewFamily :=
  { views := verifierTransitionDispatchMuxInvocationViews W input
    rowAligned :=
      verifierTransitionDispatchMuxInvocationViews_rowAligned W input }

/-- The typed-family input encoding is literally the prepared verifier packet
stream consumed by the concrete assembler. -/
theorem
    verifierTransitionDispatchMuxInvocationAlignedViewFamily_preparedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchMuxInvocationAlignedViewFamily W input
      ).preparedFrames =
      verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames_eq]
  rfl

/-- Reconstructing affine segments from the typed verifier views gives the
canonical segment family used by the transition circuit. -/
theorem verifierTransitionDispatchMuxInvocationAlignedViewFamily_segments
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchMuxInvocationAlignedViewFamily W input
      ).segments =
      verifierTransitionDispatchMuxInvocationSegments W input := by
  rw [← verifierTransitionDispatchMuxDescriptorInvocationSegments_eq W input]
  unfold verifierTransitionDispatchMuxInvocationAlignedViewFamily
    AlignedTransitionDispatchMuxInvocationViewFamily.segments
    verifierTransitionDispatchMuxInvocationViews
    verifierTransitionDispatchMuxDescriptorInvocationSegments
    transitionDispatchMuxDescriptorInvocationSegments
  exact List.flatMap_assoc

/-- From the actual prepared verifier label packets, one fixed
polynomial-time TM2 emits exactly the dispatch-mux gate frames occurring in
the canonical transition circuit. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationFrames_fromPreparedLabelPackets_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime
      (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
        W) id
      (verifierTransitionDispatchMuxInvocationFrames W) := by
  let generic :=
    transitionDispatchMuxInvocationFrames_fromAlignedViews_computableInPolyTime
  exact
    { tm := generic.tm
      inputAlphabet := generic.inputAlphabet
      outputAlphabet := generic.outputAlphabet
      time := generic.time
      outputsFun := fun input => by
        have run := generic.outputsFun
          (verifierTransitionDispatchMuxInvocationAlignedViewFamily W input)
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationAlignedViewFamily_preparedFrames,
          verifierTransitionDispatchMuxInvocationAlignedViewFamily_segments,
          verifierTransitionDispatchMuxInvocationSegments_frames W input]
          using run }

end CLRS.Chapter34.Turing.CookLevin
