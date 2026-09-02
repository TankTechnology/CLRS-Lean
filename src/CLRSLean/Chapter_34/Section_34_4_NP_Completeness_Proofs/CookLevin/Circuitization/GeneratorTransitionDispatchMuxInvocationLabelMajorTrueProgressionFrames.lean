import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorTrueFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames

/-!
# Interpreting label-major true-arm descriptor rows

The label-major source exposes adjacent eight-field true-arm blocks.  This
module runs the established fixed-width interpreter directly after that new
physical source: it restores block boundaries, removes the verifier-fixed
leading drop amount, and exposes the ordinary seven-field affine progression
family.

The final equality is byte-for-byte, but the polynomial-time witness below is
not borrowed from the older four-way route: its first component is the
label-major true-row selector proved in the preceding module.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Mark each adjacent label-major true-arm descriptor block. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedWidthPackets 8 (by omega)
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames W input)

/-- Restore ordinary row separators inside every marked eight-field block. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  restoreUnaryFrameFixedWidthPacketSeparators
    (verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames W input)

/-- Delete the leading prefix-drop amount from every true-arm block. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixDrop 1
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames
      W input)

/-- Expose the canonical adjacent seven-field affine progression family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames
      W input)

/-- The label-major interpreter reaches exactly the established semantic
progression stream. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames
        W input =
      encodeAffineUnaryTripleProgressionFamily
        (verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
          W input) := by
  rw [show
      verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames
          W input =
        verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames
          W input by
      unfold
        verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames
        verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames
        verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames
        verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames
        verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames
        verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedPacketFrames
        verifierTransitionDispatchMuxInvocationDescriptorTrueNormalizedPacketFrames
        verifierTransitionDispatchMuxInvocationDescriptorTruePacketFrames
      rw [verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames_eq_existing]]
  exact
    verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames_eq
      W input

/-- Fixed-width marking remains polynomial-time from the label-major source. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames_computableInPolyTime
        W)
      (unaryFrameFixedWidthPacketMark_computableInPolyTime 8 (by omega))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedWidthPackets 8 (by omega)
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames] using
      Classical.choice composed

/-- Separator restoration remains polynomial-time from the raw word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames_computableInPolyTime
        W)
      restoreUnaryFrameFixedWidthPacketSeparators_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => restoreUnaryFrameFixedWidthPacketSeparators
      (verifierTransitionDispatchMuxInvocationLabelMajorTruePacketFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames]
    using Classical.choice composed

/-- Fixed-prefix deletion remains polynomial-time from the raw word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames_computableInPolyTime
        W)
      (unaryFrameFixedPrefixDrop_computableInPolyTime 1)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedPrefixDrop 1
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueNormalizedPacketFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames]
    using Classical.choice composed

set_option maxHeartbeats 600000

/-- The complete eight-to-seven-field interpretation is one concrete
polynomial-time TM2 whose source is the label-major true channel. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueDroppedPacketFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationLabelMajorTrueProgressionFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
