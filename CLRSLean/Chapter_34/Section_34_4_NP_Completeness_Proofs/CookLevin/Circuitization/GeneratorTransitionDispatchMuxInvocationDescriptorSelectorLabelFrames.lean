import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSelectorFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedWidthPacketNormalize

/-!
# Label boundaries for the routed dispatch selector channel

The recovered selector source is one flat ordinary unary frame.  Each selector
is a one-field packet.  Reusing the fixed-width packet marker at width one and
its standard normalizer produces one canonical marked unary row per program
label, without changing the selector payload.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One singleton unary row for every dispatch selector, in transition-row
and program-label order. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List Nat) :=
  ((verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchSelectors W.machine.tm)).map fun selector => [selector]

theorem
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_eq_valueRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames W input =
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows
        W input).flatMap encodeUnaryFrame := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_eq]
  rw [verifierTransitionDispatchSelectorFrames_eq]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows
  simp [encodeUnaryFrame, List.flatMap_map]

theorem
    verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows_width
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ row ∈
        verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows
          W input,
      row.length = 1 := by
  intro row hrow
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows at hrow
  rw [List.mem_map] at hrow
  rcases hrow with ⟨selector, hselector, rfl⟩
  rfl

/-- Compact width-one packets: the selector's final separator has become its
physical label boundary. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedWidthPackets 1 (by omega)
    (verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames W input)

theorem
    verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames
        W input =
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows
        W input).flatMap encodeUnaryFrameFixedWidthPacket := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_eq_valueRows]
  exact rewriteUnaryFrameFixedWidthPackets_encode 1 (by omega) _
    (verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows_width
      W input)

/-- Canonical label-marked selector stream, with the ordinary unary field
separator restored immediately before every `frameEnd`. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  restoreUnaryFrameFixedWidthPacketSeparators
    (verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames
      W input)

/-- The concrete selector channel is exactly one canonical marked singleton
row per actual dispatch selector. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchSelectors W.machine.tm seed).flatMap fun selector =>
          encodeUnaryFrame [selector] ++ [.frameEnd] := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames_eq]
  rw [restoreUnaryFrameFixedWidthPacketSeparators_family]
  · unfold
      verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows
    rw [List.flatMap_map, List.flatMap_assoc]
  · intro row hrow
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorSelectorValueRows at hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨selector, hselector, rfl⟩
    simp

/-- The width-one physical packet marker composes with the recovered selector
source in polynomial time. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_computableInPolyTime
        W)
      (unaryFrameFixedWidthPacketMark_computableInPolyTime 1 (by omega))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedWidthPackets 1 (by omega)
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames
        W input))
  simpa only [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames]
    using Classical.choice composed

/-- The complete selector boundary restoration is a concrete polynomial-time
TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames_computableInPolyTime
        W)
      restoreUnaryFrameFixedWidthPacketSeparators_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => restoreUnaryFrameFixedWidthPacketSeparators
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorCompactLabelFrames
        W input))
  simpa only [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
