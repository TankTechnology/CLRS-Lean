import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedWidthPacketMark

/-!
# Physical row packets for unified dispatch-mux descriptors

The affine descriptor source is one uninterrupted ordinary unary stream.  This
module instantiates the fixed-width packet marker at the verifier-fixed size of
one complete selector/coordinate/true-arm/false-arm descriptor packet.  The
result has a real `frameEnd` after every transition-row packet, so later TM2
passes may duplicate and route that one physical source without oracle-side
fan-out.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Number of unary fields in one complete mux descriptor packet. -/
noncomputable def transitionDispatchMuxInvocationDescriptorPacketWidth
    (tm : _root_.Turing.FinTM2) : Nat :=
  (transitionDispatchMuxInvocationDescriptorForms tm).length

/-- Every packet contains at least the selector of one program label. -/
theorem transitionDispatchMuxInvocationDescriptorPacketWidth_pos
    (tm : _root_.Turing.FinTM2) :
    0 < transitionDispatchMuxInvocationDescriptorPacketWidth tm := by
  have hlabels : 0 < (programLabels tm).length :=
    List.length_pos_of_ne_nil (programLabels_nonempty tm)
  unfold transitionDispatchMuxInvocationDescriptorPacketWidth
    transitionDispatchMuxInvocationDescriptorForms
    transitionDispatchSelectorForms
  simp only [List.length_append, List.length_map]
  omega

/-- Runtime evaluation preserves the fixed field count of the descriptor
table. -/
theorem transitionDispatchMuxInvocationDescriptorValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationDescriptorValues tm seed).length =
      transitionDispatchMuxInvocationDescriptorPacketWidth tm := by
  rw [← transitionDispatchMuxInvocationDescriptorForms_value tm seed]
  simp [transitionDispatchMuxInvocationDescriptorPacketWidth,
    affineUnaryTripleMap]

/-- Concrete packet-marked descriptor stream generated for a verifier word. -/
noncomputable def verifierTransitionDispatchMuxInvocationDescriptorPacketFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedWidthPackets
    (transitionDispatchMuxInvocationDescriptorPacketWidth W.machine.tm)
    (transitionDispatchMuxInvocationDescriptorPacketWidth_pos W.machine.tm)
    (verifierTransitionDispatchMuxInvocationDescriptorFrames W input)

private theorem descriptorPacket_encode_flatMap
    {α : Type} (rows : List α) (values : α → List Nat) :
    encodeUnaryFrame (rows.flatMap values) =
      rows.flatMap fun row => encodeUnaryFrame (values row) := by
  unfold encodeUnaryFrame
  rw [List.flatMap_assoc]

/-- The concrete marker places exactly one physical boundary after every
complete seed-local descriptor packet. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorPacketFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorPacketFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrameFixedWidthPacket
          (transitionDispatchMuxInvocationDescriptorValues W.machine.tm
            seed) := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorPacketFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorFrames_eq]
  rw [descriptorPacket_encode_flatMap]
  let packets := (verifierTransitionRowSeeds W input).map
    (transitionDispatchMuxInvocationDescriptorValues W.machine.tm)
  have hwidth : ∀ packet ∈ packets,
      packet.length =
        transitionDispatchMuxInvocationDescriptorPacketWidth W.machine.tm := by
    intro packet hpacket
    rw [List.mem_map] at hpacket
    rcases hpacket with ⟨seed, hseed, rfl⟩
    exact transitionDispatchMuxInvocationDescriptorValues_length
      W.machine.tm seed
  have marked := rewriteUnaryFrameFixedWidthPackets_encode
    (transitionDispatchMuxInvocationDescriptorPacketWidth W.machine.tm)
    (transitionDispatchMuxInvocationDescriptorPacketWidth_pos W.machine.tm)
    packets hwidth
  simpa [packets, List.flatMap_map] using marked

/-- From the original verifier word, one fixed polynomial-time TM2 now emits
the physically packetized unified mux descriptor stream. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorPacketFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorPacketFrames W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationDescriptorFrames_computableInPolyTime W
  let marker := unaryFrameFixedWidthPacketMark_computableInPolyTime
    (transitionDispatchMuxInvocationDescriptorPacketWidth W.machine.tm)
    (transitionDispatchMuxInvocationDescriptorPacketWidth_pos W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      descriptors marker
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameFixedWidthPackets
        (transitionDispatchMuxInvocationDescriptorPacketWidth W.machine.tm)
        (transitionDispatchMuxInvocationDescriptorPacketWidth_pos W.machine.tm)
        (verifierTransitionDispatchMuxInvocationDescriptorFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
