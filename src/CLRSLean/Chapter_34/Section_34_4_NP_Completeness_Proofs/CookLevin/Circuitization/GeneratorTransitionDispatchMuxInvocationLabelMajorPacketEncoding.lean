import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorPacketSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMapCycle
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# Physical encoding of typed label-major descriptor packets

The preceding modules expose the concrete source as a cyclic delimiter map
and the local interpretation contract as typed packets.  Here those two
interfaces are joined byte-for-byte.  Every complete delimiter cycle is one
transition seed; inside it, each verifier-fixed delimiter group is exactly
one marked typed label packet.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Physical marked encoding of one typed descriptor packet. -/
def TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.frames
    {tm : _root_.Turing.FinTM2} (seed : TransitionRowSeed)
    (packet : TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm) :
    List UnaryFrameSym :=
  encodeUnaryFrameFixedWidthPacket (packet.descriptorValues seed)

/-- Marker-free body used to package typed descriptors as a generic marked
row family. -/
def TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.bodyFrames
    {tm : _root_.Turing.FinTM2} (seed : TransitionRowSeed)
    (packet : TransitionDispatchMuxInvocationLabelMajorDescriptorPacket tm) :
    List UnaryFrameSym :=
  encodeUnaryFrameFixedWidthPacketBody (packet.descriptorValues seed)

private theorem labelMajorFormGroups_fixed_encoding
    (seed : TransitionRowSeed) :
    ∀ (groups : List (List AffineUnaryTripleForm)),
      (∀ group ∈ groups, 0 < group.length) →
      encodeUnaryFrameWithFixedDelimiters
          ((groups.map fun group =>
            affineUnaryTripleMap group
              (transitionTailAffineSeed seed)).flatten)
          (groups.flatMap
            transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters) =
        (groups.map fun group =>
          affineUnaryTripleMap group
            (transitionTailAffineSeed seed)).flatMap
              encodeUnaryFrameFixedWidthPacket := by
  intro groups hnonempty
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      let values := affineUnaryTripleMap group
        (transitionTailAffineSeed seed)
      have hgroup : 0 < group.length := hnonempty group (by simp)
      have hgroups : ∀ other ∈ groups, 0 < other.length := by
        intro other hother
        exact hnonempty other (by simp [hother])
      have hvaluesLength : values.length = group.length := by
        simp [values, affineUnaryTripleMap]
      have hvalues : values ≠ [] := by
        intro hempty
        rw [hempty] at hvaluesLength
        simp at hvaluesLength
        omega
      have hdelimiterLength :
          values.length =
            (transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters
              group).length := by
        simp [transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters,
          hvaluesLength]
        omega
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _
        hdelimiterLength]
      rw [ih hgroups]
      apply congrArg (fun head =>
        head ++
          (groups.map fun other =>
            affineUnaryTripleMap other
              (transitionTailAffineSeed seed)).flatMap
                encodeUnaryFrameFixedWidthPacket)
      change encodeUnaryFrameWithFixedDelimiters values
          (transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters
            group) = encodeUnaryFrameFixedWidthPacket values
      unfold
        transitionDispatchMuxInvocationLabelMajorDescriptorGroupDelimiters
      rw [← hvaluesLength]
      rw [encodeUnaryFrameWithOwnFinalDelimiter values .frameEnd hvalues]
      cases hvaluesEq : values with
      | nil => exact False.elim (hvalues hvaluesEq)
      | cons value rest =>
          simpa [hvaluesEq] using
            (encodeUnaryFrameFixedWidthPacket_eq_body value rest).symm

private theorem
    transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups_fixed_encoding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
          tm seed).flatten
        (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable tm) =
      (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
        tm seed).flatMap encodeUnaryFrameFixedWidthPacket := by
  rw [←
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups_eq_canonical]
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
    transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
  exact labelMajorFormGroups_fixed_encoding seed _
    (transitionDispatchMuxInvocationLabelMajorDescriptorFormGroups_nonempty tm)

private theorem
    transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups_flatten_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
        tm seed).flatten.length =
      (transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable
        tm).length := by
  rw [transitionDispatchMuxInvocationLabelMajorDescriptorDelimiterTable_length]
  rw [←
    transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups_eq_canonical]
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorValueGroups
    transitionDispatchMuxInvocationLabelMajorDescriptorForms
  simp only [List.length_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro group hgroup
  simp [affineUnaryTripleMap]

/-- The actual cyclic delimiter machine output is the seed-major,
label-major concatenation of typed packet encodings. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames_eq_packets
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
          W.machine.tm seed).flatMap fun packet => packet.frames seed := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames_eq_canonical]
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorCanonicalMarkedDescriptorFrames
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
              W.machine.tm seed).flatten) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          (transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups
            W.machine.tm seed).flatten).flatten by
      induction verifierTransitionRowSeeds W input with
      | nil => rfl
      | cons seed seeds ih =>
          simp only [List.flatMap_cons, List.map_cons, List.flatten_cons]
          rw [ih]]
  rw [encodeUnaryFrameWithDelimiterCycle_eq_fixedRows]
  · rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    rw [
      transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups_fixed_encoding]
    rw [←
      transitionDispatchMuxInvocationLabelMajorDescriptorPackets_values]
    simp [TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.frames,
      List.flatMap_map]
  · intro row hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨seed, hseed, rfl⟩
    exact
      transitionDispatchMuxInvocationLabelMajorCanonicalDescriptorValueGroups_flatten_length
        W.machine.tm seed

/-- Typed marked-row family physically emitted by the raw-input source. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
        W.machine.tm seed).map fun packet => packet.bodyFrames seed
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_flatMap] at hrow
      rcases hrow with ⟨seed, hseed, hrow⟩
      rw [List.mem_map] at hrow
      rcases hrow with ⟨packet, hpacket, rfl⟩
      exact encodeUnaryFrameFixedWidthPacketBody_frameEnd_free _ symbol
        hsymbol }

/-- The generic marked-row encoding of the typed family is byte-for-byte the
concrete label-major descriptor source. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketFamily
          W input) =
      verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames_eq_packets]
  unfold encodeUnaryFrameMarkedRowFamily
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketFamily
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro packet hpacket
  unfold
    TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.bodyFrames
    TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.frames
  have hne : packet.descriptorValues seed ≠ [] := by
    simp [TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.descriptorValues]
  cases hvalues : packet.descriptorValues seed with
  | nil => exact False.elim (hne hvalues)
  | cons value values =>
      simpa [hvalues] using
        (encodeUnaryFrameFixedWidthPacket_eq_body value values).symm

/-- The raw verifier input is compiled by one concrete polynomial-time TM2
into the typed, physically marked descriptor packet family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketFamily
        W) := by
  let source :=
    verifierTransitionDispatchMuxInvocationLabelMajorMarkedDescriptorFrames_computableInPolyTime
      W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationLabelMajorDescriptorPacketFamily_encoding_eq
            W input] using run }

end CLRS.Chapter34.Turing.CookLevin
