import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowHaltedOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource

/-!
# Canonical complete validity-row input packets

This file pins the exact row-at-a-time target of the remaining concrete
source controller.  The three already compiled raw-input sources are proved
to be synchronized projections of one canonical packet list; no permutation
or length-only statement is used.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Three delimiter-bearing fragments owned by one validity-row invocation. -/
structure ValidityRowOperandPacket where
  oneHotPrefix : List UnaryFrameSym
  halted : List UnaryFrameSym
  tail : List UnaryFrameSym
deriving DecidableEq, Repr

/-- Concatenate one row's fragments in complete-controller consumption order. -/
def encodeValidityRowOperandPacket
    (packet : ValidityRowOperandPacket) : List UnaryFrameSym :=
  packet.oneHotPrefix ++ packet.halted ++ packet.tail

/-- Canonical fragment packet of one already expanded validity row. -/
def validityRowOperandPacket
    (frame : AffineValidityRowFrame) : ValidityRowOperandPacket :=
  { oneHotPrefix :=
      .tick :: (encodeAffineExactlyOneFamily frame.oneHotFrames ++
        [.frameEnd])
    halted :=
      encodeUnaryFrame
        [frame.haltedStart, frame.haltedLeft, frame.haltedRight] ++
          [.frameEnd]
    tail := encodeAffineValidityTailFrame frame.tailFrame }

/-- Row packets for the canonical verifier validity-frame family. -/
def verifierValidityRowOperandPackets
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List ValidityRowOperandPacket :=
  (verifierValidityRowFramesByLength W input.length).map
    validityRowOperandPacket

/-- Packet-family encoding, including the outer family terminator. -/
def encodeValidityRowOperandPacketFamily
    (packets : List ValidityRowOperandPacket) : List UnaryFrameSym :=
  packets.flatMap encodeValidityRowOperandPacket ++ [.frameEnd]

/-- Direct row-seed specification of the complete family input.  This is the
semantic output target for the remaining fixed source controller. -/
def validityRowSeedFamilyInput (tm : _root_.Turing.FinTM2) :
    List ValidityRowSeed → List UnaryFrameSym
  | [] => [.frameEnd]
  | seed :: rest =>
      .tick ::
        (encodeAffineValidityRowFrame (expandValidityRowSeed tm seed) ++
          validityRowSeedFamilyInput tm rest)

/-- The recursive seed target is exactly the established family encoding. -/
theorem validityRowSeedFamilyInput_eq
    (tm : _root_.Turing.FinTM2) (seeds : List ValidityRowSeed) :
    validityRowSeedFamilyInput tm seeds =
      encodeAffineValidityRowFamilyInput
        (seeds.map (expandValidityRowSeed tm)) := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [validityRowSeedFamilyInput,
        encodeAffineValidityRowFamilyInput,
        encodeAffineValidityRowFamily, ih, List.append_assoc]

/-- Raw-verifier specialization of the complete row-family target. -/
def verifierValidityRowFamilyInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  validityRowSeedFamilyInput W.machine.tm
    (verifierValidityRowSeeds W input)

/-- The seed target is byte-for-byte the canonical complete family input. -/
theorem verifierValidityRowFamilyInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowFamilyInputTarget W input =
      encodeAffineValidityRowFamilyInput
        (verifierValidityRowFramesByLength W input.length) := by
  unfold verifierValidityRowFamilyInputTarget
  rw [validityRowSeedFamilyInput_eq,
    verifierValidityRowSeeds_expand_eq_frames]

/-- The complete family encoding is literally the row-packet encoding. -/
theorem verifierValidityRowFamilyInputTarget_eq_packets
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowFamilyInputTarget W input =
      encodeValidityRowOperandPacketFamily
        (verifierValidityRowOperandPackets W input) := by
  rw [verifierValidityRowFamilyInputTarget_eq_canonical]
  unfold verifierValidityRowOperandPackets
  generalize verifierValidityRowFramesByLength W input.length = frames
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [encodeAffineValidityRowFamilyInput,
        encodeAffineValidityRowFamily,
        encodeValidityRowOperandPacketFamily,
        encodeValidityRowOperandPacket, validityRowOperandPacket,
        encodeAffineValidityRowFrame, List.append_assoc]
      exact List.append_cancel_right ih

/-- The concrete one-hot source is the first projection of the synchronized
canonical packet list. -/
theorem verifierValidityRowOperandPackets_oneHot
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidityRowOperandPackets W input).flatMap
        (fun packet => packet.oneHotPrefix) =
      verifierValidityRowOneHotMarkedOperandFrames W input := by
  rw [verifierValidityRowOneHotMarkedOperandFrames_eq_canonical]
  simp [verifierValidityRowOperandPackets, validityRowOperandPacket,
    List.flatMap_map]

/-- The concrete halted source is the second projection of the synchronized
canonical packet list. -/
theorem verifierValidityRowOperandPackets_halted
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidityRowOperandPackets W input).flatMap
        (fun packet => packet.halted) =
      verifierValidityRowHaltedMarkedOperandFrames W input := by
  rw [verifierValidityRowHaltedMarkedOperandFrames_eq_frames]
  simp [verifierValidityRowOperandPackets, validityRowOperandPacket,
    List.flatMap_map]

/-- The concrete tail source is the third projection of the synchronized
canonical packet list. -/
theorem verifierValidityRowOperandPackets_tail
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidityRowOperandPackets W input).flatMap
        (fun packet => packet.tail) =
      verifierValidityRowTailOperandFrames W input := by
  rw [verifierValidityRowTailOperandFrames_eq_canonical]
  simp [verifierValidityRowOperandPackets, validityRowOperandPacket,
    List.flatMap_map]

end CLRS.Chapter34.Turing.CookLevin
