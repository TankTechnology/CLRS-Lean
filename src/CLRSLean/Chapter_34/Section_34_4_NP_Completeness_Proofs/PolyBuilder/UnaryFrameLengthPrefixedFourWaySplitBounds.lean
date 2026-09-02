import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitFamilySimulation
import Mathlib.Tactic

/-!
# Linear bounds for the dynamic four-way splitter

The input itself contains every unary payload symbol and enough separators to
pay for the counter operations.  Consequently the complete fixed controller
has a uniform linear bound in the concrete source-stream length.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Every unary field contributes at least its terminating separator. -/
theorem length_le_encodeUnaryFrame_length (values : List Nat) :
    values.length ≤ (encodeUnaryFrame values).length := by
  rw [encodeUnaryFrame_length]
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- Exact concrete source length of one self-described packet. -/
theorem UnaryFrameLengthPrefixedFourWayPacket.sourceFrames_length
    (packet : UnaryFrameLengthPrefixedFourWayPacket) :
    packet.sourceFrames.length =
      packet.width + 1 + (packet.selector + 1) +
        (encodeUnaryFrame packet.coordinates).length +
        (encodeUnaryFrame packet.whenTrue).length +
        (encodeUnaryFrame packet.whenFalse).length + 1 := by
  simp [UnaryFrameLengthPrefixedFourWayPacket.sourceFrames,
    encodeUnaryFrameLengthPrefixedFourWaySplitInput,
    encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]
  omega

/-- One packet costs at most six builder steps per concrete input symbol. -/
theorem UnaryFrameLengthPrefixedFourWayPacket.steps_le_sourceFrames
    (packet : UnaryFrameLengthPrefixedFourWayPacket) :
    packet.steps ≤ 6 * packet.sourceFrames.length := by
  have hcoordinates := length_le_encodeUnaryFrame_length packet.coordinates
  have htrue := length_le_encodeUnaryFrame_length packet.whenTrue
  have hfalse := length_le_encodeUnaryFrame_length packet.whenFalse
  rw [packet.coordinates_length] at hcoordinates
  rw [packet.whenTrue_length] at htrue
  rw [packet.whenFalse_length] at hfalse
  rw [packet.sourceFrames_length]
  simp only [UnaryFrameLengthPrefixedFourWayPacket.steps,
    unaryFrameLengthPrefixedFourWaySplitPacketSteps,
    unaryFrameLengthPrefixedFourWaySplitSectionSteps]
  rw [packet.coordinates_length, packet.whenTrue_length,
    packet.whenFalse_length]
  omega

/-- Family body steps are linear in the actual concatenated source. -/
theorem unaryFrameLengthPrefixedFourWayPacketFamilySteps_le
    (packets : List UnaryFrameLengthPrefixedFourWayPacket) :
    unaryFrameLengthPrefixedFourWayPacketFamilySteps packets ≤
      6 * (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets).length := by
  induction packets with
  | nil => simp [unaryFrameLengthPrefixedFourWayPacketFamilySteps,
      encodeUnaryFrameLengthPrefixedFourWayPacketFamily]
  | cons packet rest ih =>
      have hpacket := packet.steps_le_sourceFrames
      rw [unaryFrameLengthPrefixedFourWayPacketFamilySteps]
      have hsource :
          encodeUnaryFrameLengthPrefixedFourWayPacketFamily (packet :: rest) =
            packet.sourceFrames ++
              encodeUnaryFrameLengthPrefixedFourWayPacketFamily rest := rfl
      rw [hsource, List.length_append]
      omega

end CLRS.Chapter34.Turing.PolyBuilder
