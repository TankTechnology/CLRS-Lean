import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitPacketSimulation

/-!
# Family simulation for the dynamic four-way splitter

Well-sized packets package the three width equations required by the physical
counter discipline.  The family theorem streams any list of such packets
through one fixed controller and then exposes a complete halt run.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev splitStep :=
  step unaryFrameLengthPrefixedFourWaySplitRevProgram

/-- One semantically well-sized input packet for the dynamic splitter. -/
structure UnaryFrameLengthPrefixedFourWayPacket where
  width : Nat
  selector : Nat
  coordinates : List Nat
  whenTrue : List Nat
  whenFalse : List Nat
  coordinates_length : coordinates.length = 3 * width
  whenTrue_length : whenTrue.length = width
  whenFalse_length : whenFalse.length = width

namespace UnaryFrameLengthPrefixedFourWayPacket

def sourceFrames (packet : UnaryFrameLengthPrefixedFourWayPacket) :
    List UnaryFrameSym :=
  encodeUnaryFrameLengthPrefixedFourWaySplitInput packet.width packet.selector
    packet.coordinates packet.whenTrue packet.whenFalse

def outputFrames (packet : UnaryFrameLengthPrefixedFourWayPacket) :
    List UnaryFrameSym :=
  encodeUnaryFrameLengthPrefixedFourWaySplitOutput packet.selector
    packet.coordinates packet.whenTrue packet.whenFalse

def steps (packet : UnaryFrameLengthPrefixedFourWayPacket) : Nat :=
  unaryFrameLengthPrefixedFourWaySplitPacketSteps packet.width packet.selector
    packet.coordinates packet.whenTrue packet.whenFalse

end UnaryFrameLengthPrefixedFourWayPacket

/-- Concrete source stream for a packet family. -/
def encodeUnaryFrameLengthPrefixedFourWayPacketFamily
    (packets : List UnaryFrameLengthPrefixedFourWayPacket) :
    List UnaryFrameSym :=
  packets.flatMap UnaryFrameLengthPrefixedFourWayPacket.sourceFrames

/-- Forward four-row stream denoted by a packet family. -/
def unaryFrameLengthPrefixedFourWayPacketFamilyOutput
    (packets : List UnaryFrameLengthPrefixedFourWayPacket) :
    List UnaryFrameSym :=
  packets.flatMap UnaryFrameLengthPrefixedFourWayPacket.outputFrames

/-- Exact controller steps before the empty-input finish transition. -/
def unaryFrameLengthPrefixedFourWayPacketFamilySteps :
    List UnaryFrameLengthPrefixedFourWayPacket → Nat
  | [] => 0
  | packet :: rest => packet.steps +
      unaryFrameLengthPrefixedFourWayPacketFamilySteps rest

/-- Stale pop buffer after the family, used only at the loop boundary. -/
def unaryFrameLengthPrefixedFourWayPacketFamilyBuffer
    (packets : List UnaryFrameLengthPrefixedFourWayPacket)
    (initial : Option UnaryFrameSym) : Option UnaryFrameSym :=
  match packets with
  | [] => initial
  | _ :: rest =>
      unaryFrameLengthPrefixedFourWayPacketFamilyBuffer rest (some .frameEnd)

/-- Exact streaming simulation for a complete packet family. -/
def unaryFrameLengthPrefixedFourWaySplit_family
    (packets : List UnaryFrameLengthPrefixedFourWayPacket)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth buffer₁ buffer₂
        false
        (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets ++ tail)
        output 0 0 0)
      (some (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth
        (unaryFrameLengthPrefixedFourWayPacketFamilyBuffer packets buffer₁)
        buffer₂ false tail
        ((unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse ++
          output)
        0 0 0))
      (unaryFrameLengthPrefixedFourWayPacketFamilySteps packets) := by
  induction packets generalizing buffer₁ output with
  | nil => exact EvalsToInTime.refl splitStep _
  | cons packet rest ih =>
      have hpacket := unaryFrameLengthPrefixedFourWaySplit_packet
        packet.width packet.selector packet.coordinates packet.whenTrue
        packet.whenFalse packet.coordinates_length packet.whenTrue_length
        packet.whenFalse_length buffer₁ buffer₂
        (encodeUnaryFrameLengthPrefixedFourWayPacketFamily rest ++ tail) output
      have hrest := ih (some UnaryFrameSym.frameEnd)
        ((packet.outputFrames).reverse ++ output)
      let full := EvalsToInTime.trans splitStep packet.steps
        (unaryFrameLengthPrefixedFourWayPacketFamilySteps rest)
        _ _ _ hpacket hrest
      convert full using 1
      · simp [encodeUnaryFrameLengthPrefixedFourWayPacketFamily,
          UnaryFrameLengthPrefixedFourWayPacket.sourceFrames,
          List.append_assoc]
      · simp [unaryFrameLengthPrefixedFourWayPacketFamilyBuffer,
          unaryFrameLengthPrefixedFourWayPacketFamilyOutput,
          UnaryFrameLengthPrefixedFourWayPacket.outputFrames,
          List.reverse_append, List.append_assoc]
      · simp [unaryFrameLengthPrefixedFourWayPacketFamilySteps,
          UnaryFrameLengthPrefixedFourWayPacket.steps, Nat.add_comm]

/-- The reversed-output controller reaches its actual halt configuration. -/
def unaryFrameLengthPrefixedFourWaySplitRev_haltRun
    (packets : List UnaryFrameLengthPrefixedFourWayPacket) :
    EvalsToInTime splitStep
      (initialCfg unaryFrameLengthPrefixedFourWaySplitRevProgram
        (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets))
      (some (haltCfg unaryFrameLengthPrefixedFourWaySplitRevProgram
        (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse))
      (unaryFrameLengthPrefixedFourWayPacketFamilySteps packets + 2) := by
  have hfamily := unaryFrameLengthPrefixedFourWaySplit_family packets
    none none [] []
  have hfamily' : EvalsToInTime splitStep
      (initialCfg unaryFrameLengthPrefixedFourWaySplitRevProgram
        (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets))
      (some (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth
        (unaryFrameLengthPrefixedFourWayPacketFamilyBuffer packets none)
        none false []
        (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse
        0 0 0))
      (unaryFrameLengthPrefixedFourWayPacketFamilySteps packets) := by
    simpa [initialCfg, unaryFrameLengthPrefixedFourWaySplitCfg,
      unaryFrameLengthPrefixedFourWaySplitRevProgram] using hfamily
  let finishCfg := unaryFrameLengthPrefixedFourWaySplitCfg .finish none none
    false [] (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse
    0 0 0
  have hfinish : EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth
        (unaryFrameLengthPrefixedFourWayPacketFamilyBuffer packets none)
        none false []
        (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse
        0 0 0)
      (some finishCfg) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hhalt : EvalsToInTime splitStep finishCfg
      (some (haltCfg unaryFrameLengthPrefixedFourWaySplitRevProgram
        (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse))
      1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let hbody := EvalsToInTime.trans splitStep
    (unaryFrameLengthPrefixedFourWayPacketFamilySteps packets) 1
    _ _ _ hfamily' hfinish
  let full := EvalsToInTime.trans splitStep
    (1 + unaryFrameLengthPrefixedFourWayPacketFamilySteps packets) 1
    _ finishCfg _ hbody hhalt
  convert full using 1 <;> omega

end CLRS.Chapter34.Turing.PolyBuilder
