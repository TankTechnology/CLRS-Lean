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

/-! ## Single-source fixed operands with compact one-hot payload -/

/-- Runtime row seed in the generic affine source's field order. -/
def validityRowUnifiedAffineSeed
    (height start rowBase : Nat) : AffineUnaryTripleSeed :=
  { first := height, second := start, third := rowBase }

/-- The halted triple followed by every verifier-fixed tail operand form.
All coefficients depend only on the fixed verifier machine. -/
noncomputable def arithmeticValidityRowFixedOperandForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  [ { constant := arithmeticRawOneHotGateCountConstant tm
      first := arithmeticRawOneHotGateCountHeightCoeff tm
      second := 1
      third := 0 },
    { constant := 0, first := 0, second := 0, third := 1 },
    { constant := labelCount tm + 1
      first := 0
      second := 0
      third := 1 },
    { constant := 0, first := 0, second := 0, third := 0 } ] ++
    arithmeticValidityTailFixedOperandForms tm

/-- The unified affine table is value-exact for the halted fields and the
complete fixed part of the canonical tail invocation. -/
theorem arithmeticValidityRowFixedOperandForms_eq
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityRowFixedOperandForms tm)
        (validityRowUnifiedAffineSeed height start rowBase) =
      [ arithmeticHaltedMatchStart tm height start,
        rowBase,
        arithmeticNoneLabelWire tm rowBase,
        0 ] ++
        arithmeticValidityTailFixedOperandValues
          tm height start rowBase := by
  unfold arithmeticValidityRowFixedOperandForms
  rw [show affineUnaryTripleMap
      ([ { constant := arithmeticRawOneHotGateCountConstant tm
           first := arithmeticRawOneHotGateCountHeightCoeff tm
           second := 1
           third := 0 },
         { constant := 0, first := 0, second := 0, third := 1 },
         { constant := labelCount tm + 1
           first := 0
           second := 0
           third := 1 },
         { constant := 0, first := 0, second := 0, third := 0 } ] ++
        arithmeticValidityTailFixedOperandForms tm)
        (validityRowUnifiedAffineSeed height start rowBase) =
      affineUnaryTripleMap
          [ { constant := arithmeticRawOneHotGateCountConstant tm
              first := arithmeticRawOneHotGateCountHeightCoeff tm
              second := 1
              third := 0 },
            { constant := 0, first := 0, second := 0, third := 1 },
            { constant := labelCount tm + 1
              first := 0
              second := 0
              third := 1 },
            { constant := 0, first := 0, second := 0, third := 0 } ]
          (validityRowUnifiedAffineSeed height start rowBase) ++
        affineUnaryTripleMap (arithmeticValidityTailFixedOperandForms tm)
          (validityRowUnifiedAffineSeed height start rowBase) by
    simp [affineUnaryTripleMap]]
  rw [show affineUnaryTripleMap
        [ { constant := arithmeticRawOneHotGateCountConstant tm
            first := arithmeticRawOneHotGateCountHeightCoeff tm
            second := 1
            third := 0 },
          { constant := 0, first := 0, second := 0, third := 1 },
          { constant := labelCount tm + 1
            first := 0
            second := 0
            third := 1 },
          { constant := 0, first := 0, second := 0, third := 0 } ]
        (validityRowUnifiedAffineSeed height start rowBase) =
      [ arithmeticHaltedMatchStart tm height start,
        rowBase,
        arithmeticNoneLabelWire tm rowBase,
        0 ] by
    simp [affineUnaryTripleMap, affineUnaryTripleFormValue,
      validityRowUnifiedAffineSeed, arithmeticHaltedMatchStart,
      arithmeticNoneLabelWire,
      arithmeticRawOneHotGateCount_eq_affine]
    ring_nf
    simp]
  congr 1
  have h := arithmeticValidityTailFixedOperandForms_eq
    tm height start rowBase
  change affineUnaryTripleMap (arithmeticValidityTailFixedOperandForms tm)
      { first := height, second := start, third := rowBase } =
    arithmeticValidityTailFixedOperandValues tm height start rowBase at h
  simpa [validityRowUnifiedAffineSeed] using h

/-- One seed plus its full compact one-hot row, before any projection to
final-conjunction output invocations. -/
noncomputable def verifierValidityRowUnifiedPayloadRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTriplePayloadRow :=
  (verifierValidityRowSeeds W input).map fun seed =>
    { seed := validityRowUnifiedAffineSeed
        seed.height seed.start seed.rowBase
      payload := encodeAffineExactlyOneCompactFamily
        (validityRowSeedOneHotFrames W.machine.tm seed) }

private theorem inputCompiler_encodeUnaryFrame_no_frameEnd
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

private theorem inputCompiler_compactFamily_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneCompactFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction frames with
  | nil => simp [encodeAffineExactlyOneCompactFamily] at hsymbol
  | cons frame rest ih =>
      simp only [encodeAffineExactlyOneCompactFamily,
        List.mem_append] at hsymbol
      rcases hsymbol with hframe | hrest
      · exact inputCompiler_encodeUnaryFrame_no_frameEnd _ symbol hframe
      · exact ih hrest

/-- Typed well-formed domain for the single-source affine compiler. -/
noncomputable def verifierValidityRowUnifiedPayloadFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTriplePayloadFamily :=
  { rows := verifierValidityRowUnifiedPayloadRows W input
    payload_frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [verifierValidityRowUnifiedPayloadRows, List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact inputCompiler_compactFamily_no_frameEnd _ symbol hsymbol }

/-- The typed affine-family input is byte-for-byte the existing concrete
seed-preserving compact one-hot stream. -/
theorem verifierValidityRowUnifiedPayloadFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowUnifiedPayloadFamily W input) =
      verifierValidityRowSeedMarkedOneHotFrames W input := by
  rw [verifierValidityRowSeedMarkedOneHotFrames_eq_rows]
  unfold encodeAffineUnaryTriplePayloadFamily
  change encodeAffineUnaryTriplePayloadRowFamily
      (verifierValidityRowUnifiedPayloadRows W input) = _
  unfold verifierValidityRowUnifiedPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineUnaryTriplePayloadRowFamily,
        encodeAffineUnaryTriplePayloadRow,
        encodeAffineUnaryTripleSeed,
        encodeAffineExactlyOneStructuredRowSeed,
        validityRowUnifiedAffineSeed, List.append_assoc]
      simpa [encodeAffineUnaryTriplePayloadRowFamily,
        encodeAffineUnaryTriplePayloadRow,
        encodeAffineUnaryTripleSeed,
        encodeAffineExactlyOneStructuredRowSeed,
        validityRowUnifiedAffineSeed] using ih

/-- Concrete output of the single-source affine stage.  Every row contains
all fixed halted/tail values, an internal marker, the untouched compact
one-hot payload, and its outer row marker. -/
noncomputable def verifierValidityRowUnifiedOperandPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTriplePayloadRowOutputFamily
    (arithmeticValidityRowFixedOperandForms W.machine.tm)
    (verifierValidityRowUnifiedPayloadRows W input)

/-- Exact semantic row layout of the unified source. -/
theorem verifierValidityRowUnifiedOperandPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowUnifiedOperandPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
          ([ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
             seed.rowBase,
             arithmeticNoneLabelWire W.machine.tm seed.rowBase,
             0 ] ++
            arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase) ++
        [.frameEnd] ++
        encodeAffineExactlyOneCompactFamily
          (validityRowSeedOneHotFrames W.machine.tm seed) ++
        [.frameEnd] := by
  unfold verifierValidityRowUnifiedOperandPayloadFrames
    verifierValidityRowUnifiedPayloadRows
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, List.flatMap_cons,
        affineUnaryTriplePayloadRowOutputFamily,
        affineUnaryTriplePayloadRowOutput]
      rw [arithmeticValidityRowFixedOperandForms_eq, ih]

/-- The unified row packets are compiled from the original verifier word by
one honest source pipeline; no fan-out or oracle-side zip is used. -/
noncomputable def
    verifierValidityRowUnifiedOperandPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowUnifiedOperandPayloadFrames W) := by
  let seedSource :=
    verifierValidityRowSeedMarkedOneHotStructuredSeeds_computableInPolyTime W
  let typedSeedSource :
      _root_.Turing.TM2ComputableInPolyTime id
        encodeAffineUnaryTriplePayloadFamily
        (verifierValidityRowUnifiedPayloadFamily W) :=
    { tm := seedSource.tm
      inputAlphabet := seedSource.inputAlphabet
      outputAlphabet := seedSource.outputAlphabet
      time := seedSource.time
      outputsFun := fun input => by
        rw [verifierValidityRowUnifiedPayloadFamily_encoding_eq]
        simpa only [id_eq,
          verifierValidityRowSeedMarkedOneHotFrames] using
            seedSource.outputsFun input }
  let affineSource := affineUnaryTriplePayloadFamily_computableInPolyTime
    (arithmeticValidityRowFixedOperandForms W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedSeedSource affineSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      affineUnaryTriplePayloadRowOutputFamily
        (arithmeticValidityRowFixedOperandForms W.machine.tm)
        (verifierValidityRowUnifiedPayloadRows W input))
  simpa [Function.comp_def, verifierValidityRowUnifiedPayloadFamily] using
    Classical.choice composed

/-! ## Materialized halted and tail-prefix delimiters -/

/-- Semantic fixed values of one unified row.  The inserted zero is a real
unary field whose delimiter becomes the post-halted `frameEnd`. -/
noncomputable def arithmeticValidityRowFixedOperandValues
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) : List Nat :=
  [ arithmeticHaltedMatchStart tm height start,
    rowBase,
    arithmeticNoneLabelWire tm rowBase,
    0 ] ++
    arithmeticValidityTailFixedOperandValues tm height start rowBase

theorem arithmeticValidityRowFixedOperandForms_eq_values
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    affineUnaryTripleMap (arithmeticValidityRowFixedOperandForms tm)
        (validityRowUnifiedAffineSeed height start rowBase) =
      arithmeticValidityRowFixedOperandValues
        tm height start rowBase := by
  exact arithmeticValidityRowFixedOperandForms_eq
    tm height start rowBase

/-- Fixed delimiter table: three ordinary halted operands, their explicit
boundary field, then the established complete tail-prefix table. -/
def arithmeticValidityRowFixedOperandDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  [.separator, .separator, .separator, .frameEnd] ++
    arithmeticValidityTailFixedOperandDelimiters tm

@[simp] theorem arithmeticValidityRowFixedOperandDelimiters_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (arithmeticValidityRowFixedOperandDelimiters tm).length := by
  simp [arithmeticValidityRowFixedOperandDelimiters]

/-- Every unified affine form has one verifier-fixed output delimiter. -/
theorem arithmeticValidityRowFixedOperandDelimiters_length
    (tm : _root_.Turing.FinTM2) :
    (arithmeticValidityRowFixedOperandDelimiters tm).length =
      (arithmeticValidityRowFixedOperandForms tm).length := by
  simp [arithmeticValidityRowFixedOperandDelimiters,
    arithmeticValidityRowFixedOperandForms,
    arithmeticValidityTailFixedOperandDelimiters_length]

private theorem inputCompiler_encodeFixedDelimiters_append
    (left right : List Nat) (leftDelimiters rightDelimiters :
      List UnaryFrameSym)
    (hlength : left.length = leftDelimiters.length) :
    encodeUnaryFrameWithFixedDelimiters (left ++ right)
        (leftDelimiters ++ rightDelimiters) =
      encodeUnaryFrameWithFixedDelimiters left leftDelimiters ++
        encodeUnaryFrameWithFixedDelimiters right rightDelimiters := by
  induction left generalizing leftDelimiters with
  | nil =>
      cases leftDelimiters with
      | nil => rfl
      | cons delimiter delimiters => simp at hlength
  | cons value values ih =>
      cases leftDelimiters with
      | nil => simp at hlength
      | cons delimiter delimiters =>
          simp only [List.length_cons] at hlength
          have hlength' : values.length = delimiters.length :=
            Nat.add_right_cancel hlength
          simp [encodeUnaryFrameWithFixedDelimiters,
            ih delimiters hlength', List.append_assoc]

/-- Materializing the unified table preserves all three ordinary halted
separators, inserts their extra boundary, and then uses the established tail
delimiter table unchanged. -/
theorem arithmeticValidityRowFixedEncoding_eq
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    encodeUnaryFrameWithFixedDelimiters
        (arithmeticValidityRowFixedOperandValues
          tm height start rowBase)
        (arithmeticValidityRowFixedOperandDelimiters tm) =
      encodeUnaryFrame
          [ arithmeticHaltedMatchStart tm height start,
            rowBase,
            arithmeticNoneLabelWire tm rowBase ] ++
        [.frameEnd] ++
        encodeUnaryFrameWithFixedDelimiters
          (arithmeticValidityTailFixedOperandValues
            tm height start rowBase)
          (arithmeticValidityTailFixedOperandDelimiters tm) := by
  unfold arithmeticValidityRowFixedOperandValues
    arithmeticValidityRowFixedOperandDelimiters
  rw [inputCompiler_encodeFixedDelimiters_append]
  · simp [encodeUnaryFrameWithFixedDelimiters, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.append_assoc]
  · rfl

private theorem arithmeticValidityRowFixedOperandValues_length
    (tm : _root_.Turing.FinTM2) (height start rowBase : Nat) :
    (arithmeticValidityRowFixedOperandValues
        tm height start rowBase).length =
      (arithmeticValidityRowFixedOperandDelimiters tm).length := by
  have h := congrArg List.length
    (arithmeticValidityRowFixedOperandForms_eq_values
      tm height start rowBase)
  simpa [affineUnaryTripleMap,
    arithmeticValidityRowFixedOperandDelimiters_length] using h.symm

/-- The unified affine output is precisely a fixed-prefix splice input. -/
theorem verifierValidityRowUnifiedOperandPayloadFrames_eq_spliceInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowUnifiedOperandPayloadFrames W input =
      encodeUnaryFrameFixedPrefixSpliceInputFamily
        (fun seed : ValidityRowSeed =>
          arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed))
        (verifierValidityRowSeeds W input) := by
  rw [verifierValidityRowUnifiedOperandPayloadFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.flatMap_cons,
        encodeUnaryFrameFixedPrefixSpliceInputFamily]
      rw [show
        [ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
          seed.rowBase,
          arithmeticNoneLabelWire W.machine.tm seed.rowBase,
          0 ] ++
            arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase =
          arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase by rfl]
      rw [ih]

/-- Delimiter-materialized unified row packets.  The compact one-hot payload
is still retained verbatim for the final row-local expansion/projection stage. -/
noncomputable def verifierValidityRowSplicedOperandPayloadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixSplice
    (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
    (verifierValidityRowUnifiedOperandPayloadFrames W input)

/-- Exact row-major semantics after materializing every fixed delimiter. -/
theorem verifierValidityRowSplicedOperandPayloadFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowSplicedOperandPayloadFrames W input =
      encodeUnaryFrameFixedPrefixSpliceOutputFamily
        (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
        (fun seed : ValidityRowSeed =>
          arithmeticValidityRowFixedOperandValues W.machine.tm
            seed.height seed.start seed.rowBase)
        (fun seed : ValidityRowSeed =>
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed))
        (verifierValidityRowSeeds W input) := by
  unfold verifierValidityRowSplicedOperandPayloadFrames
  rw [verifierValidityRowUnifiedOperandPayloadFrames_eq_spliceInput]
  apply rewriteUnaryFrameFixedPrefixSplice_family
  · intro seed
    exact arithmeticValidityRowFixedOperandValues_length W.machine.tm
      seed.height seed.start seed.rowBase
  · intro seed symbol hsymbol
    exact inputCompiler_compactFamily_no_frameEnd _ symbol hsymbol

/-- Expanded row view of the spliced stream, exposing the exact halted
boundary and the unchanged compact one-hot payload. -/
theorem verifierValidityRowSplicedOperandPayloadFrames_eq_explicit
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowSplicedOperandPayloadFrames W input =
      (verifierValidityRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            [ arithmeticHaltedMatchStart W.machine.tm seed.height seed.start,
              seed.rowBase,
              arithmeticNoneLabelWire W.machine.tm seed.rowBase ] ++
          [.frameEnd] ++
          encodeUnaryFrameWithFixedDelimiters
            (arithmeticValidityTailFixedOperandValues W.machine.tm
              seed.height seed.start seed.rowBase)
            (arithmeticValidityTailFixedOperandDelimiters W.machine.tm) ++
          encodeAffineExactlyOneCompactFamily
            (validityRowSeedOneHotFrames W.machine.tm seed) ++
          [.frameEnd] := by
  rw [verifierValidityRowSplicedOperandPayloadFrames_eq_rows]
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [encodeUnaryFrameFixedPrefixSpliceOutputFamily,
        List.flatMap_cons]
      rw [arithmeticValidityRowFixedEncoding_eq, ih]

/-- One fixed polynomial-time pipeline computes the delimiter-materialized
unified packets directly from the original verifier word. -/
noncomputable def
    verifierValidityRowSplicedOperandPayloadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowSplicedOperandPayloadFrames W) := by
  let unifiedSource :=
    verifierValidityRowUnifiedOperandPayloadFrames_computableInPolyTime W
  let spliceSource := unaryFrameFixedPrefixSplice_computableInPolyTime
    (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unifiedSource spliceSource
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFrameFixedPrefixSplice
        (arithmeticValidityRowFixedOperandDelimiters W.machine.tm)
        (verifierValidityRowUnifiedOperandPayloadFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
