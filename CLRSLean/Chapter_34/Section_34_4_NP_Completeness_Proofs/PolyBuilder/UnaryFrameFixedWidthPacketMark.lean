import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import Mathlib.Tactic

/-!
# Marking fixed-width unary packets

Affine sources emit one uninterrupted ordinary unary frame.  Later streaming
controllers need a real tape boundary between consecutive fixed-width runtime
packets.  This module supplies a finite-state TM2 which preserves every tick,
keeps ordinary separators inside a packet, and replaces the final separator
of every packet by `frameEnd`.

The width is part of finite control.  No packet is split or reconstructed by a
meta-level list operation in the polynomial-time result.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Advance inside a positive fixed-width packet, resetting after its final
field. -/
def unaryFrameFixedWidthPacketNext (width : Nat) (hpositive : 0 < width)
    (position : Fin width) : Fin width :=
  if hnext : position.val + 1 < width then
    ⟨position.val + 1, hnext⟩
  else
    ⟨0, hpositive⟩

/-- Replace precisely the separator ending each fixed-width packet. -/
def unaryFrameFixedWidthPacketAction (width : Nat) (hpositive : 0 < width)
    (position : Fin width) (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × Fin width :=
  match symbol with
  | .tick => (some .tick, position)
  | .frameEnd => (some .frameEnd, position)
  | .separator =>
      if hnext : position.val + 1 < width then
        (some .separator, ⟨position.val + 1, hnext⟩)
      else
        (some .frameEnd, ⟨0, hpositive⟩)

/-- Finite-state specification of the packet marker. -/
def unaryFrameFixedWidthPacketSpec (width : Nat) (hpositive : 0 < width) :
    UnaryFrameStatefulMapSpec (Fin width) :=
  { initial := ⟨0, hpositive⟩
    action := unaryFrameFixedWidthPacketAction width hpositive }

/-- Pure forward action of the fixed-width packet marker. -/
def rewriteUnaryFrameFixedWidthPackets (width : Nat)
    (hpositive : 0 < width) (input : List UnaryFrameSym) :
    List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFrameFixedWidthPacketSpec width hpositive) input

/-- Unary encoding of one packet: ordinary separators occur after every field
except the last, whose delimiter is `frameEnd`. -/
def encodeUnaryFrameFixedWidthPacket : List Nat → List UnaryFrameSym
  | [] => []
  | [value] => List.replicate value .tick ++ [.frameEnd]
  | value :: next :: rest =>
      List.replicate value .tick ++ .separator ::
        encodeUnaryFrameFixedWidthPacket (next :: rest)

/-- Payload of one nonempty packet, excluding its final physical marker. -/
def encodeUnaryFrameFixedWidthPacketBody : List Nat → List UnaryFrameSym
  | [] => []
  | [value] => List.replicate value .tick
  | value :: next :: rest =>
      List.replicate value .tick ++ .separator ::
        encodeUnaryFrameFixedWidthPacketBody (next :: rest)

/-- A nonempty marked packet is exactly its marker-free body followed by one
outer row boundary. -/
theorem encodeUnaryFrameFixedWidthPacket_eq_body
    (value : Nat) (values : List Nat) :
    encodeUnaryFrameFixedWidthPacket (value :: values) =
      encodeUnaryFrameFixedWidthPacketBody (value :: values) ++
        [.frameEnd] := by
  induction values generalizing value with
  | nil => simp [encodeUnaryFrameFixedWidthPacket,
      encodeUnaryFrameFixedWidthPacketBody]
  | cons next rest ih =>
      simp [encodeUnaryFrameFixedWidthPacket,
        encodeUnaryFrameFixedWidthPacketBody, ih, List.append_assoc]

/-- Packet bodies use only ticks and ordinary separators. -/
theorem encodeUnaryFrameFixedWidthPacketBody_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrameFixedWidthPacketBody values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction values with
  | nil => simp [encodeUnaryFrameFixedWidthPacketBody] at hsymbol
  | cons value values ih =>
      cases values with
      | nil =>
          simp [encodeUnaryFrameFixedWidthPacketBody] at hsymbol
          rcases hsymbol with ⟨_, rfl⟩
          simp
      | cons next rest =>
          simp only [encodeUnaryFrameFixedWidthPacketBody,
            List.mem_append, List.mem_replicate, List.mem_cons] at hsymbol
          rcases hsymbol with ⟨_, rfl⟩ | rfl | hrest
          · simp
          · simp
          · exact ih hrest

private theorem fixedWidthPacket_ticks (width : Nat)
    (hpositive : 0 < width) (position : Fin width) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedWidthPacketSpec width hpositive) position
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedWidthPacketSpec width hpositive) position tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      change .tick ::
          rewriteUnaryFrameStatefulFrom
            (unaryFrameFixedWidthPacketSpec width hpositive) position
            (List.replicate count .tick ++ tail) = _
      rw [ih]
      simp [List.cons_append]

private theorem fixedWidthPacket_encode_from (width : Nat)
    (hpositive : 0 < width) (values : List Nat) (position : Nat)
    (hposition : position < width)
    (hfit : position + values.length = width)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedWidthPacketSpec width hpositive)
        ⟨position, hposition⟩ (encodeUnaryFrame values ++ tail) =
      encodeUnaryFrameFixedWidthPacket values ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedWidthPacketSpec width hpositive)
          ⟨0, hpositive⟩ tail := by
  induction values generalizing position with
  | nil =>
      simp only [List.length_nil, Nat.add_zero] at hfit
      omega
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            .separator :: (encodeUnaryFrame values ++ tail) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [fixedWidthPacket_ticks]
      cases values with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hfit
          have hlast : ¬position + 1 < width := by omega
          simp only [rewriteUnaryFrameStatefulFrom,
            unaryFrameFixedWidthPacketSpec,
            unaryFrameFixedWidthPacketAction]
          rw [dif_neg hlast]
          simp [encodeUnaryFrame, encodeUnaryFrameFixedWidthPacket]
      | cons next rest =>
          simp only [List.length_cons] at hfit
          have hnext : position + 1 < width := by
            omega
          have hrestFit : position + 1 + (next :: rest).length = width := by
            simp only [List.length_cons]
            omega
          simp only [rewriteUnaryFrameStatefulFrom,
            unaryFrameFixedWidthPacketSpec,
            unaryFrameFixedWidthPacketAction]
          rw [dif_pos hnext]
          change List.replicate value .tick ++
              .separator ::
                rewriteUnaryFrameStatefulFrom
                  (unaryFrameFixedWidthPacketSpec width hpositive)
                  ⟨position + 1, hnext⟩
                  (encodeUnaryFrame (next :: rest) ++ tail) = _
          rw [ih (position + 1) hnext hrestFit]
          simp [encodeUnaryFrameFixedWidthPacket, List.append_assoc,
            unaryFrameFixedWidthPacketSpec]

/-- Exact packet-boundary semantics on any family of rows having the declared
positive width. -/
theorem rewriteUnaryFrameFixedWidthPackets_encode (width : Nat)
    (hpositive : 0 < width) (packets : List (List Nat))
    (hwidth : ∀ packet ∈ packets, packet.length = width) :
    rewriteUnaryFrameFixedWidthPackets width hpositive
        (packets.flatMap encodeUnaryFrame) =
      packets.flatMap encodeUnaryFrameFixedWidthPacket := by
  unfold rewriteUnaryFrameFixedWidthPackets rewriteUnaryFrameStateful
  induction packets with
  | nil => rfl
  | cons packet packets ih =>
      have hpacket : packet.length = width := hwidth packet (by simp)
      have hpackets : ∀ row ∈ packets, row.length = width := by
        intro row hrow
        exact hwidth row (by simp [hrow])
      simp only [List.flatMap_cons]
      change rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedWidthPacketSpec width hpositive)
          ⟨0, hpositive⟩
          (encodeUnaryFrame packet ++ packets.flatMap encodeUnaryFrame) = _
      rw [fixedWidthPacket_encode_from width hpositive packet 0 hpositive
        (by simpa using hpacket)
        (packets.flatMap encodeUnaryFrame)]
      have ih' := ih hpackets
      change rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedWidthPacketSpec width hpositive)
          ⟨0, hpositive⟩ (packets.flatMap encodeUnaryFrame) = _ at ih'
      rw [ih']

/-- The fixed-width marker is implemented by one concrete linear-time TM2. -/
noncomputable def unaryFrameFixedWidthPacketMark_computableInPolyTime
    (width : Nat) (hpositive : 0 < width) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameFixedWidthPackets width hpositive) := by
  exact unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameFixedWidthPacketSpec width hpositive)

end CLRS.Chapter34.Turing.PolyBuilder
