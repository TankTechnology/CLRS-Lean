import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic

/-!
# Delimiter-bearing unary runtime frames

The Ch34 validity family reuses three local unary registers for every gate
serializer.  Runtime indices that must survive between primitive invocations
therefore live in a symbol-stack frame.  A separator is essential: a plain
`Unit` stack cannot distinguish adjacent unary values, including zero.
-/

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite alphabet for a sequence of delimiter-separated unary naturals. -/
inductive UnaryFrameSym
  | tick
  | separator
  | frameEnd
deriving DecidableEq, Fintype, Repr

/-- One self-delimiting unary natural. -/
def encodeUnaryFrameBlock (value : Nat) : List UnaryFrameSym :=
  List.replicate value .tick ++ [.separator]

/-- Concatenated runtime frame.  Zero is represented by a bare separator. -/
def encodeUnaryFrame (values : List Nat) : List UnaryFrameSym :=
  values.flatMap encodeUnaryFrameBlock

/-- Accumulating parser for a delimiter-bearing unary frame.  An unterminated
final block is rejected. -/
def decodeUnaryFrameAux : Nat → List UnaryFrameSym → Option (List Nat)
  | 0, [] => some []
  | _ + 1, [] => none
  | count, .tick :: rest => decodeUnaryFrameAux (count + 1) rest
  | count, .separator :: rest =>
      (count :: ·) <$> decodeUnaryFrameAux 0 rest
  | _, .frameEnd :: _ => none

/-- Decode a complete runtime frame. -/
def decodeUnaryFrame (frame : List UnaryFrameSym) : Option (List Nat) :=
  decodeUnaryFrameAux 0 frame

private theorem decodeUnaryFrameAux_ticks (count value : Nat)
    (rest : List UnaryFrameSym) :
    decodeUnaryFrameAux count
        (List.replicate value .tick ++ rest) =
      decodeUnaryFrameAux (count + value) rest := by
  induction value generalizing count with
  | zero => simp
  | succ value ih =>
      simp only [List.replicate_succ, List.cons_append,
        decodeUnaryFrameAux]
      rw [ih]
      simp only [Nat.add_assoc]
      rw [Nat.add_comm 1 value]

private theorem decodeUnaryFrameAux_block (value : Nat)
    (rest : List UnaryFrameSym) :
    decodeUnaryFrameAux 0 (encodeUnaryFrameBlock value ++ rest) =
      (value :: ·) <$> decodeUnaryFrameAux 0 rest := by
  simp only [encodeUnaryFrameBlock, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [decodeUnaryFrameAux_ticks]
  simp only [Nat.zero_add]
  cases value <;> rfl

/-- Encoding followed by decoding returns every runtime index exactly,
including empty frames and zero-valued fields. -/
@[simp] theorem decodeUnaryFrame_encode (values : List Nat) :
    decodeUnaryFrame (encodeUnaryFrame values) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change decodeUnaryFrameAux 0
        (encodeUnaryFrameBlock value ++ encodeUnaryFrame values) = _
      rw [decodeUnaryFrameAux_block]
      change (value :: ·) <$> decodeUnaryFrame
        (encodeUnaryFrame values) = some (value :: values)
      rw [ih]
      rfl

/-- Exact frame size: one tick per unary unit and one separator per field. -/
@[simp] theorem encodeUnaryFrame_length (values : List Nat) :
    (encodeUnaryFrame values).length =
      (values.map fun value => value + 1).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change (encodeUnaryFrameBlock value ++ encodeUnaryFrame values).length = _
      rw [List.length_append, ih]
      simp [encodeUnaryFrameBlock]

/-- Runtime frames are unambiguous. -/
theorem encodeUnaryFrame_injective : Function.Injective encodeUnaryFrame := by
  intro left right hframe
  have hdecode := congrArg decodeUnaryFrame hframe
  simpa using hdecode

end CLRS.Chapter34.Turing.PolyBuilder
