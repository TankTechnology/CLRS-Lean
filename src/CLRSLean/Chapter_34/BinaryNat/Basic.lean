import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Size

/-!
# Canonical compact natural-number fields

The payload is big-endian.  Zero has the unique one-bit representation
`[false]`; a positive number is represented by the reverse of its nonempty
`Nat.bits` list, and therefore starts with one.  Delimiters belong to the
enclosing instance grammar rather than this payload codec.
-/

namespace CLRS.Chapter34

/-- Canonical compact binary representation of a natural number. -/
def encodeBinaryNat (n : Nat) : List Bool :=
  if n = 0 then [false] else n.bits.reverse

/-- Numeric interpretation of a big-endian binary payload. -/
def binaryNatValue (bits : List Bool) : Nat :=
  Nat.ofDigits 2 (bits.reverse.map Bool.toNat)

/-- Decidable syntactic test for the canonical representation.

The empty payload is invalid.  A zero bit is canonical only when it is the
entire payload; every payload beginning in one is the unique big-endian
representation of its value.
-/
def isCanonicalBinaryNat : List Bool → Bool
  | [] => false
  | [false] => true
  | false :: _ :: _ => false
  | true :: _ => true

end CLRS.Chapter34
