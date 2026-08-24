import CLRSLean.Chapter_34.BinaryNat.Basic

/-!
# Parser for canonical compact naturals

Parsing first checks the canonical leading-bit grammar and then computes the
numeric value.  This rejects the empty word, leading zeroes, and every
noncanonical representation of zero.
-/

namespace CLRS.Chapter34

/-- Parse one complete canonical binary-natural payload. -/
def decodeBinaryNat (bits : List Bool) : Option Nat :=
  if isCanonicalBinaryNat bits then some (binaryNatValue bits) else none

theorem decodeBinaryNat_eq_some_iff {bits : List Bool} {n : Nat} :
    decodeBinaryNat bits = some n ↔
      isCanonicalBinaryNat bits = true ∧ binaryNatValue bits = n := by
  simp [decodeBinaryNat]

theorem decodeBinaryNat_eq_none_iff {bits : List Bool} :
    decodeBinaryNat bits = none ↔
      isCanonicalBinaryNat bits = false := by
  simp [decodeBinaryNat]

end CLRS.Chapter34
