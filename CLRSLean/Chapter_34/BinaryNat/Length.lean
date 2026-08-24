import CLRSLean.Chapter_34.BinaryNat.RoundTrip

/-!
# Physical-size bounds for compact natural-number fields
-/

namespace CLRS.Chapter34

theorem encodeBinaryNat_length (n : Nat) :
    (encodeBinaryNat n).length = if n = 0 then 1 else n.size := by
  by_cases hn : n = 0
  · simp [encodeBinaryNat, hn]
  · simp [encodeBinaryNat, hn, Nat.size_eq_bits_len]

/-- A canonical field occupies at most one more cell than `Nat.size`.
For positive values the extra cell is not used; it accounts only for the
distinguished one-bit encoding of zero. -/
theorem encodeBinaryNat_length_le (n : Nat) :
    (encodeBinaryNat n).length ≤ n.size + 1 := by
  rw [encodeBinaryNat_length]
  split
  · simp_all
  · omega

theorem encodeBinaryNat_length_pos (n : Nat) :
    0 < (encodeBinaryNat n).length := by
  rw [encodeBinaryNat_length]
  split
  · simp
  · exact Nat.size_pos.mpr (Nat.pos_of_ne_zero (by assumption))

end CLRS.Chapter34
