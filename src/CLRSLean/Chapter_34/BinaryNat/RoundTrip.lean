import CLRSLean.Chapter_34.BinaryNat.Parser

/-!
# Exact laws for canonical compact naturals
-/

namespace CLRS.Chapter34

private theorem bits_reverse_starts_true (n : Nat) (hn : n ≠ 0) :
    ∃ rest, n.bits.reverse = true :: rest := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have hleading : n.div2 = 0 → n.bodd = true := by
        intro hdiv
        cases hbit : n.bodd with
        | false =>
            apply False.elim
            apply hn
            rw [← Nat.bit_bodd_div2 n, hbit, hdiv]
            rfl
        | true => rfl
      have hbits : n.bits = n.bodd :: n.div2.bits := by
        calc
          n.bits = (Nat.bit n.bodd n.div2).bits :=
            congrArg Nat.bits (Nat.bit_bodd_div2 n).symm
          _ = n.bodd :: n.div2.bits :=
            Nat.bits_append_bit n.div2 n.bodd hleading
      by_cases hdiv : n.div2 = 0
      · have hbit := hleading hdiv
        rw [hbits, hdiv, Nat.zero_bits, hbit]
        exact ⟨[], rfl⟩
      · have hlt : n.div2 < n := Nat.binaryRec_decreasing hn
        rcases ih n.div2 hlt hdiv with ⟨rest, hrest⟩
        rw [hbits, List.reverse_cons, hrest]
        exact ⟨rest ++ [n.bodd], rfl⟩

@[simp] theorem isCanonicalBinaryNat_encode (n : Nat) :
    isCanonicalBinaryNat (encodeBinaryNat n) = true := by
  by_cases hn : n = 0
  · subst n
    rfl
  · rw [encodeBinaryNat, if_neg hn]
    rcases bits_reverse_starts_true n hn with ⟨rest, hrest⟩
    rw [hrest]
    rfl

theorem binaryNatValue_encode (n : Nat) :
    binaryNatValue (encodeBinaryNat n) = n := by
  by_cases hn : n = 0
  · subst n
    simp [binaryNatValue, encodeBinaryNat]
  · rw [encodeBinaryNat, if_neg hn]
    rw [binaryNatValue]
    rw [List.reverse_reverse]
    change Nat.ofDigits 2
      (n.bits.map (fun b => cond b 1 0)) = n
    rw [← Nat.digits_two_eq_bits]
    exact Nat.ofDigits_digits 2 n

/-- Semantic decoding is a left inverse of canonical binary encoding. -/
@[simp] theorem decodeBinaryNat_encode (n : Nat) :
    decodeBinaryNat (encodeBinaryNat n) = some n := by
  rw [decodeBinaryNat_eq_some_iff]
  exact ⟨isCanonicalBinaryNat_encode n, binaryNatValue_encode n⟩

/-- Successful parsing returns the unique canonical encoding of its value. -/
theorem encodeBinaryNat_of_decode_eq_some {bits : List Bool} {n : Nat}
    (h : decodeBinaryNat bits = some n) :
    encodeBinaryNat n = bits := by
  rcases decodeBinaryNat_eq_some_iff.mp h with ⟨hcanonical, rfl⟩
  cases bits with
  | nil => simp [isCanonicalBinaryNat] at hcanonical
  | cons bit rest =>
      cases bit with
      | false =>
          cases rest with
          | nil => rfl
          | cons next tail => simp [isCanonicalBinaryNat] at hcanonical
      | true =>
          simp only [binaryNatValue, encodeBinaryNat]
          have hvalue : Nat.ofDigits 2 ((true :: rest).reverse.map Bool.toNat) ≠ 0 := by
            rw [List.reverse_cons, List.map_append]
            simp only [List.map_singleton, Bool.toNat_true]
            rw [Nat.ofDigits_append]
            simp
          rw [if_neg hvalue]
          have hdigitBound : ∀ d ∈ (true :: rest).reverse.map Bool.toNat, d < 2 := by
            intro d hd
            simp only [List.mem_map] at hd
            rcases hd with ⟨b, _, rfl⟩
            cases b <;> decide
          have hlast : ∀ hne : (true :: rest).reverse.map Bool.toNat ≠ [],
              ((true :: rest).reverse.map Bool.toNat).getLast hne ≠ 0 := by
            intro hne
            simp
          have hdigits := Nat.digits_ofDigits 2 (by decide)
            ((true :: rest).reverse.map Bool.toNat) hdigitBound hlast
          rw [Nat.digits_two_eq_bits] at hdigits
          have hmaps :
              ((Nat.ofDigits 2 ((true :: rest).reverse.map Bool.toNat)).bits.map
                  Bool.toNat) =
                ((true :: rest).reverse.map Bool.toNat) := by
            exact hdigits
          have hboolInjective : Function.Injective Bool.toNat := by
            intro a b hab
            cases a <;> cases b <;> simp_all
          have := (List.map_injective_iff.mpr hboolInjective) hmaps
          simpa using congrArg List.reverse this

/-- The canonical encoding is injective. -/
theorem encodeBinaryNat_injective : Function.Injective encodeBinaryNat := by
  intro m n h
  have := congrArg decodeBinaryNat h
  simpa using this

end CLRS.Chapter34
