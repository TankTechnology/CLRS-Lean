import Mathlib
import CLRSLean.Chapter_31.Section_31_3_Modular_Arithmetic

/-!
# 31.5 The Chinese Remainder Theorem

CLRS §31.5: the **Chinese remainder theorem** (Theorem 31.27) — if the moduli
`n₁, …, nₖ` are pairwise relatively prime, then the system of congruences
`x ≡ aᵢ (mod nᵢ)` has a unique solution modulo `n₁·…·nₖ`.

This section formalizes the two-modulus form (the building block of the full
theorem): for coprime `n` and `m`, the system `x ≡ a (mod n)`, `x ≡ b (mod m)`
has a solution, and any two solutions agree modulo `n·m`.  Mathlib's
`Nat.chineseRemainder` supplies existence; uniqueness uses
`Nat.modEq_and_modEq_iff_modEq_mul`.

Main results:

- Theorem {lit}`chinese_remainder_two`: for coprime `n m`, the system
  `x ≡ a (mod n)`, `x ≡ b (mod m)` has a solution.
- Theorem {lit}`chinese_remainder_unique`: any two solutions agree modulo
  `n·m`.

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.Coprime n m` : `gcd n m = 1`.

Deferred: the general `k`-modulus form via `Nat.chineseRemainderOfList` /
`ZMod.chineseRemainder`, and the CRT-based RSA proofs (§31.7).
-/

namespace CLRS

namespace Chapter31

/--
**Chinese remainder theorem (CLRS Theorem 31.27, two moduli).**  If `n` and
`m` are coprime, the system of congruences `x ≡ a (mod n)` and
`x ≡ b (mod m)` has a solution.
-/
theorem chinese_remainder_two {n m a b : ℕ} (hcop : Nat.Coprime n m) :
    ∃ x : ℕ, x ≡ a [MOD n] ∧ x ≡ b [MOD m] := by
  exact ⟨(Nat.chineseRemainder hcop a b).1, (Nat.chineseRemainder hcop a b).2⟩

/--
**Chinese remainder theorem, uniqueness.**  For coprime `n` and `m`, any two
solutions of the same system `x ≡ a (mod n)`, `x ≡ b (mod m)` agree modulo
`n·m`.
-/
theorem chinese_remainder_unique {n m a b x y : ℕ} (hcop : Nat.Coprime n m)
    (hx : x ≡ a [MOD n] ∧ x ≡ b [MOD m]) (hy : y ≡ a [MOD n] ∧ y ≡ b [MOD m]) :
    x ≡ y [MOD n * m] := by
  have hxcr := Nat.chineseRemainder_modEq_unique hcop hx.1 hx.2
  have hycr := Nat.chineseRemainder_modEq_unique hcop hy.1 hy.2
  exact hxcr.trans hycr.symm

/--
**Chinese remainder theorem (two moduli, bundled).**  For coprime `n m`, the
system has a solution, unique modulo `n·m`.
-/
theorem chinese_remainder {n m a b : ℕ} (hcop : Nat.Coprime n m) :
    ∃ x : ℕ, x ≡ a [MOD n] ∧ x ≡ b [MOD m] ∧
      ∀ y : ℕ, y ≡ a [MOD n] → y ≡ b [MOD m] → x ≡ y [MOD n * m] := by
  obtain ⟨x, hx₁, hx₂⟩ := chinese_remainder_two hcop
  refine ⟨x, hx₁, hx₂, ?_⟩
  intro y hy₁ hy₂
  exact chinese_remainder_unique hcop ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

end Chapter31

end CLRS
