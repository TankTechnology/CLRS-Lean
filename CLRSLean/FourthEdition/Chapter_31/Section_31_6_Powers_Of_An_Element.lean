import Mathlib
import CLRSLean.FourthEdition.Chapter_31.Section_31_3_Modular_Arithmetic

/-!
# 31.6 Powers of an Element

CLRS §31.6: modular exponentiation and the two theorems that make powers
modulo a number tractable — **Fermat's little theorem** (prime modulus) and
**Euler's theorem** (general modulus, via the totient function).

Main results:

- {lit}`modularExponentiation` + {lit}`modularExponentiation_spec`:
  computing `a^b mod n` by repeated squaring returns a number congruent to
  `a^b` modulo `n`.
- Theorem {lit}`fermat_little_theorem` (CLRS Theorem 31.30): for prime `p`,
  `a^p ≡ a (mod p)`.
- Theorem {lit}`euler_theorem` (CLRS Euler's theorem): for `gcd(a, n) = 1`,
  `a^φ(n) ≡ 1 (mod n)`.

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.totient n` : Euler's totient `φ(n)`.

Deferred: the full repeated-squaring recursion with an explicit operation
count, and the use of Euler's theorem in RSA (§31.7).
-/

namespace CLRS

namespace Chapter31

/-- **MODULAR-EXPONENTIATION (CLRS §31.6).**  Compute `a^b mod n`.  The
value is the remainder of `a^b` upon division by `n`; the repeated-squaring
algorithm computes it in `O(log b)` multiplications. -/
def modularExponentiation (a b n : ℕ) : ℕ :=
  a ^ b % n

/-- **MODULAR-EXPONENTIATION is correct**: `modularExponentiation a b n`
is congruent to `a^b` modulo `n`. -/
theorem modularExponentiation_spec (a b n : ℕ) :
    modularExponentiation a b n ≡ a ^ b [MOD n] := by
  rw [Nat.ModEq]
  unfold modularExponentiation
  rw [Nat.mod_mod]

/--
**Fermat's little theorem (CLRS Theorem 31.30).**  For a prime `p` and any
`a`, `a^p ≡ a (mod p)`.
-/
theorem fermat_little_theorem {p a : ℕ} (hp : Nat.Prime p) : a ^ p ≡ a [MOD p] := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := ZMod.pow_card (p := p) (x := (a : ZMod p))
  exact (ZMod.natCast_eq_natCast_iff (a ^ p) a p).mp (by
    simpa [Nat.cast_pow] using h)

/--
**Euler's theorem (CLRS §31.6).**  If `gcd(a, n) = 1` and `1 < n`, then
`a^φ(n) ≡ 1 (mod n)`.
-/
theorem euler_theorem {a n : ℕ} (hn : 1 < n) (hcop : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  rw [Nat.ModEq]
  rw [Nat.pow_totient_mod_eq_one hn hcop]
  rw [Nat.mod_eq_of_lt hn]

end Chapter31

end CLRS
