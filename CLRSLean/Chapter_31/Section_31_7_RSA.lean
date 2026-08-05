import Mathlib
import CLRSLean.Chapter_31.Section_31_6_Powers_Of_An_Element

/-!
# 31.7 The RSA Public-Key Cryptosystem

CLRS §31.7: the RSA public-key cryptosystem.  With `n = p·q` for distinct
primes `p, q`, `φ(n) = (p−1)(q−1)`, a public exponent `e` coprime to `φ(n)`,
and the private exponent `d ≡ e⁻¹ (mod φ(n))`, encryption `c = m^e mod n`
and decryption `m = c^d mod n` are mutually inverse.

Main results:

- Theorem {lit}`totient_mul_prime`: for distinct primes `p q`,
  `φ(p·q) = (p−1)·(q−1)`.
- Theorem {lit}`rsa_correct` (CLRS Theorem 31.36): if `e·d ≡ 1 (mod φ(n))`
  and `gcd(m, n) = 1`, then `m^(e·d) ≡ m (mod n)` — decryption undoes
  encryption.

Notation:

- {lit}`Nat.totient n` : Euler's totient `φ(n)`.
- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.

Deferred: the full proof for `m` sharing a factor with `n` (the general RSA
argument), and the running-time / key-generation analysis.
-/

namespace CLRS

namespace Chapter31

/-- For distinct primes `p` and `q`, `φ(p·q) = (p−1)·(q−1)`: the totient of
the RSA modulus. -/
theorem totient_mul_prime (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    (p * q).totient = (p - 1) * (q - 1) := by
  have hcop : Nat.Coprime p q := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hpq_dvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq p hpq_dvd) with h1 | heq
    · exfalso
      have hp2 : 2 ≤ p := Nat.Prime.two_le hp
      omega
    · exact hpq heq
  rw [Nat.totient_mul hcop]
  rw [Nat.totient_prime hp, Nat.totient_prime hq]

/--
**RSA is correct (CLRS Theorem 31.36).**  If the exponents satisfy
`e·d ≡ 1 (mod φ(n))` and `m` is coprime to the modulus `n`, then
`m^(e·d) ≡ m (mod n)`: raising to the power `e·d` (encryption followed by
decryption, or vice versa) recovers `m`.
-/
theorem rsa_correct {m e d n : ℕ} (hle : 1 ≤ e * d)
    (hmed : e * d ≡ 1 [MOD Nat.totient n]) (hcop : Nat.Coprime m n) :
    m ^ (e * d) ≡ m [MOD n] := by
  rcases (Nat.modEq_iff_exists_eq_add hle).mp hmed.symm with ⟨k, hk⟩
  have hE : m ^ Nat.totient n ≡ 1 [MOD n] := Nat.ModEq.pow_totient hcop
  have h1 : m ^ (e * d) ≡ m ^ (1 + Nat.totient n * k) [MOD n] := by
    rw [hk]
  have h2 : m ^ (1 + Nat.totient n * k) = m * (m ^ Nat.totient n) ^ k := by
    rw [pow_add, pow_mul, pow_one]
  have h3 : m * (m ^ Nat.totient n) ^ k ≡ m * 1 ^ k [MOD n] := by
    exact Nat.ModEq.mul (Nat.ModEq.refl m) (Nat.ModEq.pow k hE)
  have hmid : m ^ (1 + Nat.totient n * k) ≡ m * 1 ^ k [MOD n] := by
    rw [h2]
    exact h3
  exact (by simpa using (h1.trans hmid))

end Chapter31

end CLRS
