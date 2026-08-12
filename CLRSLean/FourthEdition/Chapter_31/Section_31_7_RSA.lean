import Mathlib
import CLRSLean.FourthEdition.Chapter_31.Section_31_6_Powers_Of_An_Element
import CLRSLean.FourthEdition.Chapter_31.Section_31_5_Chinese_Remainder_Theorem

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
- Theorem {lit}`rsa_correct_general` (CLRS Theorem 31.36, general message):
  for distinct primes `p q` and `e·d ≡ 1 (mod (p−1)(q−1))`, `m^(e·d) ≡ m
  (mod p·q)` for every `m` — via Fermat modulo each prime and the Chinese
  remainder theorem.

Notation:

- {lit}`Nat.totient n` : Euler's totient `φ(n)`.
- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.

Deferred: the running-time / key-generation analysis and the RSA
security (one-way function) claims.
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

/-- For prime `p` and `e·d ≡ 1 (mod p−1)`, `m^(e·d) ≡ m (mod p)`: the RSA
exponentiation recovers `m` modulo each prime factor of the modulus (the
`p`-side of the general RSA correctness). -/
lemma rsa_pow_cong {p m e d : ℕ} (hp : Nat.Prime p) (hle : 1 ≤ e * d)
    (hmed : e * d ≡ 1 [MOD p - 1]) : m ^ (e * d) ≡ m [MOD p] := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨Nat.Prime.ne_zero hp⟩
  rcases (Nat.modEq_iff_exists_eq_add hle).mp hmed.symm with ⟨k, hk⟩
  have hz0 : (m : ZMod p) ^ (e * d) = (m : ZMod p) := by
    rw [hk, pow_add, pow_one, pow_mul]
    by_cases hm0 : (m : ZMod p) = 0
    · rw [hm0]
      simp
    · have hp1 : (m : ZMod p) ^ (p - 1) = 1 := by
        simpa [hm0] using (ZMod.pow_card_sub_one (p := p) (a := (m : ZMod p)))
      rw [hp1]
      simp
  rw [Nat.ModEq]
  calc
    (m ^ (e * d)) % p = (↑(m ^ (e * d)) : ZMod p).val := (ZMod.val_natCast p (m ^ (e * d))).symm
    _ = ((m : ZMod p) ^ (e * d)).val := by rw [Nat.cast_pow]
    _ = (m : ZMod p).val := by rw [hz0]
    _ = m % p := ZMod.val_natCast p m

/-- Distinct primes are coprime. -/
lemma prime_coprime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Nat.Coprime p q := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hpq_dvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq p hpq_dvd) with h1 | heq
  · exfalso
    have hp2 : 2 ≤ p := Nat.Prime.two_le hp
    omega
  · exact hpq heq

/--
**RSA is correct for every message (CLRS Theorem 31.36).**  For distinct
primes `p q`, `n = p·q`, and exponents with `e·d ≡ 1 (mod (p−1)(q−1))`,
`m^(e·d) ≡ m (mod p·q)` for **every** `m` — including messages sharing a
factor with `n`.  The proof shows the congruence modulo each prime factor
({lit}`rsa_pow_cong`, which covers both `p | m` and `p ∤ m` via Fermat) and
combines them with the Chinese remainder theorem.
-/
theorem rsa_correct_general {p q m e d : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hle : 1 ≤ e * d) (hmed : e * d ≡ 1 [MOD (p - 1) * (q - 1)]) :
    m ^ (e * d) ≡ m [MOD p * q] := by
  have hp_cong : m ^ (e * d) ≡ m [MOD p] := by
    apply rsa_pow_cong hp hle
    rw [Nat.ModEq] at hmed ⊢
    have hd : p - 1 ∣ (p - 1) * (q - 1) := by simpa [Nat.mul_comm] using (dvd_mul_left (p - 1) (q - 1))
    rw [← Nat.mod_mod_of_dvd (e * d) hd]
    rw [hmed]
    rw [Nat.mod_mod_of_dvd 1 hd]
  have hq_cong : m ^ (e * d) ≡ m [MOD q] := by
    apply rsa_pow_cong hq hle
    rw [Nat.ModEq] at hmed ⊢
    have hd : q - 1 ∣ (p - 1) * (q - 1) := by simpa [Nat.mul_comm] using (dvd_mul_right (q - 1) (p - 1))
    rw [← Nat.mod_mod_of_dvd (e * d) hd]
    rw [hmed]
    rw [Nat.mod_mod_of_dvd 1 hd]
  exact chinese_remainder_unique (prime_coprime hp hq hpq) ⟨hp_cong, hq_cong⟩ ⟨Nat.ModEq.refl m, Nat.ModEq.refl m⟩

end Chapter31

end CLRS
