import CLRSLean.FourthEdition.Chapter_31.Section_31_7_RSA

/-!
Generated keys from supplied distinct primes and a coprime public exponent
round-trip every message modulo the generated modulus, including messages
sharing a factor with it. In-range messages are recovered exactly. This is
key assembly and algebraic correctness, not prime generation or a security claim.
-/

namespace CLRS.Chapter31

theorem rsaKeyGen_roundTrip_mod (p q e m : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcop : Nat.Coprime e ((p - 1) * (q - 1))) :
    rsaDecrypt (rsaKeyGen p q e).2.2 (rsaKeyGen p q e).1
      (rsaEncrypt (rsaKeyGen p q e).2.1 (rsaKeyGen p q e).1 m) =
      m % (rsaKeyGen p q e).1 := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hφ : 1 < (p - 1) * (q - 1) := by
    by_cases hp3 : 3 ≤ p
    · have hp' : 2 ≤ p - 1 := by omega
      have hq' : 1 ≤ q - 1 := by omega
      nlinarith
    · have hp' : p = 2 := by omega
      have hq' : 2 ≤ q - 1 := by omega
      rw [hp']; omega
  have hc := rsaPrivateExponent_spec p q e hp hq hpq hcop
  have hpos : 1 ≤ e * rsaPrivateExponent p q e := by
    by_contra hn
    have hz : e * rsaPrivateExponent p q e = 0 := by omega
    rw [Nat.ModEq, hz, Nat.zero_mod, Nat.mod_eq_of_lt hφ] at hc
    omega
  simp only [rsaKeyGen, rsaDecrypt_spec, rsaEncrypt_spec]
  rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← pow_mul]
  exact rsa_correct_general hp hq hpq hpos hc

theorem rsaKeyGen_roundTrip (p q e m : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hcop : Nat.Coprime e ((p - 1) * (q - 1))) (hm : m < p * q) :
    rsaDecrypt (rsaKeyGen p q e).2.2 (rsaKeyGen p q e).1
      (rsaEncrypt (rsaKeyGen p q e).2.1 (rsaKeyGen p q e).1 m) = m := by
  rw [rsaKeyGen_roundTrip_mod p q e m hp hq hpq hcop]
  exact Nat.mod_eq_of_lt hm

end CLRS.Chapter31
