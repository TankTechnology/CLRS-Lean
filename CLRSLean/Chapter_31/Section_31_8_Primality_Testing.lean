import Mathlib
import CLRSLean.Chapter_31.Section_31_5_Chinese_Remainder_Theorem
import CLRSLean.Chapter_31.Section_31_6_Powers_Of_An_Element

/-!
# 31.8 Primality Testing

CLRS §31.8: probabilistic primality testing.  Fermat's little theorem gives a
candidate test — for prime `p` and `gcd(a, p) = 1`, `a^(p−1) ≡ 1 (mod p)` — so
a value `n` for which some `a` fails this congruence cannot be prime.  The
PSEUDOPRIME test checks `2^(n−1) ≡ 1 (mod n)`.

Main results:

- Theorem {lit}`fermat_test` (CLRS Theorem 31.31): for a prime `p` and `a`
  coprime to `p`, `a^(p−1) ≡ 1 (mod p)`.
- Definition {lit}`fermatPseudoprime`: a composite `n` with
  `a^(n−1) ≡ 1 (mod n)` for a given `a`.
- {lit}`pseudoprime` + {lit}`pseudoprime_correct` (CLRS PSEUDOPRIME): the
  executable test returns whether `2^(n−1) ≡ 1 (mod n)`.
- {lit}`isCarmichael` (**Carmichael numbers**): a composite `n` passing the
  Fermat test for every `a` coprime to `n`; a Carmichael number is a Fermat
  pseudoprime to every coprime base
  ({lit}`carmichael_fermatPseudoprime`).  {lit}`isCarmichael_561` shows the
  smallest Carmichael number is 561, so `PSEUDOPRIME` cannot certify
  primality.  The helper {lit}`modeq_of_coprime_mul` combines congruences
  under coprime moduli.

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.totient n` : Euler's totient.

Deferred: the Miller-Rabin test and its error bound, and the random-witness
analysis (§31.8); the executable pseudoprime loop with an operation count.
-/

namespace CLRS

namespace Chapter31

/--
**Fermat's test (CLRS Theorem 31.31).**  For a prime `p` and `a` coprime to
`p`, `a^(p−1) ≡ 1 (mod p)`.  Consequently, if some `a` coprime to `n`
satisfies `a^(n−1) ≢ 1 (mod n)`, then `n` is not prime.
-/
theorem fermat_test {p a : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime a p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  rw [← Nat.totient_prime hp]
  exact Nat.ModEq.pow_totient hcop

/-- `n` is a **Fermat pseudoprime to base `a`**: it is composite yet passes
the Fermat test `a^(n−1) ≡ 1 (mod n)`. -/
def fermatPseudoprime (n a : ℕ) : Prop :=
  ¬ Nat.Prime n ∧ a ^ (n - 1) ≡ 1 [MOD n]

/--
**PSEUDOPRIME (CLRS §31.8).**  The executable test: `n` passes when
`2^(n−1) ≡ 1 (mod n)`.
-/
def pseudoprime (n : ℕ) : Bool :=
  decide (2 ^ (n - 1) ≡ 1 [MOD n])

/-- **PSEUDOPRIME is correct on odd primes**: every prime `n ≠ 2` passes the
test.  (The base case `n = 2` is a known special case handled separately.) -/
theorem pseudoprime_correct {n : ℕ} (hn : Nat.Prime n) (hn2 : n ≠ 2) :
    pseudoprime n = true := by
  unfold pseudoprime
  rw [decide_eq_true]
  have hnot : ¬ 2 ∣ n := by
    intro h2dvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hn 2 h2dvd) with h1 | h2
    · omega
    · exact hn2 h2.symm
  have hcop : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnot
  exact fermat_test hn hcop

/--
`n` is a **Carmichael number** if it is composite and passes the Fermat test
`a^(n−1) ≡ 1 (mod n)` for every `a` coprime to `n` (CLRS §31.8).  Such numbers
fool the Fermat primality test for every base, so the test alone cannot
certify primality.
-/
def isCarmichael (n : ℕ) : Prop :=
  ¬ Nat.Prime n ∧ 1 < n ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- A Carmichael number is composite. -/
theorem carmichael_not_prime {n : ℕ} (h : isCarmichael n) : ¬ Nat.Prime n := h.1

/-- A Carmichael number is larger than one. -/
theorem carmichael_gt_one {n : ℕ} (h : isCarmichael n) : 1 < n := h.2.1

/-- A Carmichael number passes the Fermat test for every base coprime to it. -/
theorem carmichael_passes_fermat {n a : ℕ} (h : isCarmichael n) (hcop : Nat.Coprime a n) :
    a ^ (n - 1) ≡ 1 [MOD n] := h.2.2 a hcop

/-- A Carmichael number is a Fermat pseudoprime to every base coprime to it. -/
theorem carmichael_fermatPseudoprime {n a : ℕ} (h : isCarmichael n) (hcop : Nat.Coprime a n) :
    fermatPseudoprime n a :=
  ⟨carmichael_not_prime h, carmichael_passes_fermat h hcop⟩

/--
**Combining congruences under coprime moduli.**  If `a ≡ b (mod m)` and
`a ≡ b (mod n)` with `m`, `n` coprime, then `a ≡ b (mod m·n)`.  This is the
"glue" needed to lift a congruence from pairwise-coprime prime factors to
their product (used to verify that 561 is a Carmichael number).
-/
theorem modeq_of_coprime_mul {a b m n : ℕ} (hcop : Nat.Coprime m n)
    (hm : a ≡ b [MOD m]) (hn : a ≡ b [MOD n]) : a ≡ b [MOD m * n] := by
  rcases chinese_remainder (n := m) (m := n) (a := b) (b := b) hcop with
    ⟨x, hx₁, hx₂, huniq⟩
  have hxb : x ≡ b [MOD m * n] := huniq b (Nat.ModEq.refl b) (Nat.ModEq.refl b)
  have hax : x ≡ a [MOD m * n] := huniq a hm hn
  exact hax.symm.trans hxb

/--
**561 is a Carmichael number.**  The smallest Carmichael number (CLRS §31.8).
It shows the Fermat test can be fooled by a composite integer for every base
coprime to it, so `PSEUDOPRIME` cannot certify primality.
-/
theorem isCarmichael_561 : isCarmichael 561 := by
  constructor
  · intro hp
    have hdiv3 : 3 ∣ 561 := by norm_num
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdiv3) with h1 | h561
    · norm_num at h1
    · norm_num at h561
  · constructor
    · norm_num
    · intro a hcop
      have hcop3 : Nat.Coprime a 3 :=
        (Nat.Coprime.of_dvd_left (by norm_num : 3 ∣ 561) hcop.symm).symm
      have hcop11 : Nat.Coprime a 11 :=
        (Nat.Coprime.of_dvd_left (by norm_num : 11 ∣ 561) hcop.symm).symm
      have hcop17 : Nat.Coprime a 17 :=
        (Nat.Coprime.of_dvd_left (by norm_num : 17 ∣ 561) hcop.symm).symm
      have h3 : a ^ 560 ≡ 1 [MOD 3] := by
        simpa [← pow_mul] using (fermat_test (p := 3) (by norm_num : Nat.Prime 3) hcop3).pow 280
      have h11 : a ^ 560 ≡ 1 [MOD 11] := by
        simpa [← pow_mul] using (fermat_test (p := 11) (by norm_num : Nat.Prime 11) hcop11).pow 56
      have h17 : a ^ 560 ≡ 1 [MOD 17] := by
        simpa [← pow_mul] using (fermat_test (p := 17) (by norm_num : Nat.Prime 17) hcop17).pow 35
      have h33 : a ^ 560 ≡ 1 [MOD 3 * 11] := modeq_of_coprime_mul (by norm_num) h3 h11
      have hfull : a ^ 560 ≡ 1 [MOD 3 * 11 * 17] :=
        modeq_of_coprime_mul (by norm_num) h33 h17
      simpa [show 3 * 11 * 17 = 561 by norm_num] using hfull

end Chapter31

end CLRS
