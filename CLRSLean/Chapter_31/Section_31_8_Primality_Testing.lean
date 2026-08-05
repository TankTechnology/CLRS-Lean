import Mathlib
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

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.totient n` : Euler's totient.

Deferred: Carmichael numbers, the Miller-Rabin test and its error bound, and
the random-witness analysis (§31.8); the executable pseudoprime loop with an
operation count.
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

end Chapter31

end CLRS
