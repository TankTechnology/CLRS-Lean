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
- **Miller-Rabin**: {lit}`strongTestParams` writes `n−1 = 2^s·d` with `d` odd;
  {lit}`strongPseudoprime` (STRONG-PSEUDOPRIME) is the strong probable-prime
  condition; {lit}`Witness` is a base that refutes it; and
  {lit}`millerRabin` is the executable single-base test.  (Evaluating
  `millerRabin 561 2` returns `false`: although 561 is a Carmichael number,
  base 2 witnesses that it is composite.)
- **Miller-Rabin correctness**: {lit}`strongPseudoprime_of_prime` shows a
  prime is a strong probable prime to every coprime base — the repeated
  squaring in STRONG-PSEUDOPRIME can only reach `1` through `−1` modulo a
  prime (via {lit}`modeq_neg_one_of_sq_eq_one`, the roots-of-unity fact).
  Consequently {lit}`not_witness_of_prime` (a prime has no witness) and
  {lit}`witness_not_prime` (a witness certifies compositeness) hold.
- **Error-bound foundation**: {lit}`strongPseudoprime_pow` — every strong
  probable prime satisfies `a^(n−1) ≡ 1 (mod n)`, so every strong liar lies
  in the kernel of `a ↦ a^(n−1)` (the first step toward showing the liars
  form a subgroup of the units); {lit}`modeq_pow_two_sub_one` is the
  `(n−1)² ≡ 1 (mod n)` fact used there.
- **Error-bound infrastructure (Rabin–Monier)**: {lit}`nu` is the minimum
  over prime factors `p | n` of `v₂(p−1)`; {lit}`goodUnits` (`S(n)`) is the
  subgroup of units `x` with `x^(2^(ν(n)−1)·t) ∈ {±1}` (preimage of `{1, −1}`
  under the power map); and {lit}`liar_mem_goodSet` shows **every strong liar
  lies in `S(n)`** via the order-of-element parity lemma
  {lit}`two_pow_succ_dvd_orderOf` applied modulo each prime divisor.

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.totient n` : Euler's totient.

Deferred: the Miller-Rabin error bound itself — counting `|S(n)|` and proving
`|S(n)| ≤ (n−1)/4` (the three-case Rabin–Monier bound) — and the
random-witness analysis (§31.8); the executable pseudoprime loop with an
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

/--
**STRONG-PSEUDOPRIME parameters (CLRS §31.8).**  Write `n−1 = 2^s · d` with
`d` odd: `s` is the exponent of 2 in the prime factorization of `n−1`, and
`d` is the odd part.
-/
def strongTestParams (n : ℕ) : ℕ × ℕ :=
  (Nat.factorization (n - 1) 2, (n - 1) / 2 ^ Nat.factorization (n - 1) 2)

/--
**STRONG-PSEUDOPRIME (CLRS §31.8).**  `n` is a strong probable prime to base
`a` if, writing `n−1 = 2^s·d` with `d` odd, either `a^d ≡ 1 (mod n)` or
`a^(2^i·d) ≡ −1 (mod n)` for some `i < s`.
-/
def strongPseudoprime (n a : ℕ) : Prop :=
  let s := (strongTestParams n).1
  let d := (strongTestParams n).2
  a ^ d ≡ 1 [MOD n] ∨ ∃ i : Fin s, a ^ (2 ^ (i : ℕ) * d) ≡ n - 1 [MOD n]

/--
**WITNESS (CLRS §31.8).**  A base `a` witnesses that `n` is composite when
`n` fails the strong-pseudoprime test to base `a`.  A witness certifies
`¬ Nat.Prime n`.
-/
def Witness (n a : ℕ) : Prop :=
  ¬ strongPseudoprime n a

instance instDecidableStrongPseudoprime (n a : ℕ) : Decidable (strongPseudoprime n a) := by
  unfold strongPseudoprime
  infer_instance

/--
**MILLER-RABIN (single base, CLRS §31.8).**  The executable decision procedure
returning whether `n` is a strong probable prime to base `a`.
-/
def millerRabin (n a : ℕ) : Bool :=
  decide (strongPseudoprime n a)

/--
**STRONG-PSEUDOPRIME decomposition (CLRS §31.8).**  For `n ≠ 0`,
`n = 2^s · (n / 2^s)` where `s` is the exponent of 2 in `n` — i.e. the odd part
of `n` times `2^s` recovers `n`.
-/
theorem strongTestParams_spec (n : ℕ) (hn : n ≠ 0) :
    n = 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) := by
  have hdvd : 2 ^ (n.factorization 2) ∣ n := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hn).2 le_rfl
  exact (Nat.mul_div_cancel' hdvd).symm

/--
**Roots of unity modulo a prime.**  If `b^2 ≡ 1 (mod p)` for a prime `p` and
`b ≢ 1 (mod p)`, then `b ≡ −1 (mod p)`.  This is the only fact about prime
moduli needed by the Miller-Rabin correctness proof: repeatedly squaring a
root of unity can only reach `1` through `−1`.
-/
theorem modeq_neg_one_of_sq_eq_one {p b : ℕ} (hp : Nat.Prime p) (hb : 1 ≤ b)
    (hb2 : b ^ 2 ≡ 1 [MOD p]) (hbne : ¬ b ≡ 1 [MOD p]) :
    b ≡ p - 1 [MOD p] := by
  have hb2' : 1 ≡ b ^ 2 [MOD p] := hb2.symm
  have hb2_dvd : p ∣ b ^ 2 - 1 := by
    exact (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ b ^ 2)).mp hb2'
  have hsq : b ^ 2 - 1 = (b - 1) * (b + 1) := by
    have hsub := Nat.sq_sub_sq b 1
    simpa [mul_comm] using hsub
  rw [hsq] at hb2_dvd
  have hdvd_or := (hp.dvd_mul).1 hb2_dvd
  rcases hdvd_or with hd1 | hd2
  · exfalso
    exact hbne ((Nat.modEq_iff_dvd' hb).mpr hd1).symm
  · have h0 : b + 1 ≡ 0 [MOD p] := hd2.modEq_zero_nat
    have h1 : (p - 1) + 1 ≡ 0 [MOD p] := by
      rw [Nat.sub_add_cancel (Nat.one_le_of_lt hp.pos)]
      exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)
    have h : b + 1 ≡ (p - 1) + 1 [MOD p] := h0.trans h1.symm
    exact Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) h

/--
**Miller-Rabin correctness, prime direction.**  If `n` is prime and `a` is
coprime to `n`, then `n` is a strong probable prime to base `a` — i.e. a prime
has no witness.  Writing `n−1 = 2^s·d`, the sequence `a^d, a^{2d}, …, a^{2^s·d}`
ends at `1` (Fermat); at the first index where it reaches `1`, the previous
value is a square root of `1` that is not `1`, hence `−1` (mod a prime).
-/
theorem strongPseudoprime_of_prime {n a : ℕ} (hn : Nat.Prime n) (hcop : Nat.Coprime a n) :
    strongPseudoprime n a := by
  have hn2 : 2 ≤ n := hn.two_le
  have hnm1 : n - 1 ≠ 0 := by omega
  have hdecomp : n - 1 = 2 ^ (strongTestParams n).1 * (strongTestParams n).2 := by
    have h := strongTestParams_spec (n - 1) hnm1
    simpa [strongTestParams] using h
  have hfermat : a ^ (n - 1) ≡ 1 [MOD n] := fermat_test hn hcop
  let s := (strongTestParams n).1
  let d := (strongTestParams n).2
  have h1 : a ^ (2 ^ s * d) ≡ 1 [MOD n] := by
    rw [← hdecomp]
    exact hfermat
  let P : ℕ → Prop := fun i => a ^ (2 ^ i * d) ≡ 1 [MOD n]
  have hP_s : P s := by
    simpa [P, hdecomp] using hfermat
  let i0 := Nat.find ⟨s, hP_s⟩
  have hP0 : P i0 := by
    exact Nat.find_spec ⟨s, hP_s⟩
  have hmin : ∀ m, m < i0 → ¬ P m := by
    intro m hm
    exact Nat.find_min ⟨s, hP_s⟩ (by simpa [i0] using hm)
  have hile : i0 ≤ s := by simpa [i0] using (Nat.find_le (h := ⟨s, hP_s⟩) hP_s)
  by_cases hi00 : i0 = 0
  · left
    have : P 0 := by simpa [hi00] using hP0
    simpa [P] using this
  · right
    let j := i0 - 1
    have hj : j < s := by omega
    have hjlt_i0 : j < i0 := by omega
    have hj1 : j + 1 = i0 := by omega
    have hb : a ^ (2 ^ j * d) ≡ n - 1 [MOD n] := by
      have hb2 : (a ^ (2 ^ j * d)) ^ 2 ≡ 1 [MOD n] := by
        have hsq : (a ^ (2 ^ j * d)) ^ 2 = a ^ (2 ^ i0 * d) := by
          rw [← pow_mul]
          congr 1
          rw [mul_assoc, mul_comm d 2, ← mul_assoc, ← pow_succ, hj1]
        rw [hsq]
        simpa [P] using hP0
      have hbne : ¬ a ^ (2 ^ j * d) ≡ 1 [MOD n] := by
        exact hmin j hjlt_i0
      have ha1 : 1 ≤ a := by
        have ha_ne : a ≠ 0 := by
          intro ha
          have hg : Nat.gcd a n = 1 := hcop
          have hn1 : n = 1 := by
            rw [ha, Nat.gcd_zero_left] at hg
            exact hg
          omega
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha_ne)
      have hb1 : 1 ≤ a ^ (2 ^ j * d) := by
        exact one_le_pow₀ ha1
      exact modeq_neg_one_of_sq_eq_one hn hb1 hb2 hbne
    exact ⟨⟨j, hj⟩, hb⟩

/-- **A prime has no witness**: for `n` prime and `a` coprime to `n`, `a` does
not witness compositeness of `n`. -/
theorem not_witness_of_prime {n a : ℕ} (hn : Nat.Prime n) (hcop : Nat.Coprime a n) :
    ¬ Witness n a := by
  intro hw
  exact hw (strongPseudoprime_of_prime hn hcop)

/-- **A witness certifies compositeness**: for `n` and a coprime base `a`, if
`a` is a witness then `n` is not prime. -/
theorem witness_not_prime {n a : ℕ} (hcop : Nat.Coprime a n) (hw : Witness n a) :
    ¬ Nat.Prime n := by
  intro hn
  exact (not_witness_of_prime hn hcop) hw

/-- `(n−1)² ≡ 1 (mod n)` for `n ≠ 0`: `n` divides `(n−1)² − 1 = n·(n−2)`. -/
theorem modeq_pow_two_sub_one (hn : n ≠ 0) : (n - 1) ^ 2 ≡ 1 [MOD n] := by
  rw [Nat.ModEq]
  by_cases h2 : 2 ≤ n
  · have hsq2 := Nat.sq_sub_sq (n - 1) 1
    have hsq2' : (n - 1) ^ 2 - 1 = (n - 1 + 1) * (n - 1 - 1) := by simpa using hsq2
    have hform : (n - 1) ^ 2 - 1 = n * (n - 2) := by
      rw [hsq2']
      have h1 : (n - 1) + 1 = n := by omega
      have h2' : (n - 1) - 1 = n - 2 := by omega
      rw [h1, h2', mul_comm]
    have hdvd : n ∣ (n - 1) ^ 2 - 1 := by
      rw [hform]
      exact dvd_mul_right n (n - 2)
    rcases hdvd with ⟨k, hk⟩
    have hle : 1 ≤ (n - 1) ^ 2 := by
      have ht : 1 ≤ n - 1 := by omega
      nlinarith
    have hk' : (n - 1) ^ 2 = n * k + 1 := by
      rw [← hk]
      omega
    rw [hk']
    simp
  · have hn1 : n = 1 := by omega
    simp [hn1]

/--
**A strong probable prime satisfies Fermat's congruence.**  If `n` is a strong
pseudoprime to base `a`, then `a^(n−1) ≡ 1 (mod n)`.  Indeed `n−1 = 2^s·d`, and
either `a^d ≡ 1` or `a^(2^i·d) ≡ −1` for some `i < s`; in the second case
`a^(n−1) = (a^(2^i·d))^(2^(s−i)) ≡ (−1)^even = 1`.  This is the first step of
the Miller-Rabin error-bound proof: every strong liar lies in the kernel of
`a ↦ a^(n−1)`.
-/
theorem strongPseudoprime_pow {n a : ℕ} (h : strongPseudoprime n a) :
    a ^ (n - 1) ≡ 1 [MOD n] := by
  by_cases hn0 : n - 1 = 0
  · simpa [hn0] using (Nat.ModEq.refl 1)
  · have hdecomp : n - 1 = 2 ^ (strongTestParams n).1 * (strongTestParams n).2 := by
      have hd := strongTestParams_spec (n - 1) hn0
      simpa [strongTestParams] using hd
    unfold strongPseudoprime at h
    rw [hdecomp]
    rcases h with hd1 | ⟨i, hi⟩
    · have hpow := hd1.pow (2 ^ (strongTestParams n).1)
      simpa [← pow_mul, mul_comm] using hpow
    · have hpow := hi.pow (2 ^ ((strongTestParams n).1 - (i : ℕ)))
      have hsum : (i : ℕ) + ((strongTestParams n).1 - (i : ℕ)) = (strongTestParams n).1 := by
        exact Nat.add_sub_of_le (Nat.le_of_lt i.isLt)
      have hpowsum : 2 ^ (i : ℕ) * 2 ^ ((strongTestParams n).1 - (i : ℕ)) = 2 ^ (strongTestParams n).1 := by
        rw [← pow_add, hsum]
      have hexp : (2 ^ (i : ℕ) * (strongTestParams n).2) * 2 ^ ((strongTestParams n).1 - (i : ℕ)) =
          2 ^ (strongTestParams n).1 * (strongTestParams n).2 := by
        rw [mul_assoc]
        rw [mul_comm (strongTestParams n).2 (2 ^ ((strongTestParams n).1 - (i : ℕ)))]
        rw [← mul_assoc, hpowsum]
      have h1 : a ^ (2 ^ (strongTestParams n).1 * (strongTestParams n).2) =
          (a ^ (2 ^ (i : ℕ) * (strongTestParams n).2)) ^ (2 ^ ((strongTestParams n).1 - (i : ℕ))) := by
        rw [← pow_mul]
        congr 1
        exact hexp.symm
      rw [h1]
      have h2 : (n - 1) ^ (2 ^ ((strongTestParams n).1 - (i : ℕ))) ≡ 1 [MOD n] := by
        have hsmi_pos : 0 < (strongTestParams n).1 - (i : ℕ) := by
          exact Nat.sub_pos_of_lt i.isLt
        have heven : 2 ^ ((strongTestParams n).1 - (i : ℕ)) =
            2 * 2 ^ (((strongTestParams n).1 - (i : ℕ)) - 1) := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hsmi_pos]
        rw [heven]
        rw [pow_mul]
        have hsq := modeq_pow_two_sub_one (n := n) (by omega : n ≠ 0)
        simpa using (hsq.pow (2 ^ (((strongTestParams n).1 - (i : ℕ)) - 1)))
      exact hpow.trans h2

/-! ## Error bound: the good subgroup `S(n)` (Rabin–Monier)

The Miller-Rabin error bound (Theorem 31.38; sharpened by Rabin and Monier)
states that for odd composite `n`, at most `(n−1)/4` of the bases are strong
liars.  The proof embeds the liars into a subgroup `S(n)` of the units modulo
`n` and bounds `|S(n)|`.  This section develops the infrastructure: the units
of `ZMod n`, the cyclicity of prime-power unit groups (from Mathlib), the
2-adic valuation `ν(n)`, and the good subgroup `S(n)`. -/

/-- The reduction `(ZMod n)ˣ → (ZMod p)ˣ` of units when `p ∣ n`. -/
def zmodUnitReduction {n p : ℕ} (hp : p ∣ n) : (ZMod n)ˣ →* (ZMod p)ˣ :=
  Units.map (ZMod.castHom hp (ZMod p)).toMonoidHom

/-- The unit group of `ZMod n` has `φ(n)` elements. -/
theorem units_card_eq_totient {n : ℕ} [NeZero n] : Nat.card (ZMod n)ˣ = Nat.totient n := by
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card_units_eq_totient n

/-- For a prime `p`, the unit group of `ZMod p` has `p − 1` elements. -/
theorem units_card_prime {p : ℕ} (hp : Nat.Prime p) : Nat.card (ZMod p)ˣ = p - 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient p, Nat.totient_prime hp]

/-- The subgroup `{1, −1}` of the units modulo `n`. -/
def negOneTwoSubgroup {n : ℕ} [NeZero n] : Subgroup (ZMod n)ˣ where
  carrier := {x : (ZMod n)ˣ | x = 1 ∨ x = -1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha1 | ham
    · rcases hb with hb1 | hbm
      · simp [ha1, hb1]
      · simp [ha1, hbm]
    · rcases hb with hb1 | hbm
      · simp [ham, hb1]
      · simp [ham, hbm]
  inv_mem' := by
    intro a ha
    rcases ha with ha1 | ham
    · simp [ha1]
    · simp [ham]

/-- The power homomorphism `x ↦ x^m` on the units modulo `n`. -/
def unitPowHom {n : ℕ} [NeZero n] (m : ℕ) : (ZMod n)ˣ →* (ZMod n)ˣ where
  toFun x := x ^ m
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [mul_pow]

/--
The **good set** `S_m = {x ∈ (ZMod n)ˣ : x^m ∈ {1, −1}}`, a subgroup of the
units (the preimage of `{1, −1}` under the power map `x ↦ x^m`).
-/
def goodSet {n : ℕ} [NeZero n] (m : ℕ) : Subgroup (ZMod n)ˣ :=
  negOneTwoSubgroup.comap (unitPowHom (n := n) m)

/-- Membership in `goodSet` as a power-of-a-unit condition. -/
theorem mem_goodSet_iff {n : ℕ} [NeZero n] (m : ℕ) (x : (ZMod n)ˣ) :
    x ∈ goodSet (n := n) m ↔ x ^ m = 1 ∨ x ^ m = -1 := by
  rfl

/-- Membership in `goodSet` as a power condition in `ZMod n`. -/
theorem mem_goodSet_zmod {n : ℕ} [NeZero n] (m : ℕ) (x : (ZMod n)ˣ) :
    x ∈ goodSet (n := n) m ↔ (x : ZMod n) ^ m = 1 ∨ (x : ZMod n) ^ m = -1 := by
  rw [mem_goodSet_iff]
  constructor
  · rintro (h | h)
    · left
      exact congrArg (fun u : (ZMod n)ˣ => (u : ZMod n)) h
    · right
      exact congrArg (fun u : (ZMod n)ˣ => (u : ZMod n)) h
  · rintro (h | h)
    · left
      exact Units.ext h
    · right
      exact Units.ext h

/--
`ν(n)`: the minimum over prime factors `p` of `n` of `v₂(p − 1)`, the
2-adic valuation of `p − 1`.  This is the index bound used to define the
good subgroup for the Miller-Rabin error bound.
-/
noncomputable def nu (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then
    (n.primeFactors.image (fun p => (p - 1).factorization 2)).min'
      (h.image (fun p => (p - 1).factorization 2))
  else 0

/-- For every prime factor `p | n`, `ν(n) ≤ v₂(p − 1)`. -/
theorem nu_le_v2 (hn : n.primeFactors.Nonempty) {p : ℕ} (hp : p ∈ n.primeFactors) :
    nu n ≤ (p - 1).factorization 2 := by
  unfold nu
  rw [dif_pos hn]
  have hmem : (p - 1).factorization 2 ∈
      (n.primeFactors.image (fun p => (p - 1).factorization 2)) := by
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  exact (Finset.isLeast_min' _ _).2 (by simpa using hmem)

/-- `2^ν(n)` divides `p − 1` for every prime factor `p | n`. -/
theorem two_pow_nu_dvd_prime_sub_one (hn : n.primeFactors.Nonempty) {p : ℕ}
    (hp : p ∈ n.primeFactors) : 2 ^ nu n ∣ p - 1 := by
  have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hppos : p - 1 ≠ 0 := by
    have := hp'.two_le
    omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := nu n) (n := p - 1)
    (by decide : Nat.Prime 2) hppos).2 (nu_le_v2 hn hp)

/-- `ν(n) ≥ 1` for odd `n > 1`: every prime factor is odd, so `p − 1` is even. -/
theorem nu_pos {n : ℕ} (hn_odd : Odd n) (hn1 : 1 < n) : 1 ≤ nu n := by
  have hnne : n.primeFactors.Nonempty := (Nat.nonempty_primeFactors).2 hn1
  unfold nu
  rw [dif_pos hnne]
  apply Finset.le_min'
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
  have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hpodd : Odd p := by
    have hne_even_n : ¬ Even n := (Nat.not_even_iff_odd.mpr hn_odd)
    have hne_even_p : ¬ Even p := by
      intro hep
      rcases hep with ⟨k, hk⟩
      rcases hpdvd with ⟨m, hm⟩
      refine hne_even_n ⟨k * m, ?_⟩
      rw [hm, hk]
      ring
    exact (Nat.not_even_iff_odd.mp hne_even_p)
  have h2dvd : 2 ∣ p - 1 := by
    rcases (odd_iff_exists_bit1.mp hpodd) with ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  have hppos : p - 1 ≠ 0 := by
    have := hp'.two_le
    omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := 1) (n := p - 1)
    (by decide : Nat.Prime 2) hppos).1 h2dvd

/-- The odd part `a / 2^(v₂(a))` of a nonzero `a` is odd. -/
lemma oddPart_odd (a : ℕ) (ha : a ≠ 0) : Odd (a / 2 ^ a.factorization 2) := by
  have hdvd : 2 ^ a.factorization 2 ∣ a := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) ha).2 le_rfl
  have hfac : (a / 2 ^ a.factorization 2).factorization 2 = 0 := by
    rw [Nat.factorization_div hdvd]
    simp [Nat.factorization_pow_self (by decide : Nat.Prime 2),
      Nat.Prime.factorization_self (by decide : Nat.Prime 2)]
  have htpos : 0 < a / 2 ^ a.factorization 2 := by
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hdvd) (pow_pos (by norm_num) _)
  have h2not : ¬ 2 ∣ a / 2 ^ a.factorization 2 := by
    intro h2
    have hle1 : 1 ≤ (a / 2 ^ a.factorization 2).factorization 2 := by
      exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) htpos.ne').1 h2
    omega
  exact (Nat.not_even_iff_odd.mp (even_iff_two_dvd.not.mpr h2not))

/-- The odd part `t = (n−1)/2^(v₂(n−1))` of `n−1` is odd. -/
theorem strongTestParams_odd {n : ℕ} (hn1 : 1 < n) : Odd (strongTestParams n).2 := by
  unfold strongTestParams
  exact oddPart_odd (n - 1) (by omega)

/--
The **good subgroup** `S(n)` (Rabin–Monier).  Writing `n−1 = 2^s·t` with `t`
odd and `ν = ν(n)`, `S(n) = {x ∈ (ZMod n)ˣ : x^(2^(ν−1)·t) ∈ {1, −1}}`.
Every strong liar lies in `S(n)`, and `|S(n)| ≤ (n−1)/4`.
-/
noncomputable def goodUnits {n : ℕ} [NeZero n] : Subgroup (ZMod n)ˣ :=
  goodSet (2 ^ (nu n - 1) * (strongTestParams n).2)

/--
**Parity lemma.**  If `a^(2^i·d)` has order 2 in a finite group and `d` is
odd, then `2^(i+1)` divides the order of `a`.  Indeed `orderOf a =
2·gcd(orderOf a, 2^i·d)`, whose 2-adic valuation forces
`v₂(orderOf a) = i+1`.
-/
theorem two_pow_succ_dvd_orderOf {G : Type*} [Group G] [Finite G] {a : G} {i d : ℕ}
    (hd : Odd d) (hord : orderOf (a ^ (2 ^ i * d)) = 2) :
    2 ^ (i + 1) ∣ orderOf a := by
  let e := orderOf a
  let g := e.gcd (2 ^ i * d)
  have hpow := orderOf_pow (x := a) (n := 2 ^ i * d)
  have hdiv : e / g = 2 := by
    dsimp [e, g]
    rw [← hpow]
    exact hord
  have he : e = 2 * g := by
    have hg : g ∣ e := by
      dsimp [g]
      exact Nat.gcd_dvd_left _ _
    have h := Nat.mul_div_cancel' hg
    rw [hdiv] at h
    rw [mul_comm] at h
    exact h.symm
  have epos : e ≠ 0 := by
    dsimp [e]
    exact (orderOf_pos a).ne'
  have dpos : d ≠ 0 := by
    intro hz
    rw [hz] at hd
    norm_num at hd
  have h2dpos : 2 ^ i * d ≠ 0 := mul_ne_zero (pow_ne_zero i (by norm_num)) dpos
  have hgpos : g ≠ 0 := by
    intro hg0
    have hg_dvd : g ∣ e := by
      dsimp [g]
      exact Nat.gcd_dvd_left _ _
    rw [hg0] at hg_dvd
    exact epos (zero_dvd_iff.mp hg_dvd)
  have h2notd : ¬ 2 ∣ d := (even_iff_two_dvd.not.mp (Nat.not_even_iff_odd.mpr hd))
  have hpowfac : (2 ^ i * d).factorization 2 = i := by
    rw [Nat.factorization_mul (pow_ne_zero i (by norm_num)) dpos]
    simp [Nat.Prime.factorization_self (by decide : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd h2notd]
  have hgfac : g.factorization 2 = min (e.factorization 2) i := by
    dsimp [g]
    rw [Nat.factorization_gcd epos h2dpos]
    simp [hpowfac]
  have hfac : e.factorization 2 = 1 + min (e.factorization 2) i := by
    calc
      e.factorization 2 = (2 * g).factorization 2 := by rw [he]
      _ = (2 : ℕ).factorization 2 + g.factorization 2 := by
        rw [Nat.factorization_mul (by norm_num) hgpos]
        simp
      _ = 1 + g.factorization 2 := by
        rw [Nat.Prime.factorization_self (by decide : Nat.Prime 2)]
      _ = 1 + min (e.factorization 2) i := by rw [hgfac]
  have hi_lt : i < e.factorization 2 := by
    by_contra hnot
    have hle : e.factorization 2 ≤ i := Nat.not_lt.mp hnot
    have hz : min (e.factorization 2) i = e.factorization 2 := min_eq_left hle
    have hcontra : e.factorization 2 = 1 + e.factorization 2 := by
      calc
        e.factorization 2 = 1 + min (e.factorization 2) i := hfac
        _ = 1 + e.factorization 2 := by rw [hz]
    omega
  change 2 ^ (i + 1) ∣ e
  exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) epos).2
    (Nat.succ_le_of_lt hi_lt)

/-- In `(ZMod p)ˣ` for an odd prime `p`, the element `−1` has order 2. -/
theorem orderOf_neg_one {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    orderOf (-1 : (ZMod p)ˣ) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (by simp) (by
    intro h
    have hz : (-1 : ZMod p) = 1 := by
      simpa using congrArg Units.val h
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
    exact ZMod.neg_one_ne_one hz)

/--
For an odd prime `p`, if `x^(2^i·d) = −1` with `d` odd, then `2^(i+1)`
divides `p − 1`: `x^(2^i·d)` has order 2, so by the parity lemma
`2^(i+1) | orderOf x`, and `orderOf x | p−1` by Lagrange.
-/
theorem two_pow_succ_dvd_prime_sub_one {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    {x : (ZMod p)ˣ} {i d : ℕ} (hd : Odd d) (hx : (x : ZMod p) ^ (2 ^ i * d) = -1) :
    2 ^ (i + 1) ∣ p - 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hord : orderOf (x ^ (2 ^ i * d)) = 2 := by
    have hx' : x ^ (2 ^ i * d) = -1 := by
      apply Units.ext
      simp [hx]
    rw [hx']
    exact orderOf_neg_one hp hp2
  have hdvd_ord : 2 ^ (i + 1) ∣ orderOf x := two_pow_succ_dvd_orderOf hd hord
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := units_card_prime hp
  have hord_dvd : orderOf x ∣ p - 1 := (orderOf_dvd_natCard x).trans (by rw [hcard])
  exact hdvd_ord.trans hord_dvd

/--
The **strong-liar** predicate on units modulo `n`: `n` is a strong probable
prime to base `a` (equivalently `strongPseudoprime n (a : ZMod n).val`).
-/
def isStrongLiar {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) : Prop :=
  (a : ZMod n) ^ (strongTestParams n).2 = 1 ∨
    ∃ i : Fin (strongTestParams n).1,
      (a : ZMod n) ^ (2 ^ (i : ℕ) * (strongTestParams n).2) = -1

/--
**Every strong liar lies in the good subgroup.**  For odd `n > 1`, if `a` is a
strong liar modulo `n`, then `a^(2^(ν(n)−1)·t) ∈ {±1}`, i.e. `a ∈ S(n)`.
The index bound `i < ν(n)` is obtained by reducing modulo each prime divisor
`p` of `n` and applying the parity lemma, which forces `2^(i+1) | p−1`.
-/
theorem liar_mem_goodSet {n : ℕ} [NeZero n] (hn_odd : Odd n) (hn1 : 1 < n)
    {a : (ZMod n)ˣ} (hliar : isStrongLiar a) : a ∈ goodUnits := by
  rw [goodUnits, mem_goodSet_zmod]
  rcases hliar with hd1 | ⟨i, hi⟩
  · left
    have h : (a : ZMod n) ^ (2 ^ (nu n - 1) * (strongTestParams n).2) = 1 := by
      rw [mul_comm]
      rw [pow_mul]
      rw [hd1]
      simp
    exact h
  · have hv2 : ∀ p, p ∈ n.primeFactors → 2 ^ ((i : ℕ) + 1) ∣ p - 1 := by
      intro p hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hpne2 : p ≠ 2 := by
        intro hp2
        have hne : ¬ Even n := (Nat.not_even_iff_odd.mpr hn_odd)
        exact hne (even_iff_two_dvd.mpr (by rw [← hp2]; exact hp_dvd))
      let φ := zmodUnitReduction (n := n) (p := p) hp_dvd
      have hφ : ((φ a : (ZMod p)ˣ) : ZMod p) ^ (2 ^ (i : ℕ) * (strongTestParams n).2) = -1 := by
        have hc := congrArg (ZMod.castHom hp_dvd (ZMod p)) hi
        have hc' : (ZMod.castHom hp_dvd (ZMod p) (a : ZMod n)) ^ (2 ^ (i : ℕ) * (strongTestParams n).2) = -1 := by
          simpa [map_pow, map_neg, map_one] using hc
        have hval : (φ a : ZMod p) = ZMod.castHom hp_dvd (ZMod p) (a : ZMod n) := by
          simp [φ, zmodUnitReduction]
        rwa [hval]
      exact two_pow_succ_dvd_prime_sub_one hpp hpne2 (strongTestParams_odd (n := n) hn1) hφ
    have hle : (i : ℕ) + 1 ≤ nu n := by
      have hnne : n.primeFactors.Nonempty := (Nat.nonempty_primeFactors).2 hn1
      have hfac : ∀ p, p ∈ n.primeFactors → (i : ℕ) + 1 ≤ (p - 1).factorization 2 := by
        intro p hp
        have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        exact (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (k := (i : ℕ) + 1) (n := p - 1)
          (by decide : Nat.Prime 2) (by have := hpp.two_le; omega)).1 (hv2 p hp)
      unfold nu
      rw [dif_pos hnne]
      apply Finset.le_min'
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
      exact hfac p hp
    have hi_lt : (i : ℕ) < nu n := by omega
    have hsum : (i : ℕ) + (nu n - 1 - (i : ℕ)) = nu n - 1 := by omega
    have hexp : (a : ZMod n) ^ (2 ^ (nu n - 1) * (strongTestParams n).2) =
        ((a : ZMod n) ^ (2 ^ (i : ℕ) * (strongTestParams n).2)) ^ (2 ^ (nu n - 1 - (i : ℕ))) := by
      have hexp_eq : 2 ^ (nu n - 1) * (strongTestParams n).2 =
          (2 ^ (i : ℕ) * (strongTestParams n).2) * 2 ^ (nu n - 1 - (i : ℕ)) := by
        rw [mul_assoc, mul_comm (strongTestParams n).2 (2 ^ (nu n - 1 - (i : ℕ))), ← mul_assoc,
          ← pow_add, hsum]
      rw [hexp_eq, pow_mul]
    rw [hexp, hi]
    by_cases h0 : nu n - 1 - (i : ℕ) = 0
    · right
      rw [h0]
      simp
    · left
      have hpos : 0 < nu n - 1 - (i : ℕ) := Nat.pos_of_ne_zero h0
      have hk : 2 ^ (nu n - 1 - (i : ℕ)) = 2 * 2 ^ ((nu n - 1 - (i : ℕ)) - 1) := by
        rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hpos]
      rw [hk, pow_mul]
      simp

end Chapter31

end CLRS
