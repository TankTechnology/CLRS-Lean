import Mathlib
import CLRSLean.FourthEdition.Chapter_31.Section_31_5_Chinese_Remainder_Theorem
import CLRSLean.FourthEdition.Chapter_31.Section_31_6_Powers_Of_An_Element

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
- **The Miller-Rabin error bound (Theorem 31.39, sharpened to `(n−1)/4` by
  Rabin–Monier)**: counting
  `|S(n)|` via the cyclicity of prime-power unit groups and the CRT, then
  bounding `|S(n)| ≤ (n−1)/4` by the three-case Rabin–Monier analysis.
  Theorems {lit}`goodUnits_card_le` (the subgroup bound, split into prime
  power, semiprime, and ≥3-factors cases) and {lit}`strongLiars_card_le` (at
  most `(n−1)/4` strong liars for odd composite `n`).

- **Random-witness analysis (the MILLER-RABIN error bound)**: the count of
  strong-liar bases among `1, …, n-1` is at most `(n-1)/4`
  ({lit}`strongLiars_nat_card_le`), so a uniformly random base errs with
  probability at most `1/4` and `s` independent rounds err with probability at
  most `4⁻ˢ` (CLRS Theorem 31.39).

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.totient n` : Euler's totient.

Deferred: none (the executable multi-base {lit}`millerRabinLoop` and its
operation-count bound {lit}`millerRabinLoop_count_le` are proved).
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

The Miller-Rabin error bound (Theorem 31.39; sharpened to `(n−1)/4` by Rabin
and Monier) states that for odd composite `n`, at most `(n−1)/4` of the bases
are strong
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

/-! ### Counting `|S(n)|` — cyclic torsion counts

The Rabin-Monier bound needs the cardinality of `S(n)`, which is a product of
per-prime-power counts of solutions to `x^m ≡ ±1`.  Each such count is a
`gcd` in a cyclic group; the lemmas below provide that counting primitive for
a finite cyclic group. -/

/-- The number of multiples of `d` in `[0, N)` is `N/d` when `d | N`. -/
lemma card_multiples_dvd {N d : ℕ} (hd : d ∣ N) :
    Nat.card {i : Fin N // d ∣ (i : ℕ)} = N / d := by
  by_cases hN : N = 0
  · subst hN
    simp
  · have hd0 : d ≠ 0 := by
      intro hz
      apply hN
      exact (zero_dvd_iff.mp (by simpa [hz] using hd))
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hN_eq : N = d * (N / d) := (Nat.mul_div_cancel' hd).symm
    let e : {i : Fin N // d ∣ (i : ℕ)} ≃ Fin (N / d) :=
      { toFun := fun i => ⟨i.val.val / d, by
          have hx : i.val.val < N := i.val.isLt
          have hx' : i.val.val < d * (N / d) := lt_of_lt_of_eq hx hN_eq
          exact (Nat.div_lt_iff_lt_mul (k := d) (x := i.val.val) (y := N / d) hdpos).mpr
            (by simpa [mul_comm] using hx')⟩
        invFun := fun k => ⟨⟨k.val * d, by
          have hk : k.val < N / d := k.isLt
          have hk' : k.val * d < (N / d) * d := Nat.mul_lt_mul_of_pos_right hk hdpos
          have : (N / d) * d = N := by simpa [mul_comm] using hN_eq.symm
          rw [this] at hk'
          exact hk'⟩, by
            simpa [mul_comm] using (dvd_mul_right d k.val : d ∣ d * k.val)⟩
        left_inv := by
          intro i
          apply Subtype.ext
          apply Fin.ext
          simp only [Fin.val_mk]
          exact (mul_comm (i.val.val / d) d).trans (Nat.mul_div_cancel' i.property)
        right_inv := by
          intro k
          apply Fin.ext
          simpa [mul_comm] using (Nat.mul_div_right k.val hdpos) }
    rw [Nat.card_congr e]
    simp

/-- The number of `i < N` with `N | i·n` is `gcd(N, n)`. -/
lemma card_fin_dvd_mul {N n : ℕ} (hN : N ≠ 0) :
    Nat.card {i : Fin N // N ∣ (i : ℕ) * n} = N.gcd n := by
  let g := N.gcd n
  have hgN : g ∣ N := Nat.gcd_dvd_left N n
  have hgn : g ∣ n := Nat.gcd_dvd_right N n
  have hg0 : g ≠ 0 := by
    intro hz
    apply hN
    exact (Nat.gcd_eq_zero_iff.mp hz).1
  have hgpos : 0 < g := Nat.pos_of_ne_zero hg0
  have hN_eq : N = g * (N / g) := (Nat.mul_div_cancel' hgN).symm
  have hn_eq : n = g * (n / g) := (Nat.mul_div_cancel' hgn).symm
  have hcop : Nat.Coprime (N / g) (n / g) := by
    unfold Nat.Coprime
    rw [Nat.gcd_div hgN hgn]
    dsimp [g]
    nth_rw 1 [← Nat.mul_one (N.gcd n)]
    exact Nat.mul_div_right 1 (Nat.pos_of_ne_zero hg0)
  have hiff : ∀ i : Fin N, (N ∣ (i : ℕ) * n) ↔ ((N / g) ∣ (i : ℕ)) := by
    intro i
    constructor
    · intro h
      have hN : g * (N / g) = N := Nat.mul_div_cancel' hgN
      have hn' : g * ((i : ℕ) * (n / g)) = (i : ℕ) * n := by
        calc
          g * ((i : ℕ) * (n / g)) = (i : ℕ) * (g * (n / g)) := by ring
          _ = (i : ℕ) * n := by rw [← hn_eq]
      have h1 : g * (N / g) ∣ g * ((i : ℕ) * (n / g)) := by
        rwa [hN, hn']
      have hdiv : N / g ∣ (i : ℕ) * (n / g) :=
        (Nat.mul_dvd_mul_iff_left hgpos).mp h1
      exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hdiv)
    · intro h
      rcases h with ⟨c, hc⟩
      have hNdvd : N ∣ (N / g) * n := by
        use n / g
        calc
          (N / g) * n = (N / g) * (g * (n / g)) := by rw [← hn_eq]
          _ = ((N / g) * g) * (n / g) := by rw [mul_assoc]
          _ = N * (n / g) := by
            have : (N / g) * g = N := by
              rw [mul_comm]
              exact Nat.mul_div_cancel' hgN
            rw [this]
      have hc' : (i : ℕ) * n = c * ((N / g) * n) := by
        rw [hc]
        ring
      rw [hc']
      simpa [mul_assoc, mul_comm, mul_left_comm] using (dvd_mul_of_dvd_left hNdvd c)
  have hcount : Nat.card {i : Fin N // (N / g) ∣ (i : ℕ)} = N / (N / g) :=
    card_multiples_dvd (d := N / g) (by
      use g
      rw [mul_comm]
      exact (Nat.mul_div_cancel' hgN).symm)
  have hquot : N / (N / g) = g := by
    have hNg : (N / g) * g = N := by
      rw [mul_comm]
      exact Nat.mul_div_cancel' hgN
    have hpos : 0 < N / g := by
      exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hgN) hgpos
    calc
      N / (N / g) = ((N / g) * g) / (N / g) := by
        nth_rw 1 [← hNg]
      _ = g := by exact Nat.mul_div_right g hpos
  let e : {i : Fin N // N ∣ (i : ℕ) * n} ≃ {i : Fin N // N / g ∣ (i : ℕ)} :=
    { toFun := fun i => ⟨i.1, (hiff i.1).mp i.2⟩
      invFun := fun i => ⟨i.1, (hiff i.1).mpr i.2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
  rw [Nat.card_congr e]
  rw [hcount, hquot]

/--
In a finite cyclic group of order `N`, the number of elements with `x^n = 1`
is `gcd(n, N)`.  This is the counting primitive for the Rabin-Monier bound:
the number of solutions to `x^m ≡ 1` modulo a prime power.
-/
theorem card_pow_eq_one_cyclic {α : Type*} [Group α] [Fintype α] [DecidableEq α]
    [IsCyclic α] (n : ℕ) : Nat.card {x : α // x ^ n = 1} = Nat.gcd n (Fintype.card α) := by
  let N := Nat.card α
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  have horder : orderOf g = N := by
    dsimp [N]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  let f : Fin N → α := fun i => g ^ (i : ℕ)
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hmod : (i : ℕ) ≡ (j : ℕ) [MOD orderOf g] := by
      exact (pow_eq_pow_iff_modEq).1 hij
    rw [horder] at hmod
    have hi : (i : ℕ) < N := i.isLt
    have hj : (j : ℕ) < N := j.isLt
    exact Nat.ModEq.eq_of_lt_of_lt hmod hi hj
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : x ∈ (Finset.range N).image (fun i : ℕ => g ^ i) := by
      dsimp [N]
      rw [IsCyclic.image_range_card hg]
      exact Finset.mem_univ x
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact ⟨⟨k, (Finset.mem_range.mp hk)⟩, rfl⟩
  let ef := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hN : N ≠ 0 := by
    dsimp [N]
    exact Nat.card_pos.ne'
  have h1 : Nat.card {i : Fin N // (f i) ^ n = 1} = Nat.card {x : α // x ^ n = 1} := by
    exact Nat.card_congr (Equiv.subtypeEquiv ef (by intro i; rfl))
  have h2 : Nat.card {i : Fin N // (f i) ^ n = 1} = Nat.card {i : Fin N // N ∣ (i : ℕ) * n} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquiv (Equiv.refl (Fin N))
    intro i
    have hpow : (f i) ^ n = g ^ ((i : ℕ) * n) := by
      simp [f, ← pow_mul, mul_comm, mul_left_comm]
    constructor
    · intro h
      rw [hpow] at h
      have hdvd : orderOf g ∣ (i : ℕ) * n := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [horder] at hdvd
      exact hdvd
    · intro h
      rw [hpow]
      have hdvd : orderOf g ∣ (i : ℕ) * n := by
        rw [horder]
        exact h
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  rw [← h1, h2]
  rw [card_fin_dvd_mul hN]
  simp [N, Nat.gcd_comm]

/--
The per-prime-power count: the number of solutions to `x^m = 1` in the unit
group of `ZMod (p^e)` is `gcd(m, φ(p^e))`, since that group is cyclic for odd
prime powers.
-/
lemma card_pow_eq_one_prime_pow {p e m : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    Nat.card {x : (ZMod (p ^ e))ˣ // x ^ m = 1} = Nat.gcd m (Nat.totient (p ^ e)) := by
  classical
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  have hcyc : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hcard : Fintype.card (ZMod (p ^ e))ˣ = Nat.totient (p ^ e) := by
    exact ZMod.card_units_eq_totient (p ^ e)
  have h := CLRS.Chapter31.card_pow_eq_one_cyclic (α := (ZMod (p ^ e))ˣ) m
  rw [hcard] at h
  exact h

/--
In a commutative finite group, the fiber of the `m`-th power map over any
element in its image has the same size as the kernel (the `m`-torsion).
-/
lemma card_pow_eq_c_of_exists {α : Type*} [CommGroup α] [Fintype α] [DecidableEq α]
    {m : ℕ} {c : α} (hc : ∃ x, x ^ m = c) :
    Nat.card {x : α // x ^ m = c} = Nat.card {x : α // x ^ m = 1} := by
  classical
  rcases hc with ⟨x₀, hx₀⟩
  let e : {x : α // x ^ m = 1} ≃ {x : α // x ^ m = c} :=
    { toFun := fun k => ⟨x₀ * k.1, by
        rw [mul_pow, hx₀, k.2]
        simp⟩
      invFun := fun x => ⟨x₀⁻¹ * x.1, by
        rw [mul_pow, inv_pow, hx₀, x.2]
        simp⟩
      left_inv := by
        intro k
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := by
        intro x
        apply Subtype.ext
        simp [mul_assoc] }
  exact (Nat.card_congr e).symm

/-- The fiber of the `m`-th power map over any element is no larger than the
kernel (it is empty, or a coset of the kernel). -/
lemma card_pow_le_card_pow_eq_one {α : Type*} [CommGroup α] [Fintype α] [DecidableEq α]
    {m : ℕ} {c : α} : Nat.card {x : α // x ^ m = c} ≤ Nat.card {x : α // x ^ m = 1} := by
  classical
  by_cases hc : ∃ x, x ^ m = c
  · rw [card_pow_eq_c_of_exists hc]
  · have : Nat.card {x : α // x ^ m = c} = 0 := by
      rw [Nat.card_eq_fintype_card]
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => hc ⟨x.1, x.2⟩⟩
    rw [this]
    exact Nat.zero_le _

/--
**CRT decomposition of the `m`-torsion.**  The number of units `x` modulo `n`
with `x^m = 1` is the product over the prime factors `p` of `n` of the number
of units modulo `p^(e_p)` (`e_p = v_p(n)`) with `x^m = 1`.
-/
lemma card_pow_eq_one_crt {n m : ℕ} (hn : n ≠ 0) :
    Nat.card {x : (ZMod n)ˣ // x ^ m = 1} =
      ∏ p : n.primeFactors, Nat.card {x : (ZMod (p ^ (n.factorization p)))ˣ // x ^ m = 1} := by
  classical
  let e : (ZMod n)ˣ ≃* Π p : n.primeFactors, (ZMod (p ^ (n.factorization p)))ˣ :=
    (Units.mapEquiv (ZMod.equivPi n hn : ZMod n ≃* Π p : n.primeFactors, ZMod (p ^ n.factorization p))).trans
      (MulEquiv.piUnits)
  have h1 : Nat.card {x : (ZMod n)ˣ // x ^ m = 1} =
      Nat.card {f : Π p : n.primeFactors, (ZMod (p ^ (n.factorization p)))ˣ // f ^ m = 1} := by
    apply Nat.card_congr
    refine (Equiv.subtypeEquiv e ?_)
    intro x
    constructor
    · intro hx
      calc
        (e x) ^ m = e (x ^ m) := (map_pow e x m).symm
        _ = 1 := by simp [hx]
    · intro hx
      apply e.injective
      calc
        e (x ^ m) = (e x) ^ m := map_pow e x m
        _ = 1 := hx
        _ = e 1 := by simp
  have h2 : Nat.card {f : Π p : n.primeFactors, (ZMod (p ^ (n.factorization p)))ˣ // f ^ m = 1} =
      ∏ p : n.primeFactors, Nat.card {b : (ZMod (p ^ (n.factorization p)))ˣ // b ^ m = 1} := by
    have h3 : Nat.card {f : Π p : n.primeFactors, (ZMod (p ^ (n.factorization p)))ˣ // f ^ m = 1} =
        Nat.card {f : Π p : n.primeFactors, (ZMod (p ^ (n.factorization p)))ˣ //
          ∀ p, (f p) ^ m = 1} := by
      apply Nat.card_congr
      refine (Equiv.subtypeEquiv (Equiv.refl _) ?_)
      intro f
      constructor
      · intro hf p
        have := congrFun hf p
        simpa using this
      · intro hf
        funext p
        simpa using hf p
    rw [h3]
    rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun p y => y ^ m = 1))]
    exact Nat.card_pi
  rw [h1, h2]

/-- An odd divisor of `2·u` divides `u`. -/
lemma odd_dvd_of_dvd_mul_two {d u : ℕ} (hd2 : d ∣ 2 * u) (hdodd : Odd d) : d ∣ u := by
  have hcop : d.Coprime 2 := Nat.coprime_two_right.mpr hdodd
  exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hd2)

/-- A divisor of an odd number is odd. -/
lemma odd_of_dvd_odd {d t : ℕ} (ht : Odd t) (hdt : d ∣ t) : Odd d := by
  by_contra hd
  have heven : Even d := (Nat.not_odd_iff_even.mp hd)
  have h2d : 2 ∣ d := even_iff_two_dvd.mp heven
  exact ht.not_two_dvd_nat (h2d.trans hdt)

/--
For `m = 2^(ν−1)·t` with `t` odd and `2^ν | p−1`, the greatest common divisor
of `m` and `p−1` is at most `(p−1)/2`: its 2-adic valuation is at most `ν−1`
and its odd part divides the odd part `(p−1)/2^ν`.
-/
lemma gcd_pow_mul_le_half {p ν t : ℕ} (hp : 0 < p - 1) (hν : 1 ≤ ν) (ht : Odd t)
    (hdvd : 2 ^ ν ∣ p - 1) :
    Nat.gcd (2 ^ (ν - 1) * t) (p - 1) ≤ (p - 1) / 2 := by
  rcases hdvd with ⟨u, hu⟩
  have hu_pos : 0 < u := by
    rw [hu] at hp
    apply Nat.pos_of_ne_zero
    intro hu0
    rw [hu0] at hp
    norm_num at hp
  have hu2 : 2 ^ ν * u = 2 ^ (ν - 1) * (2 * u) := by
    rw [← mul_assoc]
    congr 1
    rw [← pow_succ, Nat.sub_add_cancel hν]
  rw [hu, hu2]
  have hg : (2 ^ (ν - 1) * t).gcd (2 ^ (ν - 1) * (2 * u)) = 2 ^ (ν - 1) * t.gcd (2 * u) := by
    change gcd (2 ^ (ν - 1) * t) (2 ^ (ν - 1) * (2 * u)) = 2 ^ (ν - 1) * gcd t (2 * u)
    rw [gcd_mul_left]
    simp
  rw [hg]
  have hgu : Nat.gcd t (2 * u) ≤ u := by
    have hd2u : Nat.gcd t (2 * u) ∣ 2 * u := Nat.gcd_dvd_right _ _
    have hdodd : Odd (Nat.gcd t (2 * u)) :=
      odd_of_dvd_odd (d := Nat.gcd t (2 * u)) ht (Nat.gcd_dvd_left _ _)
    have hdu : Nat.gcd t (2 * u) ∣ u :=
      odd_dvd_of_dvd_mul_two (d := Nat.gcd t (2 * u)) hd2u hdodd
    exact Nat.le_of_dvd hu_pos hdu
  have hdiv : (2 ^ (ν - 1) * (2 * u)) / 2 = 2 ^ (ν - 1) * u := by
    rw [show 2 ^ (ν - 1) * (2 * u) = 2 * (2 ^ (ν - 1) * u) by ring]
    exact Nat.mul_div_right (2 ^ (ν - 1) * u) (by norm_num)
  rw [hdiv]
  exact Nat.mul_le_mul_left (2 ^ (ν - 1)) hgu

/-- `|{x : α // p x}|` equals the number of elements of `α` satisfying `p`. -/
lemma card_subtype_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x : α // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card]
  simpa [Fintype.card_subtype]

/-- The number of elements satisfying `p ∨ q` is at most the sum of the
numbers satisfying `p` and `q` separately. -/
lemma card_or_le {α : Type*} [Fintype α] [DecidableEq α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] :
    Nat.card {x : α // p x ∨ q x} ≤ Nat.card {x : α // p x} + Nat.card {x : α // q x} := by
  classical
  rw [card_subtype_filter (fun x => p x ∨ q x), card_subtype_filter p, card_subtype_filter q]
  have hset : (Finset.univ.filter p) ∪ (Finset.univ.filter q) = Finset.univ.filter (fun x => p x ∨ q x) := by
    ext x
    simp [Finset.mem_union, Finset.mem_filter]
  rw [← hset]
  exact Finset.card_union_le _ _

/--
The good set `{x : x^m ∈ {±1}}` has size at most twice the `m`-torsion:
it splits into the `x^m = 1` and `x^m = −1` parts, and the latter is no
larger than the former (a fiber of the power map).
-/
lemma goodSet_card_le {n : ℕ} [NeZero n] (m : ℕ) :
    Nat.card {x : (ZMod n)ˣ // x ∈ goodSet m} ≤
      2 * Nat.card {x : (ZMod n)ˣ // x ^ m = 1} := by
  classical
  have h1 : Nat.card {x : (ZMod n)ˣ // x ∈ goodSet m} =
      Nat.card {x : (ZMod n)ˣ // x ^ m = 1 ∨ x ^ m = -1} := by
    apply Nat.card_congr
    refine (Equiv.subtypeEquiv (Equiv.refl _) ?_)
    intro x
    exact mem_goodSet_iff m x
  rw [h1]
  have h2 := card_or_le (α := (ZMod n)ˣ) (fun x => x ^ m = 1) (fun x => x ^ m = -1)
  nlinarith [h2, card_pow_le_card_pow_eq_one (α := (ZMod n)ˣ) (m := m) (c := -1)]

/--
The `m`-torsion of `(ZMod n)ˣ` is the product over the prime factors `p` of
`n` of `gcd(m, φ(p^(e_p)))`, where `e_p = v_p(n)`.
-/
lemma mTorsion_eq_prod {n m : ℕ} (hn : n ≠ 0) (hn_odd : Odd n) :
    Nat.card {x : (ZMod n)ˣ // x ^ m = 1} =
      ∏ p : n.primeFactors, Nat.gcd m (Nat.totient (p ^ n.factorization p)) := by
  rw [card_pow_eq_one_crt hn]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
  have hpne2 : (p : ℕ) ≠ 2 := by
    intro h2
    have hdvd : (2 : ℕ) ∣ n := by
      rw [← h2]
      exact Nat.dvd_of_mem_primeFactors p.2
    have hne : ¬ Even n := (Nat.not_even_iff_odd.mpr hn_odd)
    exact hne (even_iff_two_dvd.mpr hdvd)
  exact card_pow_eq_one_prime_pow (p := (p : ℕ)) (e := n.factorization (p : ℕ)) (m := m) hpp hpne2

/-- `ν(n) ≤ v₂(n−1)`: every prime factor is `≡ 1 (mod 2^ν)`, so `n ≡ 1` and
`2^ν | n−1`. -/
lemma nu_le_v2_nat_sub_one {n : ℕ} (hn1 : 1 < n) (hn_odd : Odd n) :
    nu n ≤ (n - 1).factorization 2 := by
  have hnne : n.primeFactors.Nonempty := (Nat.nonempty_primeFactors).2 hn1
  have hmod : ∀ p ∈ n.primeFactors, p ≡ 1 [MOD 2 ^ nu n] := by
    intro p hp
    exact ((Nat.modEq_iff_dvd' (a := 1) (b := p) (Nat.succ_le_of_lt (Nat.pos_of_mem_primeFactors hp))).mpr
      (two_pow_nu_dvd_prime_sub_one (n := n) hnne hp)).symm
  have hprod : ∏ p : n.primeFactors, (p : ℕ) ^ n.factorization (p : ℕ) ≡ 1 [MOD 2 ^ nu n] := by
    exact Nat.ModEq.prod_one (s := Finset.univ)
      (f := fun p : n.primeFactors => (p : ℕ) ^ n.factorization (p : ℕ)) (by
        intro p hp
        simpa using (hmod p p.2).pow (n.factorization p))
  have hn_mod : n ≡ 1 [MOD 2 ^ nu n] := by
    conv_lhs =>
      rw [Nat.prod_pow_primeFactors_factorization (by omega : n ≠ 0)]
    exact hprod
  have hdvd : 2 ^ nu n ∣ n - 1 := (Nat.modEq_iff_dvd' (a := 1) (b := n) (by omega)).mp hn_mod.symm
  exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by omega)).1 hdvd

/-- `m = 2^(ν−1)·t` divides `n−1` (since `t·2^s = n−1` and `ν ≤ s`). -/
lemma mExp_dvd {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n) :
    2 ^ (nu n - 1) * (strongTestParams n).2 ∣ n - 1 := by
  have hs : (strongTestParams n).2 * 2 ^ (strongTestParams n).1 = n - 1 := by
    unfold strongTestParams
    have hdvd : 2 ^ (n - 1).factorization 2 ∣ n - 1 := by
      exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by omega)).2 le_rfl
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel' hdvd
  have hν_le_s : nu n - 1 ≤ (strongTestParams n).1 := by
    have hν_s : nu n ≤ (n - 1).factorization 2 := nu_le_v2_nat_sub_one hn1 hn_odd
    unfold strongTestParams
    omega
  have hpow_dvd : 2 ^ (nu n - 1) ∣ 2 ^ (strongTestParams n).1 := by
    exact pow_dvd_pow 2 hν_le_s
  have hmul : 2 ^ (nu n - 1) * (strongTestParams n).2 ∣
      2 ^ (strongTestParams n).1 * (strongTestParams n).2 := by
    exact Nat.mul_dvd_mul hpow_dvd (dvd_refl _)
  rw [← hs]
  simpa [mul_comm] using hmul

/-- `m` is coprime to every prime factor `p` of `n`: `m | n−1` and `p | n`. -/
lemma mExp_coprime_prime {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n)
    {p : ℕ} (hp : p ∈ n.primeFactors) :
    (2 ^ (nu n - 1) * (strongTestParams n).2).Coprime p := by
  have hmn : 2 ^ (nu n - 1) * (strongTestParams n).2 ∣ n - 1 := mExp_dvd (n := n) hn1 hn_odd
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hcop : (n - 1).Coprime n := by
    exact ((Nat.coprime_self_sub_right (m := 1) (n := n) (by omega)).mpr (by simp)).symm
  exact (hcop.of_dvd_left hmn).of_dvd_right hpn

/-- `gcd a (b·c) = gcd a c` when `a` is coprime to `b`. -/
lemma gcd_eq_gcd_of_coprime {a b c : ℕ} (h : a.Coprime b) : a.gcd (b * c) = a.gcd c := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · have hd2 : a.gcd (b * c) ∣ b * c := Nat.gcd_dvd_right _ _
      have hcop : (a.gcd (b * c)).Coprime b := h.of_dvd_left (Nat.gcd_dvd_left _ _)
      exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hd2)
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_left _ _
    · exact (Nat.gcd_dvd_right _ _).trans (dvd_mul_left c b)

/-- `gcd(m, φ(p^e)) = gcd(m, p−1)` when `gcd(m, p) = 1` and `0 < e`. -/
lemma gcd_totient_eq_gcd_prime {p e m : ℕ} (hp : Nat.Prime p) (he : 0 < e)
    (hpm : m.Coprime p) : m.gcd (Nat.totient (p ^ e)) = m.gcd (p - 1) := by
  rw [Nat.totient_prime_pow hp he]
  have hpm' : m.Coprime (p ^ (e - 1)) := hpm.pow_right (e - 1)
  exact gcd_eq_gcd_of_coprime (a := m) (b := p ^ (e - 1)) (c := p - 1) hpm'

/--
The `m`-torsion is at most the product over the prime factors of `(p−1)/2`,
where `m = 2^(ν(n)−1)·t`.
-/
lemma mTorsion_le_prod_half {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n) :
    Nat.card {x : (ZMod n)ˣ // x ^ (2 ^ (nu n - 1) * (strongTestParams n).2) = 1} ≤
      ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2 := by
  rw [mTorsion_eq_prod (by omega) hn_odd]
  have hν : 1 ≤ nu n := nu_pos hn_odd hn1
  have ht : Odd (strongTestParams n).2 := strongTestParams_odd hn1
  have hnne : n.primeFactors.Nonempty := (Nat.nonempty_primeFactors).2 hn1
  apply Finset.prod_le_prod'
  intro p hp
  have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
  have hppos : 0 < (p : ℕ) - 1 := by
    have := hpp.two_le
    omega
  have hpm : (2 ^ (nu n - 1) * (strongTestParams n).2).Coprime (p : ℕ) :=
    mExp_coprime_prime (n := n) hn1 hn_odd p.2
  have hdvd : 2 ^ nu n ∣ (p : ℕ) - 1 := two_pow_nu_dvd_prime_sub_one (n := n) hnne p.2
  have he : 0 < n.factorization (p : ℕ) := by
    exact hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors p.2)
  calc
    (2 ^ (nu n - 1) * (strongTestParams n).2).gcd (Nat.totient ((p : ℕ) ^ n.factorization (p : ℕ)))
        = (2 ^ (nu n - 1) * (strongTestParams n).2).gcd ((p : ℕ) - 1) := by
      exact gcd_totient_eq_gcd_prime hpp he hpm
    _ ≤ ((p : ℕ) - 1) / 2 := gcd_pow_mul_le_half (p := (p : ℕ)) (ν := nu n) (t := (strongTestParams n).2)
      hppos hν ht hdvd

/-- For an odd prime `p`, `2 ∣ p − 1`. -/
lemma two_dvd_prime_sub_one_of_odd {p : ℕ} (hp : Nat.Prime p) (hp_odd : Odd p) :
    2 ∣ p - 1 := by
  rcases (odd_iff_exists_bit1.mp hp_odd) with ⟨k, rfl⟩
  exact ⟨k, by omega⟩

/-- A product over the single prime factor `p` of `n` is just the value at `p`. -/
lemma prod_primeFactors_singleton {n p : ℕ} (hpf : n.primeFactors = ({p} : Finset ℕ))
    (f : ℕ → ℕ) : ∏ q : n.primeFactors, f (q : ℕ) = f p := by
  rw [hpf]
  simp

/--
The product over the prime factors `p | n` of `p−1` equals `2^k` times the
product of `(p−1)/2`, since each odd prime factor satisfies `2 | p−1`.
-/
lemma prod_prime_sub_one_eq_two_mul {n : ℕ} (hn_odd : Odd n) (hn1 : 1 < n) :
    ∏ p : n.primeFactors, ((p : ℕ) - 1) =
      2 ^ n.primeFactors.card * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2 := by
  calc
    ∏ p : n.primeFactors, ((p : ℕ) - 1) =
        ∏ p : n.primeFactors, 2 * (((p : ℕ) - 1) / 2) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
      have hpdvd : (p : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors p.2
      have hpodd : Odd (p : ℕ) := odd_of_dvd_odd hn_odd hpdvd
      have h2 : 2 ∣ (p : ℕ) - 1 := two_dvd_prime_sub_one_of_odd hpp hpodd
      rw [mul_comm]
      exact (Nat.div_mul_cancel h2).symm
    _ = (∏ p : n.primeFactors, 2) * ∏ p : n.primeFactors, (((p : ℕ) - 1) / 2) := by
      rw [Finset.prod_mul_distrib]
    _ = 2 ^ n.primeFactors.card * ∏ p : n.primeFactors, (((p : ℕ) - 1) / 2) := by
      simp [Finset.prod_const]

/-- `∏_{p|n}(p−1) ≤ n−1`: each `p−1 < p`, and `∏ p ≤ n`. -/
lemma prod_prime_sub_one_le {n : ℕ} (hn1 : 1 < n) :
    ∏ p : n.primeFactors, ((p : ℕ) - 1) ≤ n - 1 := by
  have hlt : ∏ p : n.primeFactors, ((p : ℕ) - 1) < ∏ p : n.primeFactors, (p : ℕ) := by
    refine Finset.prod_lt_prod (s := (Finset.univ : Finset n.primeFactors)) ?_ ?_ ?_
    · intro p hp
      have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
      have h2 : 2 ≤ (p : ℕ) := hpp.two_le
      omega
    · intro p hp
      exact Nat.sub_le _ _
    · rcases (Nat.nonempty_primeFactors).2 hn1 with ⟨p0, hp0⟩
      refine ⟨⟨p0, hp0⟩, by simp, ?_⟩
      have hpp : Nat.Prime p0 := Nat.prime_of_mem_primeFactors hp0
      have h2 : 2 ≤ p0 := hpp.two_le
      change p0 - 1 < p0
      omega
  have hle : ∏ p : n.primeFactors, (p : ℕ) ≤ n := by
    calc
      ∏ p : n.primeFactors, (p : ℕ) ≤
          ∏ p : n.primeFactors, (p : ℕ) ^ (n.factorization (p : ℕ)) := by
        refine Finset.prod_le_prod' (s := (Finset.univ : Finset n.primeFactors))
          (f := fun p : n.primeFactors => (p : ℕ))
          (g := fun p : n.primeFactors => (p : ℕ) ^ (n.factorization (p : ℕ))) ?_
        intro p hp
        have hpp : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.2
        have hpos : 0 < n.factorization (p : ℕ) :=
          hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors p.2)
        exact le_self_pow (by have h2 := hpp.two_le; omega) hpos.ne'
      _ = n := (Nat.prod_pow_primeFactors_factorization (by omega : n ≠ 0)).symm
  omega

/--
The good subgroup `S(n)` has size at most `2·∏_{p|n}(p−1)/2`: the union
bound `goodSet_card_le` splits off the factor 2, and the `m`-torsion is at
most `∏(p−1)/2` by `mTorsion_le_prod_half`.
-/
lemma goodUnits_card_le_prodHalf {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n) :
    Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤
      2 * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2 := by
  unfold goodUnits
  calc
    Nat.card {x : (ZMod n)ˣ // x ∈ goodSet (2 ^ (nu n - 1) * (strongTestParams n).2)} ≤
        2 * Nat.card {x : (ZMod n)ˣ // x ^ (2 ^ (nu n - 1) * (strongTestParams n).2) = 1} :=
      goodSet_card_le (n := n) (2 ^ (nu n - 1) * (strongTestParams n).2)
    _ ≤ 2 * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2 := by
      exact Nat.mul_le_mul_left 2 (mTorsion_le_prod_half (n := n) hn1 hn_odd)

/-- For `n` with at least three prime factors, `|S(n)| ≤ (n−1)/4`. -/
lemma goodUnits_card_le_of_ge_three {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n)
    (hk : 3 ≤ n.primeFactors.card) :
    Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ (n - 1) / 4 := by
  have h8 : 8 * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2 ≤ n - 1 := by
    calc
      8 * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2
          ≤ 2 ^ n.primeFactors.card * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2 := by
            exact Nat.mul_le_mul_right _ (by
              have hpow : 2 ^ 3 ≤ 2 ^ n.primeFactors.card :=
                pow_le_pow_right₀ (by norm_num) hk
              norm_num at hpow
              exact hpow)
      _ = ∏ p : n.primeFactors, ((p : ℕ) - 1) :=
            (prod_prime_sub_one_eq_two_mul (n := n) hn_odd hn1).symm
      _ ≤ n - 1 := prod_prime_sub_one_le (n := n) hn1
  have h4 : 4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ n - 1 := by
    calc
      4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits}
          ≤ 4 * (2 * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2) :=
            Nat.mul_le_mul_left 4 (goodUnits_card_le_prodHalf (n := n) hn1 hn_odd)
      _ = 8 * ∏ p : n.primeFactors, ((p : ℕ) - 1) / 2 := by ring
      _ ≤ n - 1 := h8
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by simpa [mul_comm] using h4)

/-- For `n = p^e` a prime power (composite), `|S(n)| ≤ (n−1)/4`. -/
lemma goodUnits_card_le_prime_power {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n)
    (hn_comp : ¬ Nat.Prime n) (hk : n.primeFactors.card = 1) :
    Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ (n - 1) / 4 := by
  rcases Finset.card_eq_one.mp hk with ⟨p, hpf⟩
  have hp_mem : p ∈ n.primeFactors := by rw [hpf]; simp
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hpodd : Odd p := odd_of_dvd_odd hn_odd (Nat.dvd_of_mem_primeFactors hp_mem)
  have hne : n = p ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_pow_primeFactors_factorization (by omega : n ≠ 0)]
    exact prod_primeFactors_singleton (n := n) (p := p) hpf
      (fun x : ℕ => x ^ (n.factorization x))
  have he1 : 1 ≤ n.factorization p :=
    hpp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp_mem)
  have hne1 : n.factorization p ≠ 1 := by
    intro h1
    have : n = p := by simpa [h1] using hne
    exact hn_comp (by simpa [this] using hpp)
  have he : 2 ≤ n.factorization p := by omega
  have hp_ne2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpodd
    norm_num at hpodd
  have hp2_le_n : p ^ 2 ≤ n := by
    have hp2d : p ^ 2 ∣ n := (hpp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).2 he
    exact Nat.le_of_dvd (by omega : 0 < n) hp2d
  have hsp : Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ p - 1 := by
    calc
      Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits}
          ≤ 2 * ∏ q : n.primeFactors, ((q : ℕ) - 1) / 2 :=
            goodUnits_card_le_prodHalf (n := n) hn1 hn_odd
      _ = 2 * ((p - 1) / 2) := by
        rw [hpf]
        simp
      _ = p - 1 := by
        have h2 : 2 ∣ p - 1 := two_dvd_prime_sub_one_of_odd hpp hpodd
        calc
          2 * ((p - 1) / 2) = ((p - 1) / 2) * 2 := by omega
          _ = p - 1 := Nat.div_mul_cancel h2
  have hp3 : 3 ≤ p := by
    exact Nat.succ_le_of_lt (lt_of_le_of_ne hpp.two_le (Ne.symm hp_ne2))
  have hsq : 4 * (p - 1) ≤ p ^ 2 - 1 := by
    have hsqf : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      simpa [mul_comm] using (Nat.sq_sub_sq p 1)
    rw [hsqf]
    rw [mul_comm 4 (p - 1)]
    exact Nat.mul_le_mul_left (p - 1) (by omega : 4 ≤ p + 1)
  have h4p : 4 * (p - 1) ≤ n - 1 := by
    exact hsq.trans (by omega)
  have h4 : 4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ n - 1 := by
    calc
      4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ 4 * (p - 1) :=
        Nat.mul_le_mul_left 4 hsp
      _ ≤ n - 1 := h4p
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by simpa [mul_comm] using h4)

/-- An odd divisor `g` of an odd `d` is at most `d/3`. -/
lemma odd_divisor_le_div_three {d g : ℕ} (hd : Odd d) (hg : g ∣ d) (hlt : g ≠ d) : g ≤ d / 3 := by
  rcases hg with ⟨c, rfl⟩
  have hc_ne1 : c ≠ 1 := by
    intro h1
    apply hlt
    rw [h1, mul_one]
  have hc_ne0 : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero] at hd
    norm_num at hd
  have hodd_c : Odd c := (Nat.odd_mul.mp hd).2
  have hc3 : 3 ≤ c := by
    rcases (odd_iff_exists_bit1.mp hodd_c) with ⟨k, rfl⟩
    have hk0 : 1 ≤ k := by
      by_contra hk
      have hk0' : k = 0 := by omega
      rw [hk0'] at hc_ne1
      norm_num at hc_ne1
    omega
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
  exact Nat.mul_le_mul_left g hc3

/-- For a prime `p`, `p−1 = 2^s·((p−1)/2^s)` where `s = v₂(p−1)`. -/
lemma prime_sub_one_decomp {p : ℕ} (hp : Nat.Prime p) :
    p - 1 = 2 ^ (p - 1).factorization 2 * ((p - 1) / 2 ^ (p - 1).factorization 2) := by
  have hppos : p - 1 ≠ 0 := by
    have h2 := hp.two_le
    omega
  have hdvd : 2 ^ (p - 1).factorization 2 ∣ p - 1 := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hppos).2 le_rfl
  exact (Nat.mul_div_cancel' hdvd).symm

/-- The odd part `t` of `n−1` divides `n−1`. -/
lemma strongTestParams_snd_dvd {n : ℕ} (hn1 : 1 < n) : (strongTestParams n).2 ∣ n - 1 := by
  unfold strongTestParams
  change (n - 1) / 2 ^ (n - 1).factorization 2 ∣ n - 1
  have hdvd : 2 ^ (n - 1).factorization 2 ∣ n - 1 := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by omega)).2 le_rfl
  refine ⟨2 ^ (n - 1).factorization 2, by rw [mul_comm]; exact (Nat.mul_div_cancel' hdvd).symm⟩

/-- `ν(p·q) = min (v₂(p−1)) (v₂(q−1))` for distinct primes `p`, `q`. -/
lemma nu_semiprime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    nu (p * q) = min ((p - 1).factorization 2) ((q - 1).factorization 2) := by
  let s := (p - 1).factorization 2
  let r := (q - 1).factorization 2
  have hpq_fac : (p * q).primeFactors = ({p, q} : Finset ℕ) := by
    rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero]
    rw [Nat.Prime.primeFactors hp, Nat.Prime.primeFactors hq]
    ext x
    simp
  unfold nu
  rw [dif_pos (by rw [hpq_fac]; simp)]
  simp [hpq_fac]

/-- `gcd(2^(ν−1)·t, 2^s·d) = 2^(ν−1)·gcd(t, d)` when `1 ≤ ν ≤ s` and `t` is odd. -/
lemma gcd_pow_mul_oddPart {t s ν d : ℕ} (hν1 : 1 ≤ ν) (hνs : ν ≤ s) (ht : Odd t) :
    (2 ^ (ν - 1) * t).gcd (2 ^ s * d) = 2 ^ (ν - 1) * t.gcd d := by
  have hpow : 2 ^ s = 2 ^ (ν - 1) * 2 ^ (s - ν + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  rw [mul_assoc]
  rw [Nat.gcd_mul_left]
  have hcop : t.Coprime (2 ^ (s - ν + 1)) := by
    exact (Nat.coprime_two_right.mpr ht).pow_right (s - ν + 1)
  rw [gcd_eq_gcd_of_coprime hcop]

/-- `(2^s·d_p)·(2^r·d_q) = 2^(s+r)·(d_p·d_q)`. -/
lemma pow_mul_mul {s r d_p d_q : ℕ} : (2 ^ s * d_p) * (2 ^ r * d_q) = 2 ^ (s + r) * (d_p * d_q) := by
  rw [pow_add]
  ring

/-- For primes `p, q ≥ 3`, `(p−1)(q−1) ≤ p·q−1`. -/
lemma prod_sub_one_le {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) : (p - 1) * (q - 1) ≤ p * q - 1 := by
  calc
    (p - 1) * (q - 1) ≤ (p - 1) * q := Nat.mul_le_mul_left (p - 1) (Nat.sub_le _ _)
    _ = p * q - q := by
      rw [Nat.mul_sub_right_distrib]
      simp
    _ ≤ p * q - 1 := by omega


/-- A product over `n.primeFactors = {p, q}` is `f p·f q`. -/
lemma prod_primeFactors_pair {n p q : ℕ} (hpf : n.primeFactors = ({p, q} : Finset ℕ)) (hpq : p ≠ q)
    (f : ℕ → ℕ) : ∏ x : n.primeFactors, f (x : ℕ) = f p * f q := by
  rw [hpf]
  change (({p, q} : Finset ℕ).attach.prod (fun x : {x // x ∈ ({p, q} : Finset ℕ)} => f (x : ℕ))) = f p * f q
  simp only [Finset.prod_attach]
  rw [show ({p, q} : Finset ℕ) = insert p {q} by ext x; simp]
  rw [Finset.prod_insert]
  · simp
  · simp [hpq]

/-- **Key lemma.** For `n = p·q`, if `d_p | t` and `d_q | t` then `d_p = d_q`. -/
lemma semiprime_key_lemma {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    ((p - 1) / 2 ^ (p - 1).factorization 2) ∣ (strongTestParams (p * q)).2 →
    ((q - 1) / 2 ^ (q - 1).factorization 2) ∣ (strongTestParams (p * q)).2 →
    (p - 1) / 2 ^ (p - 1).factorization 2 = (q - 1) / 2 ^ (q - 1).factorization 2 := by
  classical
  intro hdp_t hdq_t
  let s := (p - 1).factorization 2
  let r := (q - 1).factorization 2
  let d_p : ℕ := (p - 1) / 2 ^ s
  let d_q : ℕ := (q - 1) / 2 ^ r
  let t : ℕ := (strongTestParams (p * q)).2
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hpq1 : 1 < p * q := by
    have h4 : 4 ≤ p * q := Nat.mul_le_mul hp2 hq2
    omega
  have hdp : d_p ∣ t := by simpa [d_p, s, t] using hdp_t
  have hdq : d_q ∣ t := by simpa [d_q, r, t] using hdq_t
  have htpq : t ∣ p * q - 1 := by simpa [t] using strongTestParams_snd_dvd (n := p * q) hpq1
  have hdppq : d_p ∣ p * q - 1 := hdp.trans htpq
  have hp_eq : p = 2 ^ s * d_p + 1 := by
    have h1 : p - 1 = 2 ^ s * d_p := by
      dsimp [d_p]
      simpa [s] using (prime_sub_one_decomp hp)
    omega
  have hq_eq : q = 2 ^ r * d_q + 1 := by
    have h1 : q - 1 = 2 ^ r * d_q := by
      dsimp [d_q]
      simpa [r] using (prime_sub_one_decomp hq)
    omega
  have hfac : p * q - 1 = d_p * (2 ^ (s + r) * d_q + 2 ^ s) + 2 ^ r * d_q := by
    rw [hp_eq, hq_eq]
    calc
      (2 ^ s * d_p + 1) * (2 ^ r * d_q + 1) - 1
          = (2 ^ s * d_p) * (2 ^ r * d_q) + 2 ^ s * d_p + 2 ^ r * d_q + 1 - 1 := by
            have h : (2 ^ s * d_p + 1) * (2 ^ r * d_q + 1) =
                (2 ^ s * d_p) * (2 ^ r * d_q) + 2 ^ s * d_p + 2 ^ r * d_q + 1 := by ring
            rw [h]
      _ = (2 ^ s * d_p) * (2 ^ r * d_q) + 2 ^ s * d_p + 2 ^ r * d_q := by
            rw [Nat.add_sub_cancel]
      _ = 2 ^ (s + r) * (d_p * d_q) + 2 ^ s * d_p + 2 ^ r * d_q := by
        rw [pow_mul_mul (s := s) (r := r)]
      _ = d_p * (2 ^ (s + r) * d_q + 2 ^ s) + 2 ^ r * d_q := by ring
  have hdvd_rest : d_p ∣ 2 ^ r * d_q := by
    rw [hfac] at hdppq
    have hdpk : d_p ∣ d_p * (2 ^ (s + r) * d_q + 2 ^ s) := dvd_mul_right _ _
    exact (Nat.dvd_add_iff_left hdpk).mpr (by simpa [add_comm] using hdppq)
  have hdvd_dq : d_p ∣ d_q := by
    have hodd_dp : Odd d_p := by
      dsimp [d_p]
      have hp1 : p - 1 ≠ 0 := by omega
      simpa [s] using oddPart_odd (p - 1) hp1
    have hcop : d_p.Coprime (2 ^ r) := (Nat.coprime_two_right.mpr hodd_dp).pow_right r
    exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdvd_rest)
  have hdvd_dp : d_q ∣ d_p := by
    have hdqq : d_q ∣ p * q - 1 := hdq.trans htpq
    have hfac2 : p * q - 1 = d_q * (2 ^ (s + r) * d_p + 2 ^ r) + 2 ^ s * d_p := by
      rw [hp_eq, hq_eq]
      calc
        (2 ^ s * d_p + 1) * (2 ^ r * d_q + 1) - 1
            = (2 ^ s * d_p) * (2 ^ r * d_q) + 2 ^ s * d_p + 2 ^ r * d_q + 1 - 1 := by
              have h : (2 ^ s * d_p + 1) * (2 ^ r * d_q + 1) =
                  (2 ^ s * d_p) * (2 ^ r * d_q) + 2 ^ s * d_p + 2 ^ r * d_q + 1 := by ring
              rw [h]
        _ = (2 ^ s * d_p) * (2 ^ r * d_q) + 2 ^ s * d_p + 2 ^ r * d_q := by
              rw [Nat.add_sub_cancel]
        _ = 2 ^ (s + r) * (d_p * d_q) + 2 ^ s * d_p + 2 ^ r * d_q := by
          rw [pow_mul_mul (s := s) (r := r)]
        _ = d_q * (2 ^ (s + r) * d_p + 2 ^ r) + 2 ^ s * d_p := by ring
    have hdvd_rest2 : d_q ∣ 2 ^ s * d_p := by
      rw [hfac2] at hdqq
      have hdqk : d_q ∣ d_q * (2 ^ (s + r) * d_p + 2 ^ r) := dvd_mul_right _ _
      exact (Nat.dvd_add_iff_left hdqk).mpr (by simpa [add_comm] using hdqq)
    have hodd_dq : Odd d_q := by
      dsimp [d_q]
      have hq1 : q - 1 ≠ 0 := by omega
      simpa [r] using oddPart_odd (q - 1) hq1
    have hcop : d_q.Coprime (2 ^ s) := (Nat.coprime_two_right.mpr hodd_dq).pow_right s
    exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdvd_rest2)
  exact Nat.dvd_antisymm hdvd_dq hdvd_dp

/-- `8·gcd(m,p−1)·gcd(m,q−1) ≤ n−1` when `v₂(p−1) ≤ v₂(q−1)`. -/
lemma semiprime_gcd_bound_sle {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hle : (p - 1).factorization 2 ≤ (q - 1).factorization 2) :
    8 * ((2 ^ (nu (p * q) - 1) * (strongTestParams (p * q)).2).gcd (p - 1)) *
        ((2 ^ (nu (p * q) - 1) * (strongTestParams (p * q)).2).gcd (q - 1)) ≤
      p * q - 1 := by
  classical
  let s := (p - 1).factorization 2
  let r := (q - 1).factorization 2
  let ν := nu (p * q)
  let t := (strongTestParams (p * q)).2
  let d_p := (p - 1) / 2 ^ s
  let d_q := (q - 1) / 2 ^ r
  let g_p := t.gcd d_p
  let g_q := t.gcd d_q
  have hν : ν = s := by
    have hmin : nu (p * q) = min s r := by simpa [s, r] using nu_semiprime hp hq
    omega
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hq3 : 3 ≤ q := by
    have h2 := hq.two_le
    omega
  have hpodd : Odd p := (hp.odd_iff).mpr hp3
  have hqodd : Odd q := (hq.odd_iff).mpr hq3
  have ht : Odd t := by
    dsimp [t]
    exact strongTestParams_odd (n := p * q) (by
      have h4 : 4 ≤ p * q := Nat.mul_le_mul hp.two_le hq.two_le
      omega)
  have hν1 : 1 ≤ ν := by
    have hs1 : 1 ≤ s := by
      dsimp [s]
      exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by
        have h2 := hp.two_le; omega)).1 (by
        simpa using two_dvd_prime_sub_one_of_odd hp hpodd)
    omega
  have hodd_dp : Odd d_p := by
    dsimp [d_p]
    have hpp1 : p - 1 ≠ 0 := by
      have h2 := hp.two_le
      omega
    simpa [s] using oddPart_odd (p - 1) hpp1
  have hodd_dq : Odd d_q := by
    dsimp [d_q]
    have hqq1 : q - 1 ≠ 0 := by
      have h2 := hq.two_le
      omega
    simpa [r] using oddPart_odd (q - 1) hqq1
  have hdp : p - 1 = 2 ^ s * d_p := by
    dsimp [d_p]
    simpa [s] using prime_sub_one_decomp hp
  have hdq : q - 1 = 2 ^ r * d_q := by
    dsimp [d_q]
    simpa [r] using prime_sub_one_decomp hq
  have hgs : ν ≤ s := by omega
  have hgr : ν ≤ r := by omega
  have hga : (2 ^ (ν - 1) * t).gcd (p - 1) = 2 ^ (ν - 1) * g_p := by
    rw [hdp]
    dsimp [g_p]
    exact gcd_pow_mul_oddPart (t := t) (s := s) (ν := ν) (d := d_p) hν1 hgs ht
  have hgb : (2 ^ (ν - 1) * t).gcd (q - 1) = 2 ^ (ν - 1) * g_q := by
    rw [hdq]
    dsimp [g_q]
    exact gcd_pow_mul_oddPart (t := t) (s := r) (ν := ν) (d := d_q) hν1 hgr ht
  have hmain : 8 * (2 ^ (ν - 1) * g_p) * (2 ^ (ν - 1) * g_q) ≤ (p - 1) * (q - 1) := by
    have hpow8 : 8 * (2 ^ (ν - 1) * g_p) * (2 ^ (ν - 1) * g_q) = 2 ^ (2 * ν + 1) * g_p * g_q := by
      calc
        8 * (2 ^ (ν - 1) * g_p) * (2 ^ (ν - 1) * g_q)
            = 8 * 2 ^ (ν - 1) * g_p * 2 ^ (ν - 1) * g_q := by ring
        _ = 2 ^ 3 * 2 ^ (ν - 1) * 2 ^ (ν - 1) * g_p * g_q := by
              rw [show 8 = 2 ^ 3 by norm_num]
              ring
        _ = 2 ^ (3 + (ν - 1) + (ν - 1)) * g_p * g_q := by
              rw [← pow_add]
              rw [← pow_add]
        _ = 2 ^ (2 * ν + 1) * g_p * g_q := by
              have hexp : 3 + (ν - 1) + (ν - 1) = 2 * ν + 1 := by
                omega
              rw [hexp]
    rw [hpow8]
    have htarget : 2 ^ (2 * ν + 1) * g_p * g_q ≤ 2 ^ (s + r) * (d_p * d_q) := by
      rw [hν]
      by_cases hsr : s = r
      · have h2g : 2 * g_p * g_q ≤ d_p * d_q := by
          have hnot : ¬ (g_p = d_p ∧ g_q = d_q) := by
            intro hboth
            rcases hboth with ⟨hg1, hg2⟩
            have hd1 : d_p ∣ t := by
              rw [← hg1]
              dsimp [g_p]
              exact Nat.gcd_dvd_left t d_p
            have hd2 : d_q ∣ t := by
              rw [← hg2]
              dsimp [g_q]
              exact Nat.gcd_dvd_left t d_q
            have hdeq : d_p = d_q := semiprime_key_lemma hp hq hpq hd1 hd2
            have hp_eq : p = q := by
              have h1 : p - 1 = 2 ^ s * d_p := by
                dsimp [d_p]
                simpa [s] using prime_sub_one_decomp hp
              have h2 : q - 1 = 2 ^ r * d_q := by
                dsimp [d_q]
                simpa [r] using prime_sub_one_decomp hq
              have hsub : p - 1 = q - 1 := by
                calc
                  p - 1 = 2 ^ s * d_p := h1
                  _ = 2 ^ r * d_q := by rw [hsr, hdeq]
                  _ = q - 1 := h2.symm
              omega
            exact hpq hp_eq
          have hprop : g_p ≠ d_p ∨ g_q ≠ d_q := by
            by_contra hc
            push Not at hc
            exact hnot hc
          have hg_p_dvd : g_p ∣ d_p := by dsimp [g_p]; exact Nat.gcd_dvd_right t d_p
          have hg_q_dvd : g_q ∣ d_q := by dsimp [g_q]; exact Nat.gcd_dvd_right t d_q
          have hd_p_pos : 0 < d_p := by
            dsimp [d_p]
            have hpp : 0 < p - 1 := by
              have h2 := hp.two_le
              omega
            exact Nat.div_pos (Nat.le_of_dvd hpp (by
              exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by
                have h2 := hp.two_le; omega)).2 le_rfl)) (by norm_num : 0 < 2 ^ s)
          have hd_q_pos : 0 < d_q := by
            dsimp [d_q]
            have hqq : 0 < q - 1 := by
              have h2 := hq.two_le
              omega
            exact Nat.div_pos (Nat.le_of_dvd hqq (by
              exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by
                have h2 := hq.two_le; omega)).2 le_rfl)) (by norm_num : 0 < 2 ^ r)
          rcases hprop with hne1 | hne2
          · have hlt1 : g_p < d_p := lt_of_le_of_ne (Nat.le_of_dvd hd_p_pos hg_p_dvd) hne1
            have h13 : g_p ≤ d_p / 3 := odd_divisor_le_div_three hodd_dp hg_p_dvd hne1
            have hq_le : g_q ≤ d_q := Nat.le_of_dvd hd_q_pos hg_q_dvd
            have h23 : 2 * (d_p / 3) * d_q ≤ d_p * d_q := by
              have h2 : 2 * (d_p / 3) ≤ d_p := by omega
              exact Nat.mul_le_mul_right d_q h2
            calc
              2 * g_p * g_q ≤ 2 * (d_p / 3) * d_q := by
                exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 h13) hq_le
              _ ≤ d_p * d_q := h23
          · have h23 : g_q ≤ d_q / 3 := odd_divisor_le_div_three hodd_dq hg_q_dvd hne2
            have hp_le : g_p ≤ d_p := Nat.le_of_dvd hd_p_pos hg_p_dvd
            have h23' : 2 * (d_q / 3) * d_p ≤ d_q * d_p := by
              have h2 : 2 * (d_q / 3) ≤ d_q := by omega
              exact Nat.mul_le_mul_right d_p h2
            calc
              2 * g_p * g_q = 2 * g_q * g_p := by ring
              _ ≤ 2 * (d_q / 3) * d_p := by
                exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 h23) hp_le
              _ ≤ d_q * d_p := h23'
              _ = d_p * d_q := by ring
        calc
          2 ^ (2 * s + 1) * g_p * g_q = 2 ^ (s + r) * (2 * g_p * g_q) := by
            rw [hsr]
            rw [pow_add]
            norm_num
            ring
          _ ≤ 2 ^ (s + r) * (d_p * d_q) := by
            exact Nat.mul_le_mul_left (2 ^ (s + r)) h2g
      · have hlt : s < r := lt_of_le_of_ne hle hsr
        have hpow_le : 2 ^ (2 * s + 1) ≤ 2 ^ (s + r) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
        have hg_p_le : g_p ≤ d_p := by
          have hpp : 0 < d_p := by
            dsimp [d_p]
            have hpp' : 0 < p - 1 := by
              have h2 := hp.two_le
              omega
            exact Nat.div_pos (Nat.le_of_dvd hpp' (by
              exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by
                have h2 := hp.two_le; omega)).2 le_rfl)) (by norm_num : 0 < 2 ^ s)
          exact Nat.le_of_dvd hpp (by dsimp [g_p]; exact Nat.gcd_dvd_right t d_p)
        have hg_q_le : g_q ≤ d_q := by
          have hqq : 0 < d_q := by
            dsimp [d_q]
            have hqq' : 0 < q - 1 := by
              have h2 := hq.two_le
              omega
            exact Nat.div_pos (Nat.le_of_dvd hqq' (by
              exact (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) (by
                have h2 := hq.two_le; omega)).2 le_rfl)) (by norm_num : 0 < 2 ^ r)
          exact Nat.le_of_dvd hqq (by dsimp [g_q]; exact Nat.gcd_dvd_right t d_q)
        calc
          2 ^ (2 * s + 1) * g_p * g_q ≤ 2 ^ (s + r) * d_p * d_q := by
            exact Nat.mul_le_mul (Nat.mul_le_mul hpow_le hg_p_le) hg_q_le
          _ = 2 ^ (s + r) * (d_p * d_q) := by ring
    calc
      2 ^ (2 * ν + 1) * g_p * g_q ≤ 2 ^ (s + r) * (d_p * d_q) := htarget
      _ = (p - 1) * (q - 1) := by
        rw [hdp, hdq]
        rw [pow_mul_mul (s := s) (r := r)]
  calc
    8 * ((2 ^ (ν - 1) * t).gcd (p - 1)) * ((2 ^ (ν - 1) * t).gcd (q - 1))
        = 8 * (2 ^ (ν - 1) * g_p) * (2 ^ (ν - 1) * g_q) := by rw [hga, hgb]
    _ ≤ (p - 1) * (q - 1) := hmain
    _ ≤ p * q - 1 := prod_sub_one_le hp3 hq3

/-- `8·gcd(m,p−1)·gcd(m,q−1) ≤ n−1` for `n` with `n.primeFactors = {p,q}`. -/
lemma semiprime_gcd_bound {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    8 * ((2 ^ (nu (p * q) - 1) * (strongTestParams (p * q)).2).gcd (p - 1)) *
        ((2 ^ (nu (p * q) - 1) * (strongTestParams (p * q)).2).gcd (q - 1)) ≤
      p * q - 1 := by
  by_cases hle : (p - 1).factorization 2 ≤ (q - 1).factorization 2
  · exact semiprime_gcd_bound_sle hp hq hpq hp2 hq2 hle
  · have hle' : (q - 1).factorization 2 ≤ (p - 1).factorization 2 := by omega
    have hmain := semiprime_gcd_bound_sle (p := q) (q := p) hq hp (Ne.symm hpq) hq2 hp2 hle'
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain




/-- For primes `p, q ≥ 3`, `2·(p−1)(q−1) ≤ p²q−1`. -/
lemma crude_bound {p q : ℕ} (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) : 2 * (p - 1) * (q - 1) ≤ p ^ 2 * q - 1 := by
  have hpq_le : (p - 1) * (q - 1) ≤ p * q := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h2pq : 2 * (p * q) ≤ p ^ 2 * q - 1 := by
    have h1pq : 1 ≤ (p - 2) * (p * q) := by
      have hp2 : 1 ≤ p - 2 := by omega
      have hpqpos : 1 ≤ p * q := by
        have h9 : 9 ≤ p * q := Nat.mul_le_mul hp3 hq3
        omega
      have hmul : 1 * 1 ≤ (p - 2) * (p * q) := Nat.mul_le_mul hp2 hpqpos
      simpa using hmul
    have h'' : 1 ≤ p ^ 2 * q - 2 * (p * q) := by
      rw [Nat.mul_sub_right_distrib] at h1pq
      simpa [pow_two, Nat.mul_assoc] using h1pq
    have hgoal : 2 * (p * q) + 1 ≤ p ^ 2 * q := by omega
    omega
  calc
    2 * (p - 1) * (q - 1) = 2 * ((p - 1) * (q - 1)) := by ring
    _ ≤ 2 * (p * q) := Nat.mul_le_mul_left 2 hpq_le
    _ ≤ p ^ 2 * q - 1 := h2pq

/-- For primes `p, q ≥ 3`, `2·(p−1)(q−1) ≤ p·q²−1`. -/
lemma crude_bound' {p q : ℕ} (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) : 2 * (p - 1) * (q - 1) ≤ p * q ^ 2 - 1 := by
  have hpq_le : (p - 1) * (q - 1) ≤ p * q := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have h2pq : 2 * (p * q) ≤ p * q ^ 2 - 1 := by
    have h1pq : 1 ≤ (q - 2) * (p * q) := by
      have hq2 : 1 ≤ q - 2 := by omega
      have hpqpos : 1 ≤ p * q := by
        have h9 : 9 ≤ p * q := Nat.mul_le_mul hp3 hq3
        omega
      have hmul : 1 * 1 ≤ (q - 2) * (p * q) := Nat.mul_le_mul hq2 hpqpos
      simpa using hmul
    have h'' : 1 ≤ p * q ^ 2 - 2 * (p * q) := by
      rw [Nat.mul_sub_right_distrib] at h1pq
      simpa [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h1pq
    have hgoal : 2 * (p * q) + 1 ≤ p * q ^ 2 := by omega
    omega
  calc
    2 * (p - 1) * (q - 1) = 2 * ((p - 1) * (q - 1)) := by ring
    _ ≤ 2 * (p * q) := Nat.mul_le_mul_left 2 hpq_le
    _ ≤ p * q ^ 2 - 1 := h2pq

/-- For `n` with exactly two distinct prime factors, `|S(n)| ≤ (n−1)/4`. -/
lemma goodUnits_card_le_semiprime {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n)
    (hk : n.primeFactors.card = 2) :
    Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ (n - 1) / 4 := by
  rcases Finset.card_eq_two.mp hk with ⟨p, q, hpq_ne, hpq⟩
  have hp_mem : p ∈ n.primeFactors := by rw [hpq]; simp
  have hq_mem : q ∈ n.primeFactors := by rw [hpq]; simp
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hq : Nat.Prime q := Nat.prime_of_mem_primeFactors hq_mem
  have hp_ne2 : p ≠ 2 := by
    intro h2
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
    have hpodd : Odd p := odd_of_dvd_odd hn_odd hpdvd
    rw [h2] at hpodd
    norm_num at hpodd
  have hq_ne2 : q ≠ 2 := by
    intro h2
    have hqdvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
    have hqodd : Odd q := odd_of_dvd_odd hn_odd hqdvd
    rw [h2] at hqodd
    norm_num at hqodd
  have hne : n = p ^ (n.factorization p) * q ^ (n.factorization q) := by
    conv_lhs => rw [Nat.prod_pow_primeFactors_factorization (by omega : n ≠ 0)]
    exact prod_primeFactors_pair hpq hpq_ne (fun x : ℕ => x ^ (n.factorization x))
  let a := n.factorization p
  let b := n.factorization q
  have ha : 1 ≤ a := hp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp_mem)
  have hb : 1 ≤ b := hq.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hq_mem)
  have hp2le : 2 ≤ p := hp.two_le
  have hq2le : 2 ≤ q := hq.two_le
  have hp3 : 3 ≤ p := by omega
  have hq3 : 3 ≤ q := by omega
  by_cases hsq : a = 1 ∧ b = 1
  · have hnpq : n = p * q := by
      rw [hne]
      change p ^ a * q ^ b = p * q
      rw [hsq.1, hsq.2]
      simp
    let m := 2 ^ (nu n - 1) * (strongTestParams n).2
    have hmTorsion : Nat.card {x : (ZMod n)ˣ // x ^ m = 1} = m.gcd (p - 1) * m.gcd (q - 1) := by
      rw [mTorsion_eq_prod (n := n) (by omega : n ≠ 0) hn_odd]
      rw [prod_primeFactors_pair hpq hpq_ne (fun x : ℕ => m.gcd (Nat.totient (x ^ (n.factorization x))))]
      have hpm : m.Coprime p := by simpa [m] using mExp_coprime_prime (n := n) hn1 hn_odd hp_mem
      have hqm : m.Coprime q := by simpa [m] using mExp_coprime_prime (n := n) hn1 hn_odd hq_mem
      rw [gcd_totient_eq_gcd_prime hp (by omega : 0 < a) hpm, gcd_totient_eq_gcd_prime hq (by omega : 0 < b) hqm]
    have hS : Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ 2 * m.gcd (p - 1) * m.gcd (q - 1) := by
      unfold goodUnits
      calc
        Nat.card {x : (ZMod n)ˣ // x ∈ goodSet m} ≤ 2 * Nat.card {x : (ZMod n)ˣ // x ^ m = 1} :=
          goodSet_card_le (n := n) m
        _ = 2 * (m.gcd (p - 1) * m.gcd (q - 1)) := by rw [hmTorsion]
        _ = 2 * m.gcd (p - 1) * m.gcd (q - 1) := by ring
    have hb8 : 8 * m.gcd (p - 1) * m.gcd (q - 1) ≤ n - 1 := by
      have hb' := semiprime_gcd_bound (p := p) (q := q) hp hq hpq_ne hp_ne2 hq_ne2
      rw [← hnpq] at hb'
      simpa [m] using hb'
    have h4 : 4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ n - 1 := by
      calc
        4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ 4 * (2 * m.gcd (p - 1) * m.gcd (q - 1)) := by
          exact Nat.mul_le_mul_left 4 hS
        _ = 8 * m.gcd (p - 1) * m.gcd (q - 1) := by ring
        _ ≤ n - 1 := hb8
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by simpa [mul_comm] using h4)
  · have hnsq : 2 ≤ a ∨ 2 ≤ b := by omega
    have hS' : Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ 2 * ((p - 1) / 2) * ((q - 1) / 2) := by
      calc
        Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ 2 * ∏ x : n.primeFactors, ((x : ℕ) - 1) / 2 :=
          goodUnits_card_le_prodHalf (n := n) hn1 hn_odd
        _ = 2 * (((p - 1) / 2) * ((q - 1) / 2)) := by
          rw [prod_primeFactors_pair hpq hpq_ne (fun x : ℕ => (x - 1) / 2)]
        _ = 2 * ((p - 1) / 2) * ((q - 1) / 2) := by ring
    have h8 : 8 * ((p - 1) / 2) * ((q - 1) / 2) ≤ n - 1 := by
      have hp_even : 2 ∣ p - 1 := two_dvd_prime_sub_one_of_odd hp (by
        have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
        exact odd_of_dvd_odd hn_odd hpdvd)
      have hq_even : 2 ∣ q - 1 := two_dvd_prime_sub_one_of_odd hq (by
        have hqdvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
        exact odd_of_dvd_odd hn_odd hqdvd)
      have h8eq : 8 * ((p - 1) / 2) * ((q - 1) / 2) = 2 * (p - 1) * (q - 1) := by
        calc
          8 * ((p - 1) / 2) * ((q - 1) / 2) = 2 * (2 * ((p - 1) / 2)) * (2 * ((q - 1) / 2)) := by ring
          _ = 2 * (p - 1) * (q - 1) := by rw [Nat.mul_div_cancel' hp_even, Nat.mul_div_cancel' hq_even]
      rw [h8eq]
      rcases hnsq with ha2 | hb2
      · have hp2_n : p ^ 2 * q ≤ n := by
          rw [hne]
          have hp2a : p ^ 2 ≤ p ^ a := pow_le_pow_right₀ (by omega) ha2
          have hq1b : q ≤ q ^ b := le_self_pow (by omega) (by omega : b ≠ 0)
          exact Nat.mul_le_mul hp2a hq1b
        exact (crude_bound hp3 hq3).trans (by omega)
      · have hq2_n : p * q ^ 2 ≤ n := by
          rw [hne]
          have hp1a : p ≤ p ^ a := le_self_pow (by omega) (by omega : a ≠ 0)
          have hq2b : q ^ 2 ≤ q ^ b := pow_le_pow_right₀ (by omega) hb2
          exact Nat.mul_le_mul hp1a hq2b
        exact (crude_bound' hp3 hq3).trans (by omega)
    have h4 : 4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ n - 1 := by
      calc
        4 * Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ 4 * (2 * ((p - 1) / 2) * ((q - 1) / 2)) := by
          exact Nat.mul_le_mul_left 4 hS'
        _ = 8 * ((p - 1) / 2) * ((q - 1) / 2) := by ring
        _ ≤ n - 1 := h8
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr (by simpa [mul_comm] using h4)


/--
The good subgroup `S(n)` has size at most `(n−1)/4` for odd composite
`n` (Rabin–Monier).  The proof splits on the number `k` of distinct
prime factors: `k = 1` (prime power), `k = 2` (semiprime), and
`k ≥ 3`.
-/
theorem goodUnits_card_le {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n)
    (hn_comp : ¬ Nat.Prime n) :
    Nat.card {x : (ZMod n)ˣ // x ∈ goodUnits} ≤ (n - 1) / 4 := by
  have hcard : 1 ≤ n.primeFactors.card := by
    have hpos : 0 < n.primeFactors.card :=
      (Finset.card_pos).mpr ((Nat.nonempty_primeFactors).2 hn1)
    omega
  have hcases : n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 ∨
      3 ≤ n.primeFactors.card := by
    omega
  rcases hcases with h1 | h2 | h3
  · exact goodUnits_card_le_prime_power (n := n) hn1 hn_odd hn_comp h1
  · exact goodUnits_card_le_semiprime (n := n) hn1 hn_odd h2
  · exact goodUnits_card_le_of_ge_three (n := n) hn1 hn_odd h3

/--
**The Miller-Rabin error bound (Theorem 31.39; sharpened to `(n−1)/4` by
Rabin–Monier).**  For odd composite `n`, at most `(n−1)/4` of the bases in
`(Z/nZ)ˣ` are strong liars.
Every strong liar lies in the good subgroup `S(n)` (`liar_mem_goodSet`), and
`|S(n)| ≤ (n−1)/4` (`goodUnits_card_le`).
-/
theorem strongLiars_card_le {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n)
    (hn_comp : ¬ Nat.Prime n) :
    Nat.card {a : (ZMod n)ˣ // isStrongLiar a} ≤ (n - 1) / 4 := by
  have hle : Nat.card {a : (ZMod n)ˣ // isStrongLiar a} ≤
      Nat.card {a : (ZMod n)ˣ // a ∈ goodUnits} := by
    refine Nat.card_le_card_of_injective
      (fun a : {a : (ZMod n)ˣ // isStrongLiar a} => ⟨(a : (ZMod n)ˣ),
        liar_mem_goodSet (n := n) hn_odd hn1 a.2⟩) ?_
    intro a b h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  exact hle.trans (goodUnits_card_le (n := n) hn1 hn_odd hn_comp)

/-! ## Random-witness analysis (the MILLER-RABIN error bound) -/

/-- A strong pseudoprime base is coprime to the modulus. -/
theorem strongPseudoprime_coprime {n a : ℕ} (hn1 : 1 < n) (h : strongPseudoprime n a) :
    Nat.Coprime a n := by
  have hpow : a ^ (n - 1) ≡ 1 [MOD n] := strongPseudoprime_pow h
  have hmul : a * a ^ (n - 2) ≡ 1 [MOD n] := by
    have hn' : n - 1 = 1 + (n - 2) := by omega
    rw [hn'] at hpow
    rw [pow_add, pow_one] at hpow
    exact hpow
  exact Nat.coprime_of_mul_modEq_one (a ^ (n - 2)) hmul

/-- A natural strong liar lifts to a strong liar in the unit group. -/
theorem isStrongLiar_of_strongPseudoprime {n : ℕ} [NeZero n] {a : ℕ}
    (hcop : Nat.Coprime a n) (h : strongPseudoprime n a) :
    isStrongLiar (ZMod.unitOfCoprime a hcop) := by
  rw [isStrongLiar]
  rw [ZMod.coe_unitOfCoprime]
  unfold strongPseudoprime at h
  rcases h with h1 | ⟨i, hi⟩
  · left
    simpa [Nat.cast_pow] using
      (ZMod.natCast_eq_natCast_iff (a ^ (strongTestParams n).2) 1 n).mpr h1
  · right
    refine ⟨i, ?_⟩
    rw [← Nat.cast_pow]
    have hnat : ((a ^ (2 ^ (i : ℕ) * (strongTestParams n).2) : ℕ) : ZMod n) = ((n - 1 : ℕ) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff (a ^ (2 ^ (i : ℕ) * (strongTestParams n).2)) (n - 1) n).mpr hi
    rw [hnat]
    have hneg : ((n - 1 : ℕ) : ZMod n) = -1 := by
      have hnpos : 0 < n := NeZero.pos n
      rw [Nat.cast_sub (show 1 ≤ n by omega)]
      rw [ZMod.natCast_self]
      simp
    exact hneg

/--
**Random-witness count bound.**  For odd composite `n`, at most `(n-1)/4` of the
bases `1, …, n-1` are strong liars.  This is the sampling interpretation of the
Miller-Rabin error bound (Theorem 31.39).
-/
theorem strongLiars_nat_card_le {n : ℕ} [NeZero n] (hn1 : 1 < n) (hn_odd : Odd n)
    (hn_comp : ¬ Nat.Prime n) :
    Nat.card {a : Fin (n - 1) // strongPseudoprime n (a.val + 1)} ≤ (n - 1) / 4 := by
  let f : {a : Fin (n - 1) // strongPseudoprime n (a.val + 1)} →
      {u : (ZMod n)ˣ // isStrongLiar u} := fun a =>
    let hcop : Nat.Coprime (a.val.val + 1) n := strongPseudoprime_coprime hn1 a.2
    ⟨ZMod.unitOfCoprime (a.val.val + 1) hcop, isStrongLiar_of_strongPseudoprime hcop a.2⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have h : ZMod.unitOfCoprime (a.val.val + 1) (strongPseudoprime_coprime hn1 a.2) =
        ZMod.unitOfCoprime (b.val.val + 1) (strongPseudoprime_coprime hn1 b.2) := by
      change (f a).val = (f b).val
      exact congrArg Subtype.val hab
    have hcoef : ((ZMod.unitOfCoprime (a.val.val + 1) (strongPseudoprime_coprime hn1 a.2) : ZMod n)) =
        ((ZMod.unitOfCoprime (b.val.val + 1) (strongPseudoprime_coprime hn1 b.2) : ZMod n)) := by
      exact congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) h
    rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime] at hcoef
    have hmod : a.val.val + 1 ≡ b.val.val + 1 [MOD n] :=
      (ZMod.natCast_eq_natCast_iff (a.val.val + 1) (b.val.val + 1) n).mp hcoef
    have ha : a.val.val + 1 < n := by have := a.val.isLt; omega
    have hb : b.val.val + 1 < n := by have := b.val.isLt; omega
    rw [Nat.ModEq] at hmod
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
    omega
  calc
    Nat.card {a : Fin (n - 1) // strongPseudoprime n (a.val + 1)}
        ≤ Nat.card {u : (ZMod n)ˣ // isStrongLiar u} := Nat.card_le_card_of_injective f hfinj
    _ ≤ (n - 1) / 4 := strongLiars_card_le (n := n) hn1 hn_odd hn_comp

/--
**MILLER-RABIN (multi-base loop, CLRS §31.8).**  Run the single-base
{lit}`millerRabin` test over every base in `bases`, left to right.  The first
component is `true` exactly when every base reports "probably prime"; the
second component is the total number of modular multiplications charged by the
underlying repeated squarings ({lit}`modExpWithCount`).
-/
def millerRabinLoop (n : ℕ) : List ℕ → Bool × ℕ
| [] => (true, 0)
| a :: as =>
    let (pass, cost) := millerRabinLoop n as
    (millerRabin n a && pass, (modExpWithCount a n (n - 1)).2 + cost)

/-- **The loop reports "probably prime" exactly when every base passes**
(CLRS §31.8). -/
theorem millerRabinLoop_fst_iff (n : ℕ) (bases : List ℕ) :
    (millerRabinLoop n bases).1 = true ↔ ∀ a ∈ bases, millerRabin n a = true := by
  induction bases with
  | nil => simp [millerRabinLoop]
  | cons a as ih =>
      simp [millerRabinLoop, ih, Bool.and_eq_true, List.mem_cons]

/-- **The loop uses at most `2 · |bases| · Nat.size (n−1)` modular
multiplications** (CLRS §31.8). -/
theorem millerRabinLoop_count_le (n : ℕ) (bases : List ℕ) :
    (millerRabinLoop n bases).2 ≤ bases.length * (2 * Nat.size (n - 1)) := by
  induction bases with
  | nil => simp [millerRabinLoop]
  | cons a as ih =>
      simp [millerRabinLoop]
      have h := modExpWithCount_count_le a n (n - 1)
      calc
        (modExpWithCount a n (n - 1)).2 + (millerRabinLoop n as).2
            ≤ 2 * Nat.size (n - 1) + as.length * (2 * Nat.size (n - 1)) := Nat.add_le_add h ih
        _ = (as.length + 1) * (2 * Nat.size (n - 1)) := by ring

end Chapter31

end CLRS
