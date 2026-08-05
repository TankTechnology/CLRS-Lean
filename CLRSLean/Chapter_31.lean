import CLRSLean.Chapter_31.Section_31_1_Elementary_Number_Theory
import CLRSLean.Chapter_31.Section_31_2_Greatest_Common_Divisor

/-! # Chapter 31 — Number-Theoretic Algorithms

Chapter 31 of CLRS covers algorithms for number theory: divisibility, the
greatest common divisor, modular arithmetic, primality testing, and
cryptography.  This chapter currently formalizes Sections 31.1 (elementary
notions) and 31.2 (greatest common divisor) with the division theorem,
Bezout's identity, and the EUCLID / EXTENDED-EUCLID algorithms.

## Sections

### 31.1 Elementary Number-Theoretic Notions

* {lit}`CLRS.Chapter31.division_theorem` (Theorem 31.1) — division with a
  unique quotient and remainder.
* {lit}`CLRS.Chapter31.IsGCD` / {lit}`CLRS.Chapter31.nat_gcd_isGCD` — the
  greatest-common-divisor property and its agreement with `Nat.gcd`.
* {lit}`CLRS.Chapter31.divides_refl` … {lit}`CLRS.Chapter31.divides_sub`
  (Lemma 31.1) — the basic divisibility facts.
* {lit}`CLRS.Chapter31.coprime_iff_gcd_eq_one`,
  {lit}`CLRS.Chapter31.prime_def_gt_one`, and
  {lit}`CLRS.Chapter31.exists_prime_ge` (Euclid's theorem).

### 31.2 Greatest Common Divisor

* {lit}`CLRS.Chapter31.euclid_recursion` (Lemma 31.2) — the Euclid recursion.
* {lit}`CLRS.Chapter31.euclid` + {lit}`CLRS.Chapter31.euclid_eq_gcd` — the
  EUCLID algorithm and its correctness.
* {lit}`CLRS.Chapter31.gcd_is_linear_combination` (Lemma 31.3, Bezout) and
  {lit}`CLRS.Chapter31.gcd_is_smallest_positive_linear_combination`
  (Theorem 31.2).
* {lit}`CLRS.Chapter31.gcd_dvd_linear_combination` (Corollary 31.3) and the
  Corollary 31.4 coprime characterizations.
* {lit}`CLRS.Chapter31.extendedEuclid` + {lit}`CLRS.Chapter31.extendedEuclid_spec`
  — EXTENDED-EUCLID.

**Status: `selected-section-complete`** — Sections 31.1 and 31.2 fully proved.

## Deferred Work

* 31.2 running-time (Lamé / Fibonacci) analysis of EUCLID.
* 31.3–31.9 modular arithmetic, solving modular linear equations, the
  Chinese remainder theorem, powers / RSA, primality testing, and integer
  factorization.
-/

namespace CLRS

namespace Chapter31

end Chapter31

end CLRS
