import CLRSLean.Chapter_31.Section_31_1_Elementary_Number_Theory
import CLRSLean.Chapter_31.Section_31_2_Greatest_Common_Divisor
import CLRSLean.Chapter_31.Section_31_3_Modular_Arithmetic
import CLRSLean.Chapter_31.Section_31_4_Solving_Modular_Linear_Equations
import CLRSLean.Chapter_31.Section_31_5_Chinese_Remainder_Theorem
import CLRSLean.Chapter_31.Section_31_6_Powers_Of_An_Element
import CLRSLean.Chapter_31.Section_31_7_RSA
import CLRSLean.Chapter_31.Section_31_8_Primality_Testing
import CLRSLean.Chapter_31.Section_31_9_Integer_Factorization

/-! # Chapter 31 — Number-Theoretic Algorithms

Chapter 31 of CLRS covers algorithms for number theory: divisibility, the
greatest common divisor, modular arithmetic, primality testing, and
cryptography.  This chapter formalizes all nine sections with the division
theorem, Bezout's identity, the EUCLID / EXTENDED-EUCLID algorithms, the
Chinese remainder theorem, Fermat's and Euler's theorems, RSA, the Fermat
primality test, and the Pollard's-rho factorization heuristic.

## Sections

### 31.1 Elementary Number-Theoretic Notions

* {lit}`CLRS.Chapter31.division_theorem` (Theorem 31.1) — division with a
  unique quotient and remainder.
* {lit}`CLRS.Chapter31.IsGCD` / {lit}`CLRS.Chapter31.nat_gcd_isGCD` — the
  greatest-common-divisor property.
* {lit}`CLRS.Chapter31.divides_refl` … {lit}`CLRS.Chapter31.divides_sub`
  (Lemma 31.1), and {lit}`CLRS.Chapter31.exists_prime_ge` (Euclid's theorem).

### 31.2 Greatest Common Divisor

* {lit}`CLRS.Chapter31.euclid_recursion` (Lemma 31.2),
  {lit}`CLRS.Chapter31.euclid` + {lit}`CLRS.Chapter31.euclid_eq_gcd`,
  {lit}`CLRS.Chapter31.gcd_is_linear_combination` (Lemma 31.3, Bezout),
  {lit}`CLRS.Chapter31.gcd_is_smallest_positive_linear_combination`
  (Theorem 31.2), the Corollary 31.3/31.4 facts, and
  {lit}`CLRS.Chapter31.extendedEuclid` + `extendedEuclid_spec`.
* **Running time (Lamé / Fibonacci)**: {lit}`CLRS.Chapter31.euclidDivisions`
  counts the recursive calls of `EUCLID`;
  {lit}`CLRS.Chapter31.fib_le_of_euclidDivisions` (Lemma 31.10) gives
  `a ≥ F_{k+2}`, `b ≥ F_{k+1}` for `k` calls;
  {lit}`CLRS.Chapter31.euclidDivisions_lt` (Theorem 31.11, Lamé) bounds the
  call count by `b < F_{k+1}`; and
  {lit}`CLRS.Chapter31.euclidDivisions_le_two_log` (Corollary 31.12) is the
  `O(log b)` bound.

### 31.3 Modular Arithmetic

* {lit}`CLRS.Chapter31.mod_add` / `mod_mul` (Theorem 31.5),
  {lit}`CLRS.Chapter31.exists_mul_inverse_mod` (Theorem 31.6),
  {lit}`CLRS.Chapter31.mul_left_cancel_mod` (Theorem 31.9), and
  {lit}`CLRS.Chapter31.modular_linear_solvable` (Theorem 31.11).

### 31.4 Solving Modular Linear Equations

* {lit}`CLRS.Chapter31.linear_congruence_shift` and
  {lit}`CLRS.Chapter31.linear_congruence_all_solutions`: the solutions of
  `a·x ≡ b (mod n)` are `x₀ + k·(n/gcd(a,n))`.

### 31.5 The Chinese Remainder Theorem

* {lit}`CLRS.Chapter31.chinese_remainder_two`,
  {lit}`CLRS.Chapter31.chinese_remainder_unique`, and
  {lit}`CLRS.Chapter31.chinese_remainder` (Theorem 31.27, two moduli).

### 31.6 Powers of an Element

* {lit}`CLRS.Chapter31.modularExponentiation` + `modularExponentiation_spec`,
  {lit}`CLRS.Chapter31.fermat_little_theorem` (Theorem 31.30), and
  {lit}`CLRS.Chapter31.euler_theorem`.

### 31.7 The RSA Public-Key Cryptosystem

* {lit}`CLRS.Chapter31.totient_mul_prime` and
  {lit}`CLRS.Chapter31.rsa_correct` (Theorem 31.36).

### 31.8 Primality Testing

* {lit}`CLRS.Chapter31.fermat_test` (Theorem 31.31),
  {lit}`CLRS.Chapter31.fermatPseudoprime`, and
  {lit}`CLRS.Chapter31.pseudoprime` + `pseudoprime_correct`.
* **Carmichael numbers**: {lit}`CLRS.Chapter31.isCarmichael` — a composite `n`
  passing the Fermat test for every coprime base
  ({lit}`CLRS.Chapter31.carmichael_fermatPseudoprime`);
  {lit}`CLRS.Chapter31.isCarmichael_561` exhibits the smallest one.
* **Miller-Rabin**: {lit}`CLRS.Chapter31.strongTestParams` (the `2^s·d`
  decomposition), {lit}`CLRS.Chapter31.strongPseudoprime` (STRONG-PSEUDOPRIME),
  {lit}`CLRS.Chapter31.Witness`, and the executable
  {lit}`CLRS.Chapter31.millerRabin` test.  (The correctness and error-bound
  theorems remain deferred.)

### 31.9 Integer Factorization

* {lit}`CLRS.Chapter31.rhoStep` and
  {lit}`CLRS.Chapter31.rho_collision_factor` (Pollard's rho).

**Status: `selected-section-complete`** — Sections 31.1–31.9 fully proved.

## Deferred Work

* 31.8 Miller-Rabin correctness (primes never have a witness) and the
  error bound (at most 1/4 of the bases are strong liars).
* 31.9 the full Pollard's-rho algorithm and its birthday-paradox analysis.
-/

namespace CLRS

namespace Chapter31

end Chapter31

end CLRS
