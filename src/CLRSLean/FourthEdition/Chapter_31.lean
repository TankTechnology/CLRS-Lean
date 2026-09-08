import CLRSLean.Chapter_31
import CLRSLean.FourthEdition.Chapter_31.Section_31_1_Elementary_Number_Theory
import CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor
import CLRSLean.FourthEdition.Chapter_31.Section_31_3_Modular_Arithmetic
import CLRSLean.FourthEdition.Chapter_31.Section_31_4_Solving_Modular_Linear_Equations
import CLRSLean.FourthEdition.Chapter_31.Section_31_5_Chinese_Remainder_Theorem
import CLRSLean.FourthEdition.Chapter_31.Section_31_6_Powers_Of_An_Element
import CLRSLean.FourthEdition.Chapter_31.Section_31_7_RSA
import CLRSLean.FourthEdition.Chapter_31.Section_31_8_Primality_Testing

import CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor.Execution
import CLRSLean.FourthEdition.Chapter_31.Section_31_7_RSA.KeyRoundTrip
import CLRSLean.FourthEdition.Chapter_31.Section_31_8_Primality_Testing.Probability

/-!
# Chapter 31 — Number-Theoretic Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 31.1--31.8 are native fourth-edition sections (elementary
number-theoretic notions, the greatest common divisor, modular arithmetic,
solving modular linear equations, the Chinese remainder theorem, powers of
an element, the RSA public-key cryptosystem, and primality testing),
imported directly under [Chapter 31](CLRSLean/FourthEdition/Chapter_31/).
The integer-factorization development (legacy Section 31.9) is retained as
supplementary online material (reachable through
{lit}`CLRSLean.OnlineMaterial`).
Declarations keep their current namespaces; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_31` and
{lit}`CLRSLean.Chapter_31.Section_31_*` forward to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Elementary Number-Theoretic Notions](CLRSLean/FourthEdition/Chapter_31/Section_31_1_Elementary_Number_Theory/)
* [Greatest Common Divisor](CLRSLean/FourthEdition/Chapter_31/Section_31_2_Greatest_Common_Divisor/)
* [Modular Arithmetic](CLRSLean/FourthEdition/Chapter_31/Section_31_3_Modular_Arithmetic/)
* [Solving Modular Linear Equations](CLRSLean/FourthEdition/Chapter_31/Section_31_4_Solving_Modular_Linear_Equations/)
* [The Chinese Remainder Theorem](CLRSLean/FourthEdition/Chapter_31/Section_31_5_Chinese_Remainder_Theorem/)
* [Powers of an Element](CLRSLean/FourthEdition/Chapter_31/Section_31_6_Powers_Of_An_Element/)
* [The RSA Public-Key Cryptosystem](CLRSLean/FourthEdition/Chapter_31/Section_31_7_RSA/)
* [Primality Testing](CLRSLean/FourthEdition/Chapter_31/Section_31_8_Primality_Testing/)

## Coverage boundary

The native sections supply the represented fourth-edition number-theoretic
sections (§31.1--31.8), including the executable cost layers:
{lit}`CLRS.Chapter31.modularLinearEquationSolver` (§31.4),
{lit}`CLRS.Chapter31.modExpWithCount` (§31.6),
{lit}`CLRS.Chapter31.rsaKeyGen` and
{lit}`CLRS.Chapter31.rsaEncrypt`/{lit}`CLRS.Chapter31.rsaDecrypt` (§31.7), and
{lit}`CLRS.Chapter31.MillerRabinExecution.run` (§31.8).  §31.1 also carries the
least-common-multiple layer ({lit}`CLRS.Chapter31.gcd_mul_lcm_eq`,
{lit}`CLRS.Chapter31.lcm_eq_mul_of_coprime`), and §31.5 packages the Chinese
remainder theorem as the ring isomorphism
{lit}`CLRS.Chapter31.zmod_chineseRemainder`.

The counted Euclid companion refines the public first-argument recursion and
proves that its actual division count is {lit}`euclidDivisions b a` for the call
{lit}`euclid a b`. Generated RSA keys from supplied distinct primes round-trip
all messages modulo the generated modulus; in-range messages recover exactly.
No key-prime generation or RSA key-assembly runtime is claimed.

Miller–Rabin now decides from the residues of the same counted exponentiation
and squaring execution. It stops at the first rejecting base and uses at most
{lit}`3 * bases.length * Nat.size (n - 1)` modular multiplications. Parameter
decomposition, comparisons, supplied-base sampling and bit runtime are outside
that counter. The legacy loop retains its detached exponentiation budget.
The finite product sample space proves actual executed false acceptance is at
most {lit}`(1 / 4)^rounds` for odd composite inputs greater than one, under
independent uniform sampling with replacement from residues {lit}`1,...,n-1`.
The Carmichael theorem for 561 establishes membership, not minimality.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
