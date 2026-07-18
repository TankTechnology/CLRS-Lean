import CLRSLean.Chapter_31.Section_31_8_9_Primality_Factoring

/-!
# Chapter 31 — Number-Theoretic Algorithms

Chapter 31 of CLRS covers number-theoretic algorithms: elementary number
theory, greatest common divisor, modular arithmetic, solving modular
linear equations, the Chinese remainder theorem, powers of an element,
the RSA cryptosystem, primality testing, and integer factorization.

This formalization currently covers:

* **31.8–31.9 Primality Testing and Integer Factorization** — fast modular
  exponentiation via repeated squaring, the Miller-Rabin primality test with
  its witness concept, and Pollard's rho factorization heuristic.

## Sections

* **31.8–31.9 Primality Testing and Integer Factorization.**
  Main definitions:
  `CLRS.Chapter31.modularExponentiation`,
  `CLRS.Chapter31.factorOutTwos`,
  `CLRS.Chapter31.IsStrongLiar`,
  `CLRS.Chapter31.IsMRWitness`,
  `CLRS.Chapter31.millerRabinTest`,
  `CLRS.Chapter31.pollardRhoF`,
  `CLRS.Chapter31.pollardRho`.

  Main theorems:
  `CLRS.Chapter31.modularExponentiation_spec`,
  `CLRS.Chapter31.prime_implies_no_witnesses`,
  `CLRS.Chapter31.miller_rabin_error_bound`,
  `CLRS.Chapter31.millerRabinTest_soundness`,
  `CLRS.Chapter31.pollardRho_factor_divides`.

## Future work

* 31.1–31.2 Elementary number theory and GCD (Euclid's algorithm).
* 31.3–31.4 Modular arithmetic and solving modular linear equations.
* 31.5 The Chinese remainder theorem.
* 31.6 Powers of an element.
* 31.7 The RSA public-key cryptosystem.
* Full proofs of the Miller-Rabin ≤ 1/4 error bound (currently `sorry`).
* Expected-runtime analysis of Pollard's rho (currently `sorry`).

-/

namespace CLRS
namespace Chapter31

end Chapter31
end CLRS
