# Chapter 31 repair evidence — issue #373

The audited execution and probability gaps are repaired in companions imported
by both chapter guides. Existing public functions and their theorem signatures
remain available. The legacy Miller–Rabin counter is now explicitly described
as a detached exponentiation budget.

## Actual Miller–Rabin execution

`Section_31_8_Primality_Testing/Execution.lean` defines
`CLRS.Chapter31.MillerRabinExecution.trial` and `run`.
The initial residue comes from `modExpWithCount a n d`; the decision inspects
that returned residue and the actual subsequent modular squares. No Boolean
is obtained by deciding the old strong-pseudoprime predicate inside this
execution. A rejected base stops the multi-base loop before its suffix.

- `trial_spec` identifies the result with `strongPseudoprime`.
- `trial_prime` transfers the existing prime/coprime-base theorem.
- `squareSearch_reject_count` proves a rejected square scan performs exactly
  its remaining square allowance.
- `run_spec` identifies acceptance with all supplied bases passing.
- `run_reject` preserves the head count and omits the suffix completely.
- `run_count_le` bounds the returned modular-multiplication count by
  `bases.length * (3 * Nat.size (n - 1))`.
- `run_eq_legacy_value` preserves the old multi-base Boolean semantics.

The counter counts modular multiplications, not total or bit runtime.
Parameter decomposition, comparisons, supplied-base construction and sampling
are excluded. The kernel preserves the old strong-probable-prime predicate;
primality interpretations retain their admissible-input hypotheses.

## Repeated-trial probability

`Section_31_8_Primality_Testing/Probability.lean` uses the explicit finite
product `Samples n rounds = Fin rounds → Fin (n - 1)`. Each coordinate denotes
a base in `1,...,n-1`, sampled uniformly and independently with replacement.
`Accepted` is defined by the actual `run` Boolean.

`acceptedEquiv` gives a coordinatewise bijection to functions into the
strong-liar subtype. Consequently `accepted_card` is the one-base liar count
to the power `rounds`, and `samples_card` is `(n - 1)^rounds`.
`uniformError` is their rational ratio. For odd composite `n > 1`,
`uniform_error_le` proves `uniformError n rounds ≤ (1/4)^rounds` using the
existing natural-residue one-base bound. `uniformError_zero` is exactly one.
This is a finite probability model, not a random generator or sampling-cost proof.

## Euclid, RSA, and scope corrections

`Section_31_2_Greatest_Common_Divisor/Execution.lean` follows the actual public
first-argument Euclid recursion and increments its counter on each division.
`euclidWithCount_spec` proves
`euclidWithCount a b = (euclid a b, euclidDivisions b a)`.
Thus the public call `(8,3)` has four divisions, while `(3,8)` has three.

`Section_31_7_RSA/KeyRoundTrip.lean` proves `rsaKeyGen_roundTrip_mod` for every
message and `rsaKeyGen_roundTrip` for messages below the generated modulus.
The hypotheses are supplied distinct primes and a public exponent coprime to
their totient product. The wrapper derives positivity of the exponent product
and applies the general-message RSA theorem, including messages sharing a
factor with the modulus. It does not claim prime generation, key-assembly
runtime, or security.

Native and guide comments now state that `isCarmichael_561` proves membership,
without claiming minimality. The canonical and legacy guides, the three
relevant edition-map rows, the Chapter 31 progress row, and Trust/Chapter_31
include the repaired interfaces and cost boundaries. All non-Chapter-31 CSV
lines were preserved byte-for-byte during the update.

## Regression and trust coverage

The intended Miller–Rabin interfaces first failed as missing names in the
focused test. Final tests cover counted square scans, prime 17/base 3
`(true,5)`, composite 21/base 2 `(false,6)`, the genuine strong liar
2047/base 2 `(true,20)`, and rejection of `[2,3,5]` with only six charged
multiplications. Compiled `#guard` checks exercise the actual numeric code;
public theorem assertions remain kernel checked without native-decision axioms.

For `n=9`, kernel-checked finite counts give two liars among eight nonzero
bases, four accepting pairs among 64 samples, and exact probability `1/16`.
The second focused test covers the swapped Euclid counts, zero arguments,
RSA recovery of a noncoprime message, and arbitrary-message modular recovery.
Trust assertions cover every new headline correctness, count, and probability
theorem. No `sorry`, `admit`, or custom axiom was added.

## Verified commands

All commands below completed with exit status zero on the integrated sources:

```text
lake build CLRSLean.FourthEdition.Chapter_31
lake env lean tests/Chapter_31_MillerRabinExecution.lean
lake env lean tests/Chapter_31_NumberTheoryBridges.lean
lake env lean tests/Trust/Chapter_31.lean
lake env lean tests/Chapter_31_Interface.lean
lake env lean tests/FourthEdition_Chapter_31_Interface.lean
python3 scripts/check_repository.py
```

The targeted chapter build completed 8603 jobs. Existing documentation warnings
remain; there were no proof errors. The scoped `git diff --check` passed, and
new source files were also checked for trailing whitespace. Repository checks
passed the placeholder policy and Markdown-link checks. The repaired headline
theorems pass the repository axiom assertions. This evidence concerns the
listed source contracts, not a fresh line-by-line textbook audit.
