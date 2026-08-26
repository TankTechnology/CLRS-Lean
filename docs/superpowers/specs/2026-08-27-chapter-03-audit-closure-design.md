# Chapter 3 audit-closure design

## Goal

Close GitHub issue #316 through independently verifiable Lean milestones while
keeping the large Chapter 3 developments split into small modules.

## Module structure

- `Section_03_1_Asymptotic_Notation/Core.lean`: existing discrete asymptotic
  wrappers and algebra.
- `Section_03_1_Asymptotic_Notation/CLRSBridge.lean`: textbook nonnegative and
  strict-inequality witness forms, little-o/little-omega transitivity, and
  real-domain wrappers.
- `Section_03_2_Standard_Functions/TextbookIdentities.lean`: explicit
  floor/ceiling, remainder, powers, exponential, logarithm, factorial,
  iteration, and Fibonacci restatements.
- Later focused modules for polynomial and real-exponent growth results if
  those arguments need substantial proof infrastructure.

The existing section filenames remain facades, so downstream imports do not
change.

## Semantic choices

- The existing absolute-value definitions remain canonical because they are
  robust for signed functions.
- CLRS-style witnesses are proved equivalent under explicit eventual
  nonnegativity (and eventual positivity where a strict little-o conclusion
  needs it). No equivalence is claimed without the necessary hypotheses.
- Cost or executable claims are not introduced in Chapter 3.
- Thin restatements of Mathlib identities are acceptable when they create a
  stable CLRS-facing theorem name; substantive asymptotic claims retain local
  proofs and enter the native axiom audit.

## Verification

Each milestone must compile its focused module and public interface test.
Before integration, both Chapter 3 roots, the Chapter 3 trust gate, and the
repository checks must pass.
