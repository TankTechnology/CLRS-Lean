# CLRS Chapter 5 — Probabilistic Analysis: Design Spec

Date: 2026-06-24
Status: ready for implementation

## Content

Chapter 5 introduces probability for algorithm analysis.  We formalize
the core probabilistic framework and the hiring problem.

### Section 5.1: Indicator Random Variables + Hiring Problem

**Definitions:**
- Indicator random variable `I{A}` for event A
- Expectation of indicator: `E[I{A}] = Pr{A}`
- Linearity of expectation (from mathlib `ProbabilityTheory`)

**Hiring Problem:**
- n candidates in random order (uniform over n! permutations)
- Hire candidate i iff they are the best among first i
- `Pr{candidate i hired} = 1/i`
- Expected hires = Σ 1/i = H_n (n-th harmonic number)
- Asymptotics: `E[hires] = ln n + O(1)`

### Section 5.2: Randomized Hiring

- Randomized algorithm: permute list before interviewing
- Same expected hires as random-order analysis
- Cost analysis with interviewing vs hiring costs

## Files

```
CLRSLean/Chapter_05.lean
CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean   (indicator vars + hiring)
```

## Key mathlib dependencies

- `Mathlib.ProbabilityTheory` — `ℙ`, `𝔼`, indicator, linearity
- `Mathlib.Probability.UniformOn` — uniform distribution

## Implementation notes

- Work over a finite type `Fin n` for n candidates
- `Finset` for events
- `ProbabilityTheory.expect` for expectation
- Harmonic numbers: use `∑ i : range n, 1/(i+1)` or mathlib's harmonic

## What's in scope

- Indicator variable definition and `E[I_A] = P(A)`
- Hiring problem: expected hires = H_n proof
- Asymptotic bound: H_n = Θ(log n)

## What's out of scope (for now)

- Full measure-theoretic probability (use mathlib's discrete PMF)
- Birthday paradox (Section 5.4)
- Balls and bins (Section 5.4)
- Streaks analysis (Section 5.4)
