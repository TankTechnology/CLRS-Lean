import CLRSLean.Chapter_35.Section_35_1_3_Approximation_Algorithms
import CLRSLean.Chapter_35.Section_35_4_5_Randomized_Approximation

/-!
# Chapter 35 — Approximation Algorithms

Chapter 35 of CLRS studies algorithms that efficiently find
*approximately optimal* solutions to NP-hard optimization problems.
When the exact optimum is expensive to compute (assuming P ≠ NP),
approximation algorithms provide a polynomial-time alternative with
provable worst-case guarantees.

This chapter formalizes the classic approximation algorithms and
their ratio bounds.

## Sections

* §35.1–35.3 — Deterministic Approximation:
  * {lit}`CLRS.Chapter35.approxVertexCover` — APPROX-VERTEX-COVER,
    2-approximation (Theorem 35.1)
  * {lit}`CLRS.Chapter35.approxTSPTour` — APPROX-TSP-TOUR,
    2-approximation under the triangle inequality (Theorem 35.2)
  * {lit}`CLRS.Chapter35.greedySetCover` — GREEDY-SET-COVER,
    Hₙ-approximation (Theorem 35.4)

* §35.4–35.5 — Randomized and Fully Polynomial Approximation:
  * MAX-3-CNF randomized rounding — expected 7/8-approximation
    (Theorem 35.6)
  * SUBSET-SUM FPTAS — relative error ≤ ε in time poly(n, 1/ε)
    (Theorem 35.8)

## Key Concepts

* **Approximation ratio** ρ(n): for minimization, cost(solution) ≤ ρ · OPT;
  for maximization, value(solution) ≥ OPT / ρ.
* **FPTAS** (Fully Polynomial-Time Approximation Scheme): works for every
  ε > 0, runs in time poly(input-size, 1/ε).
* **Randomized rounding**: solve an LP relaxation, then flip biased
  coins to obtain an integer solution whose expected quality is within
  a constant factor of optimal.

## Current State

The definition layer is complete: algorithm signatures, correctness
predicates, and theorem statements.  Approximation-ratio proofs are
deferred (`sorry`).

### Completed

* {lit}`approxVertexCover` — algorithm defined, correctness predicate
  formalized
* {lit}`greedySetCover` — algorithm signature and cost model
* {lit}`approxTSPTour` — algorithm signature, triangle-inequality
  captured in `TSPInstance`
* MAX-3-CNF randomized rounding — problem formalized, expectation
  bound statement
* SUBSET-SUM FPTAS — problem formalized, relative-error theorem
  statement

### Pending

* Proof of Theorem 35.1 (vertex-cover 2-approximation):
  matching lower-bound argument.
* Proof of Theorem 35.2 (TSP 2-approximation): MST ≤ OPT lemma
  and shortcutting argument.
* Proof of Theorem 35.4 (set-cover Hₙ): charging-scheme analysis.
* Proof of Theorem 35.6 (MAX-3-CNF randomized rounding): LP
  relaxation bound and expected-fraction calculation.
* Proof of Theorem 35.8 (SUBSET-SUM FPTAS): trimming-invariant
  and error-bound analysis.
* Concrete implementations of MST construction and trimming.

## Connection to Chapter 34

The problems studied here — VERTEX-COVER, TSP (with triangle inequality),
SET-COVER, MAX-3-CNF, SUBSET-SUM — are all NP-hard (or NP-hard in their
decision versions).  Their decision variants are formalized in
Chapter 34.  This chapter shows that, despite NP-hardness,
near-optimal solutions can be found efficiently.

## References

* CLRS 4th Edition, Chapter 35
* Vazirani, *Approximation Algorithms*, Springer 2001
* Williamson & Shmoys, *The Design of Approximation Algorithms*,
  Cambridge 2011
-/

namespace CLRS
namespace Chapter35

end Chapter35
end CLRS
