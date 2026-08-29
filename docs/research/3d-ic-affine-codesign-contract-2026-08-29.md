# Research Contract: Affine Coefficient/Direction Co-Design

Date: 2026-08-29

## Phenomenon

- **Phenomenon:** affine color coefficients change modular periods along and
  across a prescribed strip-defect direction, which changes a certified
  worst-case per-color load bound.
- **Why it matters:** the fixed mixed-radix coloring is locally balanced, but
  an EDA flow must also account for likely line and strip orientations.
- **Falsifier:** if all admissible coefficients have the same family score, or
  the score fails to correlate with a faithful repair model, coefficient
  co-design has no practical benefit in that model.

## Unit and universe

- **Primary unit:** one finite `StripDefectShape` with width, length, along
  direction, and cross direction.
- **Formal universe:** finite `Finset` families of such shapes and all natural
  coefficient pairs, quotiented without loss for the score objective to the
  finite canonical residue domain `range K x range K` when `0 < K`.
- **Load denominator:** distinct physical bumps assigned one requested color;
  repeated samples are counted once.
- **Excluded:** arbitrary connected clusters, probabilistic fault samples,
  spare/mux constraints, routing cost, and empirical repair outcomes.

## Terms

| Term | Definition | Do not confuse with |
|---|---|---|
| actual load | cardinality of distinct sampled physical points of one color | sample-index count |
| shape certificate | `ceil(W/R) * ceil(L/T)` | an exact load formula |
| family score | maximum shape certificate over a finite family | observed repair failure rate |
| minimizer | least family score inside candidates, or globally for the frozen score after residue reduction | optimum under window-balance or hardware constraints |

## Evidence map

| Question | Evidence | Allowed claim |
|---|---|---|
| Does the general affine strip obey the period certificate? | Lean generalized strip theorem | deterministic upper bound under `0 < K` |
| Does one score cover a listed defect family? | Lean `Finset.sup` bridge | simultaneous upper certificate for family members |
| Can coefficients be selected exactly from candidates? | Lean finite minimizer theorem | exact minimum inside the supplied nonempty set |
| Can the natural coefficient universe be reduced structurally? | Lean residue-invariance and canonical-domain minimizer theorems | global optimum for the frozen family-score objective over all natural coefficient pairs |
| Can score minimization retain exact translated-window balance? | Lean `affineGridColor_window_count_eq_of_coprime_coefficient` and `exists_balancedAffineCoefficients_minimizer` | exact constrained minimum for `K ∣ M` inside the coprime-coordinate sufficient family |
| Is the selection better in DART? | no evidence in this phase | no claim |

## Claim ledger

| Claim | Status | Evidence | Caveat | Forbidden wording |
|---|---|---|---|---|
| arbitrary coefficients admit line/strip upper certificates | verified | kernel-checked theorems | natural nonnegative lattice model | “tight” |
| family score bounds every member | verified | load-to-`Finset.sup` theorem | only explicitly listed shapes | “all cluster faults” |
| a candidate minimizer exists | verified | finite-order theorem | candidate-relative | “solves global co-design” |
| the canonical residue domain contains a global score minimizer | verified | residue-invariance plus finite minimization | only the frozen upper-certificate objective | “globally optimal repair coloring” |
| the coprime-coordinate candidate family preserves exact window balance when `K ∣ M` | verified | kernel-checked window-count and constrained-minimizer theorems | sufficient family, not a full classification | “every score minimizer is balanced” |
| certificates predict repairability | unsupported | no simulator bridge | requires DART evaluation | “guarantees repair” |

## Open risks

- The unconstrained canonical score minimizer may still destroy local
  translated-window balance; only the new filtered candidate minimizer carries
  the balance certificate.
- The upper certificate may be loose without a matching lower-bound theorem.
- The structural residue reduction and filtered minimizer close one sufficient
  constrained family, but a complete admissibility classification or a bound
  against the unconstrained optimum remains open.
- Physical routing and repair semantics may dominate the modular load score.
