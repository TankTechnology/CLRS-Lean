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
- **Formal universe:** finite `Finset` families of such shapes and finite
  nonempty `Finset` sets of natural coefficient pairs.
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
| minimizer | least family score inside an explicit finite candidate set | global optimum under all hardware constraints |

## Evidence map

| Question | Evidence | Allowed claim |
|---|---|---|
| Does the general affine strip obey the period certificate? | Lean generalized strip theorem | deterministic upper bound under `0 < K` |
| Does one score cover a listed defect family? | Lean `Finset.sup` bridge | simultaneous upper certificate for family members |
| Can coefficients be selected exactly from candidates? | Lean finite minimizer theorem | exact minimum inside the supplied nonempty set |
| Can the natural coefficient universe be reduced structurally? | Lean residue-invariance and canonical-domain minimizer theorems | global optimum for the frozen family-score objective over all natural coefficient pairs |
| Is the selection better in DART? | no evidence in this phase | no claim |

## Claim ledger

| Claim | Status | Evidence | Caveat | Forbidden wording |
|---|---|---|---|---|
| arbitrary coefficients admit line/strip upper certificates | target | kernel-checked theorems | natural nonnegative lattice model | “tight” |
| family score bounds every member | target | load-to-`Finset.sup` theorem | only explicitly listed shapes | “all cluster faults” |
| a candidate minimizer exists | target | finite-order theorem | candidate-relative | “solves global co-design” |
| the canonical residue domain contains a global score minimizer | target | residue-invariance plus finite minimization | only the frozen upper-certificate objective | “globally optimal repair coloring” |
| coefficients preserve window balance | unsupported | none in this phase | requires a feasible-family theorem | “balance-preserving optimizer” |
| certificates predict repairability | unsupported | no simulator bridge | requires DART evaluation | “guarantees repair” |

## Open risks

- A useful coefficient may reduce directional load while destroying local
  translated-window balance.
- The upper certificate may be loose without a matching lower-bound theorem.
- Finite candidate minimization is infrastructure, not by itself research
  novelty; a structural admissibility or approximation theorem remains needed.
- Physical routing and repair semantics may dominate the modular load score.
