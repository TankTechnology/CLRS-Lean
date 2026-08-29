# Affine Coefficient/Direction Co-Design Certificate

**Date:** 2026-08-29

## Objective

Generalize the verified fixed coloring

```text
(i + M*j) mod K
```

to the parameterized family

```text
(alpha*i + beta*j + offset) mod K,
```

then lift the existing line and phase-aware strip load arguments to those
coefficients.  For a finite family of strip-defect scenarios, expose a
worst-case certificate and prove that a nonempty finite coefficient candidate
set contains an exact minimizer of that certificate.

This phase builds theorem-backed co-design infrastructure.  It does not claim
a closed-form global optimum under translated-window balance, a matching load
lower bound, or end-to-end DART repairability.

## Decomposition

Keep the proof surface in four focused modules:

1. `AffineColoring.lean` owns the parameterized coloring, directional step,
   exact period, periodicity/congruence theorems, and specialization to the
   existing `affineChainColor` construction.
2. `AffineLineDefectLoad.lean` owns finite line-prefix color sets and the
   coefficient-sensitive ceiling-period load theorem.
3. `AffineStripDefectLoad.lean` reuses `stripPoint`/`stripPoints`, defines
   colored physical strip points and the cross-row period, and proves the
   phase-aware product bound.
4. `AffineDirectionCodesign.lean` owns EDA-facing coefficient and defect-shape
   records, the closed-form strip certificate, finite-family worst-case score,
   actual-load bridge, and exact minimizer existence over a nonempty finite
   candidate set.

The existing fixed-color modules remain unchanged.  Specialization theorems
connect the new definitions to the trusted baseline instead of rewriting the
old API.

## Mathematical interface

For coefficients `alpha`, `beta`, offset `gamma`, modulus `K`, and direction
`v`, define

```text
affineGridColor alpha beta gamma K i j
  = (alpha*i + beta*j + gamma) mod K

affineDirectionStep alpha beta v
  = alpha*v.x + beta*v.y

affineLinePeriod alpha beta K v
  = K / gcd(K, affineDirectionStep alpha beta v).
```

For a strip with along direction `u` and cross direction `v`, write

```text
g = gcd(K, affineDirectionStep alpha beta u)
T = K / g
R = g / gcd(g, affineDirectionStep alpha beta v).
```

Under exactly `0 < K`, prove

```text
load(alpha,beta,gamma,K,shape,color)
  <= ceil(shape.width / R) * ceil(shape.length / T).
```

The load counts distinct physical bumps, so coincident samples are
deduplicated.  The theorem does not require `color < K`; an invalid color
selects no points.

## Co-design interface

Use an offset-free coefficient record because the additive offset changes
labels but not `T`, `R`, or any load certificate:

```lean
structure AffineCoefficients where
  alpha : Nat
  beta : Nat

structure StripDefectShape where
  width : Nat
  length : Nat
  along : Nat × Nat
  across : Nat × Nat
```

Define the shape certificate from `R` and `T`, and define a finite-family
score with `Finset.sup`.  Expose:

```lean
theorem affineStripColor_load_le_familyScore
    (K gamma c : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) (family : Finset StripDefectShape)
    (base : Nat × Nat) (hK : 0 < K) (hshape : shape ∈ family) :
    (affineStripColorPoints coeff.alpha coeff.beta gamma K
      shape.width shape.length c base shape.along shape.across).card ≤
        affineDefectFamilyScore K coeff family

theorem exists_affineCoefficients_minimizer
    (candidates : Finset AffineCoefficients)
    (hne : candidates.Nonempty) :
    ∃ coeff ∈ candidates, ∀ other ∈ candidates,
      affineDefectFamilyScore K coeff family ≤
        affineDefectFamilyScore K other family
```

The second theorem is exact over the explicitly supplied candidate universe.
Documentation must call it a certified finite-family synthesis interface, not
a non-enumerative characterization of every window-balanced affine coloring.

## Testing and trust contract

Each module gets a separate interface test.  Tests freeze full theorem
applications rather than only bare `#check` names, and include:

- specialization to `(alpha,beta,gamma) = (1,M,0)`;
- horizontal and vertical period regressions;
- a coefficient pair whose score differs by defect direction;
- empty and singleton defect families;
- degenerate/repeated physical samples;
- a concrete candidate set where the certified minimizer score is evaluated.

The trust audit adds the generalized strip theorem and the finite-candidate
minimizer theorem.  Completion requires focused module/interface checks, all
ThreeDIC interface/trust checks, full `lake build CLRSLean`, repository checks,
placeholder scan, and `git diff --check`.

## Claim boundary

Allowed:

- the load theorem is valid for arbitrary natural affine coefficients;
- the family score simultaneously upper-bounds every listed defect shape;
- a nonempty finite candidate set has an exact score minimizer;
- the old fixed coloring is a specialization of the general model.

Not allowed without later results:

- the selected coefficients preserve translated-window balance;
- the certificate is tight or optimal for actual physical failures;
- finite minimization is a new algorithmic open-problem solution;
- the score captures spare placement, mux reachability, routing congestion,
  delay, or DART repair success.
