# Phase-Aware Strip-Defect Load Design

**Date:** 2026-08-29

## Objective

Extend the verified affine repair-chain model from one lattice-line prefix to
a finite width-`W`, length-`L` strip of parallel lattice lines.  The first
checkpoint proves the honest compositional load bound obtained from the
existing line theorem.  The headline theorem then exploits cross-line color
phase to replace the factor `W` by a second ceiling-period factor when the
geometry permits it.

This is a deterministic combinatorial certificate for a DART-like defect
model.  It is not by itself an end-to-end repairability, wirelength, delay,
spare-placement, or novelty theorem.

## Geometric and physical-set model

For a base bump, an along-strip direction, and a cross-strip direction, define

```lean
def stripPoint
    (base along across : Nat × Nat) (r t : Nat) : Nat × Nat :=
  linePoint (linePoint base across r) along t
```

Here `r < W` selects one of the parallel lines and `t < L` selects a point on
that line.  The public physical strip is a `Finset (Nat × Nat)` formed by
taking the union of the images of all valid index pairs.  Consequently,
degenerate directions and intersecting samples do not count one physical bump
more than once.

Expose:

```lean
def stripLinePoints
    (L : Nat) (base along across : Nat × Nat) (r : Nat) :
    Finset (Nat × Nat)

def stripPoints
    (W L : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat)

def stripColorPoints
    (M K W L c : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat)
```

`stripColorPoints` filters the unique physical strip points by
`affineChainColor M K p.1 p.2 = c`.  An index-pair representation may be used
privately in proofs, but it is not the EDA-facing load definition.

## Period definitions

Reuse the existing along-line color period

```text
T = lineColorPeriod M K along
  = K / gcd(K, along.x + M * along.y).
```

Define the positive cross-line phase period, under `0 < K`, by

```lean
def stripAcrossColorPeriod
    (M K : Nat) (along across : Nat × Nat) : Nat :=
  let g := Nat.gcd K (lineColorStep M along)
  g / Nat.gcd g (lineColorStep M across)
```

and expose:

```lean
theorem stripAcrossColorPeriod_pos
    (M K : Nat) (along across : Nat × Nat) (hK : 0 < K) :
    0 < stripAcrossColorPeriod M K along across
```

Write `R = stripAcrossColorPeriod M K along across`.  A fixed color can occur
only on rows whose row indices agree modulo `R`.  This fact is independent of
the within-row sample indices.

## Public theorem surface

The first checkpoint is the compositional theorem:

```lean
theorem stripColor_load_le_sum_lines
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      W * ((L + lineColorPeriod M K along - 1) /
        lineColorPeriod M K along)
```

It must count unique physical points and may be proved by bounding every
parallel-line image by the corresponding `lineColorIndices` set, applying
`lineColor_load_le_ceilDiv_period`, and using finite-union cardinality
subadditivity.

The headline theorem is phase-aware:

```lean
theorem stripColor_load_le_phase_periods
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along)
```

The theorem does not require `c < K`: invalid colors simply select no physical
points when `0 < K`, and the upper bound remains valid.

Expose direct wrappers for the two axis-aligned geometries:

```lean
theorem stripColor_horizontal_load_le
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (1, 0) (0, 1)).card ≤
      W * ((L + K - 1) / K)

theorem stripColor_vertical_load_le_phase
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (0, 1) (1, 0)).card ≤
      ((W + Nat.gcd K M - 1) / Nat.gcd K M) *
        ((L + K / Nat.gcd K M - 1) / (K / Nat.gcd K M))
```

The vertical wrapper must retain the phase improvement

```text
ceil(W / gcd(K, M)) * ceil(L / (K / gcd(K, M))),
```

instead of silently weakening it to `W * ceil(L / (K / gcd(K, M)))`.

Also expose a finite-grid wrapper with the explicit geometric assumption:

```lean
theorem stripColor_finiteGrid_load_le_phase_periods
    (N M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (_hGrid : ∀ r < W, ∀ t < L,
      inGrid N (stripPoint base along across r t)) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along)
```

It reuses the same phase-aware bound.  It is a semantic wrapper, not a
different counting theorem.

## Proof architecture

The proof is split into focused layers:

1. Establish the physical-point/image membership lemmas and bound physical
   colored points by colored index pairs.
2. Reuse `lineColor_index_congruent` to show that equal-colored samples in one
   row have equal `t` residues modulo `T`.
3. Prove the cross-row analogue: equal-colored samples, possibly at different
   `t` indices, force equal row residues modulo `R`.  Reduce the affine-color
   congruence modulo `g = gcd(K, lineColorStep M along)`, eliminate the along
   multiples, and cancel the across color step modulo `g`.
4. Map a colored index pair `(r, t)` to `(r / R, t / T)`.  The two residue
   theorems plus quotient equality make this map injective on colored pairs.
5. Place the image inside
   `range (ceil(W/R)) × range (ceil(L/T))` and conclude the product bound.
6. Transfer the index-pair bound to the unique physical-point set.

Private quotient/range arithmetic helpers should remain local unless they are
reused outside this module.  Division and modulo obligations are isolated from
the geometric membership proof.

## Files and public-interface tests

Create:

- `CLRSLean/Research/ThreeDIC/StripDefectLoad.lean`
- `Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean`

Modify:

- `Tests/Research_ThreeDIC_Trust.lean`
- `docs/research/3d-ic-route-a-literature-audit-2026-08-29.md`
- `docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md`

The interface test freezes all public definitions and theorem names above.  It
also checks concrete horizontal, vertical, empty-strip, and repeated-point
examples with `by decide`.  The trust audit applies `#assert_axioms` to
`stripColor_load_le_phase_periods`.

## Verification and claim discipline

Development follows RED/GREEN interface testing.  Completion requires:

- the new module builds;
- all ThreeDIC interface and trust tests pass;
- no `sorry`, `admit`, or new `axiom` occurs on the changed proof surface;
- `git diff --check` and `scripts/check_repository.py` pass;
- an independent review finds no Critical or Important semantic issue.

Documentation must distinguish three levels:

1. the sum-of-lines theorem is a verified baseline, not the headline result;
2. the phase-aware theorem is a stronger direction-sensitive certificate, but
   is not claimed tight without a matching construction or lower bound;
3. neither theorem proves spare feasibility, mux reachability, routing delay,
   or successful physical repair.

If the phase-aware theorem is blocked, the sum-of-lines checkpoint may be
committed and reported as partial progress.  It must not be described as the
approved headline theorem, and the precise cross-row congruence blocker must
remain tracked in the research documentation.
