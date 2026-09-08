# Uniform Open-Addressing Probe Space Design

## Goal

Derive Chapter 11's existing without-replacement tail `probeTail m n i` from
the textbook uniform-hashing sample space: every permutation of `Fin m` is an
equally likely probe order.  The bridge must make the probability model a
theorem rather than an interpretation attached to a product definition.

## Fixed occupied set and event

For `occupied : Finset (Fin m)`, define the event

```lean
def firstProbesOccupied (occupied : Finset (Fin m)) (i : Nat)
    (sigma : Equiv.Perm (Fin m)) : Prop :=
  forall p : Fin i, (sigma (Fin.castLE ... p)) ∈ occupied
```

The precise embedding of `Fin i` into `Fin m` carries the hypothesis `i ≤ m`
in theorem statements, not in the event's mathematical meaning.  An equivalent
range-based predicate may be used if it substantially simplifies counting.

The uniform probability is the existing finite expectation of the event's
indicator.  `probeTail` remains unchanged.

## Module structure

- `UniformProbe/Definitions.lean`: sample type alias, occupied-prefix event,
  indicator probability, and an actual unsuccessful probe-count variable.
- `UniformProbe/Counting.lean`: event-cardinality recurrence/closed form.
- `UniformProbe/Probability.lean`: probability equals `probeTail` and
  expectation equals the existing tail sum.
- `UniformProbe.lean`: stable facade imported by Section 11.4 after the current
  analytic tail lemmas, avoiding a cyclic import.

If importing the current monolithic Section 11.4 from a child module creates a
cycle, first extract its analytic tail definitions/theorems into a small
`ProbeTail.lean` module and preserve all current public names through imports.

## Counting strategy

Count permutations incrementally.  For a prefix of length `i`, the first image
has `n` occupied choices, the next has `n-1`, and so on.  Every injective prefix
extends to exactly `(m-i)!` full permutations.  Thus the satisfying count is

```text
Nat.descFactorial n i * Nat.factorial (m - i)
```

for `i ≤ m` and `occupied.card = n`.  The total sample count is `m!`.  The
quotient simplifies to

```text
product j<i, (n-j)/(m-j),
```

which is exactly `probeTail m n i`.  The proof may use a recurrence on `i`
instead of a one-shot subtype equivalence, but it must expose either the exact
cardinality or the exact probability recurrence as a named theorem.

Reusable helpers belong in the new focused module unless their statement is
independent of hashing and immediately useful elsewhere.  Existing
`fintypeExpect`, `indicator`, `Fintype.card_perm`, and
`Nat.descFactorial_eq_prod_range` are reused.

## Actual probe-count variable

For a non-full table, define `uniformUnsuccessfulProbeCount occupied sigma` as
the number of occupied prefix slots before the first free slot, plus the final
free probe.  A bounded `Finset.range (m + 1)` count or `List.takeWhile` over the
permutation's ordered slot list is acceptable, provided the theorem

```lean
uniformUnsuccessfulProbeCount_gt_iff
```

identifies its tails with `firstProbesOccupied`.

Finite tail-sum linearity then proves:

```lean
theorem uniformUnsuccessfulExpectedProbes_eq
    (hcard : occupied.card = n) (hn : n < m) :
  fintypeExpect (fun sigma =>
    (uniformUnsuccessfulProbeCount occupied sigma : Real)) =
  expectedUnsuccessfulProbes m n
```

The existing upper bounds can then be re-exported with the left side as an
actual expectation over permutations.  Successful-search transport uses the
same insertion-time averaging model already documented by Theorem 11.8.

## Public theorem surface

The truth-source bridge is:

```lean
theorem uniformProbeTailProbability_eq_probeTail
    (occupied : Finset (Fin m)) (hcard : occupied.card = n)
    (hi : i ≤ m) :
  fintypeExpect (fun sigma : Equiv.Perm (Fin m) =>
    indicator (firstProbesOccupied occupied i sigma)) =
  probeTail m n i
```

Wrappers expose the explicit unsuccessful/insertion/successful bounds.  No
wrapper may assume the bridge equality as a hypothesis.

## Verification

The public signatures are first pinned as failing checks in a focused Chapter
11 interface test.  Counting, probability, and expectation modules are
elaborated separately.  The final batch adds native axiom checks and updates
the Chapter 11 guide's model-provenance statement.
