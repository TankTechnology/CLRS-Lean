# Exchange Optimality Kernel Design

## Goal

Extract the common optimality argument behind Chapter 16 activity selection and
Chapter 23 minimum-spanning-tree exchange proofs.  The shared library should
own only the order-theoretic fact that a feasible solution remains optimal
after a no-worse exchange.  Activity tails, graph cuts, tree paths, and edge
replacement witnesses remain chapter-specific.

This pass is successful only if both chapters consume the shared kernel in
their existing proofs.  Adding an unused generic declaration or an adapter that
does not replace proof work is outside the goal.

## Current Evidence

Chapter 16 packages maximum-cardinality activity selection in
`MaxCardinality available selected`.  Its fields say that `selected` is a
feasible sublist of `available` and that every feasible competitor has length
at most `selected.length`.  The theorem
`greedy_choice_optimal_from_certificate` proves this final domination property
by exchanging each competitor into a greedy-headed target and composing two
length inequalities.

Chapter 23 packages a minimum spanning tree extending a prefix in
`IsMSTExtending P w A T`.  Its fields say that `T` is a feasible spanning tree,
contains `A`, and has weight at most every other feasible tree containing `A`.
The theorem `mst_exchange_preserves_prefix` proves that a feasible exchanged
tree remains optimal by composing its no-heavier inequality with the old MST's
optimality inequality.

These are two instances of the same kernel:

1. define feasibility for a solution;
2. define when one solution is no worse than another;
3. record a feasible solution that is no worse than every feasible competitor;
4. transport that optimality through one exchange or through a family of
   competitor-specific exchange witnesses.

The existing `ProofPatterns.ExchangeCertificate` records a total exchange
function.  Activity selection instead produces an existential tail whose type
depends on the current subproblem.  Converting it to a total function would add
classical choice without reducing proof work.  The new kernel therefore does
not change or force use of that structure.

## Alternatives Considered

### Adapt only Chapter 16 to `ExchangeCertificate`

This is a small edit, but it has only one consumer and requires selecting a
tail from an existential witness.  It does not capture Chapter 23's already
formalized optimality transport, so it fails the real-reuse criterion.

### Rewrite Kruskal around `BoundaryTrace`

Kruskal has a genuine processed-prefix geometry, but its hard obligations are
component exactness, cut lightness, forest preservation, and tree exchange.
Changing the induction carrier would not remove those domain proofs.  This is
deferred until a second trace has the same state/index interface.

### Shared optimality kernel

This is the selected design.  It has two concrete consumers, introduces no
choice, and allows all established chapter-facing structures and theorem types
to remain unchanged.

## Shared Public Interface

Extend `CLRSLean/ProofPatterns/Exchange.lean` with a proposition under
`CLRS.ProofPatterns`:

```lean
structure Optimal
    (feasible : Solution -> Prop)
    (noWorse : Solution -> Solution -> Prop)
    (chosen : Solution) : Prop where
  feasible_chosen : feasible chosen
  noWorse_than : forall other, feasible other -> noWorse chosen other
```

The public field names are `feasible_chosen` and `noWorse_than`; the red
interface pass fixes both names before implementation.

The kernel exposes two main theorems.

### Transport from an old optimum

Given:

- an old `Optimal feasible noWorse old` certificate;
- feasibility of `new`;
- `noWorse new old`; and
- transitivity of `noWorse`;

prove `Optimal feasible noWorse new`.  The public theorem name is
`ProofPatterns.Optimal.of_noWorse`.

This theorem owns the common proof that for every competitor `other`,
`new <= old <= other` in the problem's no-worse relation.  Chapter 23 will use
it after proving that an edge exchange is feasible and does not increase
weight.

### Optimality from competitor exchanges

Given:

- feasibility of `chosen`;
- for every feasible competitor `other`, an existential target `target` such
  that `target` has a caller-defined target property and is no worse than
  `other`;
- a proof that `chosen` is no worse than every such target; and
- transitivity of `noWorse`;

prove `Optimal feasible noWorse chosen`.  The public theorem name is
`ProofPatterns.optimal_of_exchange`.

The target predicate is intentionally caller-supplied.  For activity selection
it records that the exchanged list begins with the greedy activity and that its
tail is feasible for the filtered subproblem.  The common theorem never
mentions lists, activities, prefixes, or cardinality.

Both theorems take the transitivity hypothesis explicitly.  This avoids
requiring a global typeclass instance for a relation that is often defined
locally from a score or cost function.

The existing score relations remain the canonical simple instances:

- `ExchangeCertificate.NoLessScore score new old` means
  `score old <= score new`;
- `ExchangeCertificate.NoGreaterCost cost new old` means
  `cost new <= cost old`.

The implementation uses these established names in place; this pass adds no
score-relation aliases.

## Chapter 16 Bridge

Chapter 16 imports `CLRSLean.ProofPatterns.Exchange` and keeps these public
declarations unchanged:

- `MaxCardinality`;
- `GreedyChoiceCertificate`;
- `finishSorted_greedyChoiceCertificate`;
- `greedy_choice_optimal_from_certificate`;
- all executable greedy-selection correctness theorems.

Define `MaxCardinality.toOptimal` as the conversion from
`MaxCardinality available selected` to
`ProofPatterns.Optimal` with:

```lean
feasible := fun candidate =>
  candidate.Sublist available /\ ActivitySelection.Feasible candidate
noWorse := ExchangeCertificate.NoLessScore List.length
```

Define the converse conversion as `maxCardinality_of_optimal`.  These
conversions are representation bridges, not new textbook theorem groups.

Rewrite the proof body of `greedy_choice_optimal_from_certificate` so the final
optimality argument delegates to the shared competitor-exchange theorem.  Its
chapter-specific inputs remain:

- construction of `a :: selected` as a feasible sublist;
- extraction of `tail` from `GreedyChoiceCertificate.exchange`;
- the tail optimality bound supplied by `MaxCardinality after selected`.

The shared theorem performs only the final transitive composition.  The public
statement of `greedy_choice_optimal_from_certificate` must be byte-for-byte
type-compatible with its current interface.

## Chapter 23 Bridge

Chapter 23 Section 23.1 imports `CLRSLean.ProofPatterns.Exchange` and keeps
these public declarations unchanged:

- `IsMSTExtending`;
- `CutCertificate`;
- `mst_exchange_preserves_prefix`;
- `mst_exchange_step`;
- `safe_edge_of_lightest_crossing`;
- all downstream Kruskal and Prim results.

Define `IsMSTExtending.toOptimal` and `isMSTExtending_of_optimal` as the
conversions between `IsMSTExtending P w A T` and
`ProofPatterns.Optimal` with:

```lean
feasible := fun candidate =>
  P.IsSpanningTree candidate /\ A ⊆ candidate
noWorse := ExchangeCertificate.NoGreaterCost (weight w)
```

Rewrite `mst_exchange_preserves_prefix` so it:

1. obtains the exchanged tree's feasibility from `h_tree` and `h_extends`;
2. obtains the no-worse comparison from `weight_insert_erase_le`;
3. invokes the shared old-optimum transport theorem; and
4. converts the generic certificate back to `IsMSTExtending`.

Graph-specific exchange feasibility, `weight_insert_erase_le`, cut lightness,
and path/cycle certificates remain in Chapter 23.  Only the generic optimality
transport moves to `ProofPatterns`.

## Compatibility And Dependency Rules

- No existing public declaration is removed, renamed, or weakened.
- Chapter structures remain the reader-facing interfaces; consumers are not
  forced to mention `ProofPatterns.Optimal`.
- `ProofPatterns.Exchange` imports only Mathlib and never imports a chapter.
- Chapters 16 and 23 may import the proof-pattern module, so dependency flow is
  acyclic.
- No chapter-specific definition appears in the shared theorem signatures.
- The total-function `ExchangeCertificate` remains available with its existing
  fields and `exists_target_for` theorem.

## Theorem-Group Accounting

The generic optimality kernel is common infrastructure and is documented once
at its owner.  It does not add a textbook theorem group to the progress ledger.
The following likewise add no theorem groups:

- `MaxCardinality`/`Optimal` conversions;
- `IsMSTExtending`/`Optimal` conversions;
- compatibility aliases or namespace forwards;
- repeated applications of the two common transport theorems.

Chapter 16's greedy optimality and Chapter 23's MST cut/exchange results remain
distinct textbook obligations.  This pass changes their proof ownership, not
their progress count.  `docs/clrs-proof-progress.csv` is therefore unchanged.

## Test-First Implementation

The first code commit after the design adds failing checks to
`Tests/Common_Proof_Infrastructure.lean` for:

- `ProofPatterns.Optimal`;
- the old-optimum transport theorem;
- the competitor-exchange optimality theorem;
- one maximization example using list length;
- one minimization example using a natural-valued cost.

The focused test must fail because the new identifiers are absent before the
shared implementation is written.

Chapter compatibility is fixed by checks of the existing theorem types.  The
repository currently has no `Tests/Chapter_16_Interface.lean`, so the Chapter
16 source file itself and the common interface test provide the focused gate.
`Tests/Chapter_23_Interface.lean` remains the Chapter 23 gate.

After the shared kernel compiles, add the two chapter bridges and refactor one
chapter at a time.  Each refactor must rerun its focused Lean command before
the next chapter is changed.

## Documentation

Update:

- `docs/proof-patterns/common-proof-library-decision-matrix.md` to mark exchange
  optimality as an active geometric pattern with Chapters 16 and 23 as real
  consumers;
- `docs/proof-patterns/geometric-proof-patterns.md` to distinguish generic
  optimality transport from domain-specific witness construction;
- `docs/proof-patterns/greedy-exchange-certificates.md` to point Chapter 16's
  final optimality step at the shared kernel;
- `docs/repository-architecture.md` only if its active/deferred classification
  lists `Exchange` explicitly.

Documentation must state that `Boundary` remains deferred and that this pass
does not change theorem-group counts or chapter completion status.

## Verification Boundary

Required verification is:

1. the red failure of the common interface test for the intended missing names;
2. focused compilation of `ProofPatterns/Exchange.lean`;
3. compilation of the Chapter 16 activity-selection source;
4. compilation of Chapter 23 Section 23.1 and
   `Tests/Chapter_23_Interface.lean`;
5. the common proof-infrastructure interface test;
6. placeholder and axiom audits for the changed Lean files and headline shared
   theorems;
7. `git diff --check`;
8. `uv run python scripts/check_repository.py`;
9. a final `lake build CLRSLean`.

The website target is excluded because this is a proof-only change and no
navigation or generated-page structure changes.  No `literateHtml` build is
required.

## Acceptance Criteria

The pass is complete when:

1. the shared `Optimal` interface and both transport theorems compile without
   placeholders or project axioms;
2. Chapters 16 and 23 both import and invoke the shared optimality kernel in
   existing public proofs;
3. `greedy_choice_optimal_from_certificate` and
   `mst_exchange_preserves_prefix` keep their current public types;
4. the generic declarations contain no activity-, graph-, tree-, or edge-level
   vocabulary;
5. chapter-specific witness construction remains local;
6. the progress CSV and chapter status claims are unchanged;
7. focused and root verification pass; and
8. documentation identifies Exchange as active infrastructure with two real
   consumers.

## Delivery Shape

Keep the implementation reviewable as small commits:

1. design specification;
2. red common-interface checks;
3. shared optimality kernel;
4. Chapter 16 bridge and proof delegation;
5. Chapter 23 bridge and proof delegation;
6. documentation and verification cleanup.

Every code commit must pass its focused Lean boundary.  The branch is not
merged until the combined root verification succeeds.
