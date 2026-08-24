# Dry run: CLIQUE to VERTEX-COVER

## Closure ledger

| Layer | Current evidence | Status |
| --- | --- | --- |
| Source NP-completeness | `CLIQUE_npComplete` over honest serialized graph-plus-`k` instances | closed |
| Shared typed graph instance | `CliqueInstance`, normalized edge list, `WellFormed`, and symmetric adjacency | closed |
| Target typed semantics | No Chapter 34 at-most-`k` vertex-cover predicate on `CliqueInstance` | open |
| Typed complement reduction | No theorem relating a size-`k` clique in `G` to a cover of size at most `n-k` in the complement | open |
| Target raw language | No serialized `VERTEXCOVER` language; the existing graph-plus-`k` grammar can be reused with a target-facing symbol alias | open |
| Raw membership iff | No total complement map on raw strings | open |
| Serialized output size | Complement edge count and unary endpoint/parameter lengths are not yet lifted to a polynomial | open |
| Exact reduction machine | No fixed machine computes the raw complement map | open |
| Target NP membership | Chapter 35 has mathematical cover predicates, but no Chapter 34 raw certificate checker, certificate bound, or fixed checker machine | open |
| Target hardness/completeness | Can be transported from `CLIQUE_npComplete` after the concrete reduction and independent NP membership | open |

Current status: `semantic-only` has not yet been reached for the new target.

## First missing bridge

Define an at-most-`targetSize` vertex-cover predicate directly on the existing
`CliqueInstance`, define its normalized complement with target
`vertexCount - targetSize`, and prove the typed truth-source theorem:

```lean
I.WellFormed →
  I.HasClique ↔ (I.complementForVertexCover).HasVertexCover
```

The proof should expose the set-complement cardinality lemma and the edge/nonedge
incidence lemma separately.  This is the first dependency; a serializer or TM2
would currently target an unstable semantic map.

## File decomposition

```text
Section_34_5_NP_Complete_Problems/
└── VertexCover/
    ├── Instance.lean            -- cover predicate and semantic wrappers
    ├── Complement.lean          -- normalized complement construction
    ├── ComplementSemantics.lean -- soundness, completeness, typed iff
    ├── Language.lean            -- raw language over the graph-plus-k grammar
    ├── Certificate.lean         -- exact checker semantics and length
    ├── VerifierMachine.lean     -- fixed checker and runtime assembly
    ├── ReductionEncoding.lean   -- total raw map and output bound
    ├── ReductionMachine.lean    -- exact complement machine and runtime
    └── Completeness.lean        -- reduction, hardness, NP-completeness
```

Reuse `CliqueInstance` and the existing graph-plus-`k` grammar rather than
duplicating graph parsing.  Give the target alphabet a public graph/cover-facing
alias if needed; the separate language predicate makes its meaning
unambiguous.

## Narrow verification

Start with a failing interface check for the typed theorem, then verify only the
semantic slice:

```bash
lake env lean Tests/Chapter_34_VertexCover_Semantics.lean
```

Do not begin the concrete reduction machine until this test passes.
