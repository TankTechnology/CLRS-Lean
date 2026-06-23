# Blocked And Deferred Items

This page records work that is not hidden but also not claimed as complete.

## Deferred Implementation

### Union-Find Correctness

- Related section: Section 23.2 - Kruskal and Prim
- Status: `deferred-implementation`
- Current decision: do not prove it in the first CLRS-lean phase.

The current MST proof uses `ComponentOracle` and `CycleTestImplementation` as
interfaces.  A future union-find implementation can refine this interface
without changing the mathematical Kruskal proof.

## Blocked Design

### Concrete MST Exchange Edge

- Related section: Section 23.1 - Growing a minimum spanning tree
- Status: `blocked-design`

The current theorem assumes a cut exchange certificate.  To remove that
assumption, we need a stable finite path or walk representation and a boundary
edge lemma for paths crossing a cut.

### Sorted-Order Lightness

- Related section: Section 23.2 - Kruskal and Prim
- Status: `partial`

Kruskal's textbook proof relies on processing edges in nondecreasing weight.
The Lean proof still needs a processed-prefix invariant showing that any lighter
crossing edge would already have been considered and rejected.
