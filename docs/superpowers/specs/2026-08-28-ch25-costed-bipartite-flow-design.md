# Chapter 25 costed bipartite-flow design

## Goal

Close the remaining textbook-level gap in CLRS Fourth Edition Section 25.1:
the augmenting-flow method for bipartite matching returns a maximum matching
within `O(VE)` work.

The result must not attach an unrelated arithmetic expression to an
existence theorem.  The returned flow, recovered matching, augmentation
count, and work counter must belong to one run.

## Reused proof surface

- Chapter 24's executable residual BFS and shortest augmenting path.
- Chapter 24's integral-flow preservation and unit-capacity matching
  extraction.
- Chapter 25's matching API and maximum-matching predicate.

No new maximum-flow or Berge proof is introduced.

## Selected cost model

The flow network is represented by adjacency lists over its support arcs.
For a bipartite graph `G`, the forward support contains

```
|G.L| + |G.E| + |G.R|
```

arcs.  A residual BFS scans each supported arc in at most two orientations
and each flow-network vertex once.  Updating a simple augmenting path scans
at most all flow-network vertices once.  Consequently one attempt is charged
an explicit linear budget bounded by four times the support-arc count plus a
constant.

This model is intentionally representation-specific: it claims adjacency-
list `O(E)`, not the cost of materializing neighborhoods by filtering every
vertex in an adjacency-matrix representation.

## Execution

1. Start from the zero flow of `toFlowNetwork V G`.
2. At each step, run residual BFS.
3. If an augmenting path exists, augment along the BFS shortest path;
   otherwise keep the flow unchanged.
4. Accumulate the per-attempt adjacency-list work budget and record whether
   the flow was augmented.
5. Run exactly `|G.L|` attempts.

The source cut has capacity exactly `|G.L|`.  Integral augmentation raises
the flow value by at least one.  If an earlier state has no augmenting path,
all later states are unchanged.  Hence an augmenting path after `|G.L|`
attempts would force the next flow value above the source cut, a
contradiction.

## Refinement and result

Every run state is integral.  Applying `matchingOfIntegralFlow` at each index
therefore yields a matching whose size is the flow value.  Active steps
strictly increase the recovered matching size.  The final no-augmenting-path
flow is maximal, and comparison with `matchingToFlow` proves that its
recovered matching is maximum.

The final exact work theorem has the shape

```
run.work ≤ |V| * (4 * (flowArcCount G + 1))
```

where `flowArcCount G = |G.L| + |G.E| + |G.R|`.  Since the partitions cover
`V`, this is the textbook `O(VE)` bound for the constructed flow network.

## Module boundaries

- `FlowExecution/Model.lean`: network sizes and the adjacency-list budget.
- `FlowExecution/Step.lean`: BFS step, integrality, and value progress.
- `FlowExecution/Run.lean`: the costed run and fixed-fuel maximality.
- `FlowExecution/Refinement.lean`: matching at every state and final theorem.
- `FlowExecution.lean`: public facade.

Each module receives a focused Lean build and interface check before the
section-level integration build.
